-- Prove2me | Definitions.Def_LogSupermodularBIS_Main_Weight
-- name    : LogSupermodularBIS_Main_Weight
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-11T04:30:55.911482+00:00
-- url     : https://prove2.me/theorems/efa3ddb9-9b6b-4104-b8f2-84a80cf07ce1
-- title:
--   Positive rational weights, log-supermodularity, residuals and normalized potentials
-- statement:
--   A configuration is $x\in\{0,1\}^d$, written as a map $\mathrm{Fin}\,d\to\mathrm{Bool}$; $x\wedge y$ and $x\vee y$ are the coordinatewise minimum and maximum. A weight $W:\{0,1\}^d\to\mathbb Q$ is **positive** if all values are positive, and **log-supermodular** if
--   $$W(x\wedge y)\,W(x\vee y)\ge W(x)\,W(y)\qquad(x,y\in\{0,1\}^d).\tag{1.1}$$
--   The **bit length** of a rational is the larger of the binary lengths of its reduced numerator and its denominator; $B$ bounds the value length if every value has bit length at most $B$. The partition function is $Z_W=\sum_xW(x)$ and the target law is $\mu_W=W/Z_W$.
--
--   A node of the self-reduction tree is a prefix $x_v\in\{0,1\}^j$, $0\le j\le d$, pinning the first $j$ coordinates. Its residual weight is $W_v(x')=W(x_v,x')$ on the $d-j$ free coordinates, its mass is $Z_v=\sum_{x'}W_v(x')$, and its residual law is $W_v/Z_v$. The normalized potential of the residual is
--   $$\Phi_v(x')=\log\frac{W_v(x')}{W_v(0)},\qquad Z_{\Phi_v}=\sum_{x'}e^{\Phi_v(x')}=Z_v/W_v(0).$$
--   For a real potential $\Phi$ on $\{0,1\}^k$, $Z_\Phi=\sum_xe^{\Phi(x)}$, $\mu=e^\Phi/Z_\Phi$, and $\Phi$ is **supermodular** if $\Phi(x\wedge y)+\Phi(x\vee y)\ge\Phi(x)+\Phi(y)$. The tree mass of a prefix $v$ for the weight $e^\Phi$ is the sum of $e^{\Phi(x)}$ over the configurations extending $v$, and the conditional marginal probability is $p_v=Z_{v1}/Z_v$ (2.1).
--
--   These are the objects of Theorem 1.2 and of the self-reduction in §2.1; all later statements use them.
-- source:
--   Jingcheng Liu, Yitong Yin, STOC 2027 submission #1385 (October 2026), p. 3 (PDF 4), (1.1) and the representation assumptions; pp. 9–10 (PDF 10–11), §2.1

import Mathlib

set_option autoImplicit false

namespace LogSupermodularBIS.Main

/-!
# Weights on the Boolean cube, residuals and normalized potentials (§1.1 p. 3, §2.1 pp. 9–10)

Configurations are `x : Fin d → Bool` (`true` = 1); `x ⊓ y`, `x ⊔ y` are the coordinatewise
minimum and maximum. A prefix (node of the self-reduction tree) is a list `v : List Bool` of
length `j ≤ d`, the coordinates `0, …, j-1` pinned in the fixed order. The free coordinates of
`v` are indexed by `Fin (d - v.length)`.
-/

/-- The bit length of a rational: the larger of the binary lengths of its (reduced) numerator
and its denominator. -/
def bitLength (q : ℚ) : ℕ := max (Nat.size q.num.natAbs) (Nat.size q.den)

/-- A positive weight. -/
def PositiveWeight {d : ℕ} (W : (Fin d → Bool) → ℚ) : Prop := ∀ x, 0 < W x

/-- Log-supermodularity (1.1): `W(x ∧ y) W(x ∨ y) ≥ W(x) W(y)`. -/
def LogSupermodular {d : ℕ} (W : (Fin d → Bool) → ℚ) : Prop :=
  ∀ x y : Fin d → Bool, W x * W y ≤ W (x ⊓ y) * W (x ⊔ y)

/-- Every value of `W` has bit length at most `B`. -/
def ValueLengthBound {d : ℕ} (W : (Fin d → Bool) → ℚ) (B : ℕ) : Prop :=
  ∀ x, bitLength (W x) ≤ B

/-- The partition function `Z_W = Σ_x W(x)`. -/
noncomputable def partitionFn {d : ℕ} (W : (Fin d → Bool) → ℚ) : ℝ := ∑ x, (W x : ℝ)

/-- The target law `μ_W = W / Z_W`. -/
noncomputable def gibbsLaw {d : ℕ} (W : (Fin d → Bool) → ℚ) (x : Fin d → Bool) : ℝ :=
  (W x : ℝ) / partitionFn W

/-- The all-zero configuration. -/
def zeroConfig (k : ℕ) : Fin k → Bool := fun _ => false

/-- The full configuration `(x_v, x')` obtained by pinning the prefix `v` and filling the free
coordinates with `x'`. -/
def extendPrefix {d : ℕ} (v : List Bool) (x' : Fin (d - v.length) → Bool) : Fin d → Bool :=
  fun i => if h : i.val < v.length then v[i.val] else
    x' ⟨i.val - v.length, by omega⟩

/-- The residual weight `W_v(x') = W(x_v, x')` on the free coordinates. -/
def residualWeight {d : ℕ} (W : (Fin d → Bool) → ℚ) (v : List Bool) :
    (Fin (d - v.length) → Bool) → ℚ :=
  fun x' => W (extendPrefix v x')

/-- The mass `Z_v` of the node `v`. -/
noncomputable def mass {d : ℕ} (W : (Fin d → Bool) → ℚ) (v : List Bool) : ℝ :=
  partitionFn (residualWeight W v)

/-- The residual law `W_v / Z_v` of the node `v`. -/
noncomputable def residualLaw {d : ℕ} (W : (Fin d → Bool) → ℚ) (v : List Bool) :
    (Fin (d - v.length) → Bool) → ℝ :=
  gibbsLaw (residualWeight W v)

/-- The normalized potential `Φ_v(x') = log(W_v(x') / W_v(0))` of the residual at `v`. -/
noncomputable def residualPotential {d : ℕ} (W : (Fin d → Bool) → ℚ) (v : List Bool) :
    (Fin (d - v.length) → Bool) → ℝ :=
  fun x' => Real.log ((residualWeight W v x' : ℝ) / (residualWeight W v (zeroConfig _) : ℝ))

/-- The partition function `Z_Φ = Σ_x e^{Φ(x)}` of a real potential. -/
noncomputable def potentialPartition {k : ℕ} (Φ : (Fin k → Bool) → ℝ) : ℝ :=
  ∑ x, Real.exp (Φ x)

/-- The strictly positive law `μ = e^Φ / Z_Φ`. -/
noncomputable def potentialLaw {k : ℕ} (Φ : (Fin k → Bool) → ℝ) (x : Fin k → Bool) : ℝ :=
  Real.exp (Φ x) / potentialPartition Φ

/-- Supermodularity `Φ(x ∧ y) + Φ(x ∨ y) ≥ Φ(x) + Φ(y)`. -/
def Supermodular {k : ℕ} (Φ : (Fin k → Bool) → ℝ) : Prop :=
  ∀ x y : Fin k → Bool, Φ x + Φ y ≤ Φ (x ⊓ y) + Φ (x ⊔ y)

/-- The prefix of length `j` of a configuration. -/
def prefixOf {k : ℕ} (x : Fin k → Bool) (j : ℕ) : List Bool := (List.ofFn x).take j

/-- The tree mass of the prefix `v` for the weight `e^Φ`: the sum of `e^{Φ(x)}` over the
configurations `x` extending `v`. -/
noncomputable def potentialMass {k : ℕ} (Φ : (Fin k → Bool) → ℝ) (v : List Bool) : ℝ :=
  ∑ x : Fin k → Bool, if prefixOf x v.length = v then Real.exp (Φ x) else 0

/-- The conditional marginal probability `p_v = Z_{v1} / Z_v` (2.1) of the weight `e^Φ` at the
prefix `v`. -/
noncomputable def condMarginal {k : ℕ} (Φ : (Fin k → Bool) → ℝ) (v : List Bool) : ℝ :=
  potentialMass Φ (v ++ [true]) / potentialMass Φ v

end LogSupermodularBIS.Main


