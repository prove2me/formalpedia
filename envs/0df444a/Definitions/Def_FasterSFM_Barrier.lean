-- Prove2me | Definitions.Def_FasterSFM_Barrier
-- name    : FasterSFM_Barrier
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T01:34:36.083888+00:00
-- url     : https://prove2.me/theorems/c4f57f24-8d71-44b1-bf8d-24f9a72df851
-- title:
--   The cutting-plane body, the volumetric–logarithmic barrier $\Psi_{\mathrm{fl}}$, certified centers and the potential $\Phi(S,P)$
-- statement:
--   The cutting-plane body is $P=\{x\in\mathbb R^n:\langle v_i,x\rangle\le\rho_i,\ 1\le i\le M\}$ (9). Its rows are the $2n$ cube rows $(\pm e_j,1)$ and $k$ inserted rows with $\|v_i\|_2\le1$ and $\rho_i\ge\delta$, so $M=2n+k$. For $x$ in the interior, eq. (11) and §5.3 define the slacks $s_i(x)=\rho_i-v_i^\top x$, the matrix $A_{\mathrm{fl}}(x)$ with rows $v_i^\top/s_i(x)$,
--
--   $$H_{\mathrm{fl}}(x)=\sum_i\frac{v_iv_i^\top}{s_i(x)^2},\qquad \Pi_{\mathrm{fl}}=A_{\mathrm{fl}}H_{\mathrm{fl}}^{-1}A_{\mathrm{fl}}^\top,\qquad \ell_i=(\Pi_{\mathrm{fl}})_{ii},$$
--
--   and the barrier
--
--   $$\Psi_{\mathrm{fl}}(x)=\tfrac12\log\det H_{\mathrm{fl}}(x)-\lambda\sum_i\log\frac{s_i(x)}{\rho_i}.$$
--
--   A subspace $S$ of dimension $N$ has an orthonormal basis $J\in\mathbb R^{n\times N}$; $\Psi_S(y)=\Psi_{\mathrm{fl}}(Jy)$ and $H_S(y)=J^\top H_{\mathrm{fl}}(Jy)J$. A point $z=Jy$ is a **certified center** (12) if all its slacks are positive and $\|\nabla\Psi_S(y)\|_{H_S(y)^{-1}}\le\tau$. The **potential** is $\Phi(S,P)=\min_{x\in P\cap S}\Psi_{\mathrm{fl}}(x)$ (13). A new cutting plane with unit normal $b$ at a center $z$ gets the slack $\upsilon=\sqrt{b^\top H_{\mathrm{fl}}(z)^{-1}b/\gamma}$ and offset $\rho=\upsilon+b^\top z$ (§5.4). The full Newton step is $y_+=y-\nabla^2f(y)^{-1}\nabla f(y)$ (§2.2).
--
--   **Formalization Note** Vectors are `Fin n → ℝ` with the dot product; Euclidean norms are written as square roots of sums of squares. Gradients and Hessians are the true derivatives (`fderiv`). $\Phi(S,P)$ is the infimum of $\Psi_{\mathrm{fl}}$ over the points of $S$ with all slacks positive: in the paper $\Psi_{\mathrm{fl}}=+\infty$ on the boundary, while Lean's $\log 0=0$ would give a junk finite value there. Matrix inverses use Lean's `Matrix.inv`, whose value at a singular matrix is junk; every use is at a positive definite matrix.
-- source:
--   Ene & Nguyen, A Faster Strongly Polynomial Time Algorithm for Submodular Function Minimization, arXiv:2610.25403v1, §5.1, eq. (9), p.17; §5.3, eqs. (11)–(13), pp.18–19; §5.4, p.21; §2.2, p.4

import Mathlib
import Definitions.Def_FasterSFM_Params

namespace FasterSFM

open Classical Matrix

/-!
# The cutting-plane body, the barrier, certified centers and the potential

Ene & Nguyen, arXiv:2610.25403v1, §5.1 (rows and the body (9), p.17), §5.3 (slacks, `H_fl`, `A_fl`,
`Π_fl`, leverage scores, the barrier (11), certified centers (12), the potential (13), pp.18–19),
§5.4 (`υ`, `ρ`, wide steps, p.21), and §2.2 (full Newton step and decrement, p.4).

**Formalization Note.**
* Vectors of `ℝⁿ` are `Fin n → ℝ` with the dot product `⬝ᵥ`; `ℓ₂` norms are written as square roots
  of sums of squares (Lean's `‖·‖` on `Fin n → ℝ` is the sup norm).
* A body consists of the `2n` cube rows `(±e_j, 1)`, always present, followed by `k` inserted rows
  `(v_i, ρ_i)`; rows are indexed by `(Fin n × Bool) ⊕ Fin k`, `M = 2n + k`.
* A subspace `S` of dimension `N` is given by a matrix `J ∈ ℝ^{n×N}` with orthonormal columns
  (`Jᵀ J = I`); points of `S` are `J y`.
* Gradients and Hessians are the true derivatives (`fderiv`), not the paper's closed-form formulas.
  `‖g‖_{H⁻¹} = (gᵀ H⁻¹ g)^{1/2}` uses `Matrix.inv` (junk value `0` for a singular `H`; every use is at
  a point where `H` is positive definite).
* The potential `Φ(S, P) = min_{P∩S} Ψ_fl` (13) is the infimum over the points of `S` with all slacks
  positive: `Ψ_fl` is `+∞` on the boundary in the paper, while Lean's `log 0 = 0` would give a junk
  finite value there. Lemma 9 asserts that this infimum is attained.
-/

/-- A cutting-plane body in `ℝⁿ`: the cube rows (implicit) and `k` inserted rows `⟨v_i, x⟩ ≤ ρ_i`
(§5.1, p.17). -/
structure Body (n : ℕ) where
  /-- number of inserted rows -/
  k : ℕ
  /-- inserted normal vectors -/
  v : Fin k → Fin n → ℝ
  /-- inserted offsets -/
  ρ : Fin k → ℝ

/-- Row indices: `(j, true)` is the cube row `(e_j, 1)`, `(j, false)` is `(−e_j, 1)`, `i : Fin k` an
inserted row. -/
abbrev Row (n k : ℕ) := (Fin n × Bool) ⊕ Fin k

namespace Body

variable {n : ℕ} (P : Body n)

/-- The normal vector `v_i` of row `i`. -/
noncomputable def rowV : Row n P.k → Fin n → ℝ
  | .inl (j, true) => Pi.single j 1
  | .inl (j, false) => -Pi.single j 1
  | .inr i => P.v i

/-- The offset `ρ_i` of row `i` (`1` for the cube rows). -/
noncomputable def rowρ : Row n P.k → ℝ
  | .inl _ => 1
  | .inr i => P.ρ i

/-- `M = 2n + k`, the number of rows. -/
def M : ℕ := 2 * n + P.k

/-- `W = n + λM` (Lemma 9, p.19). -/
noncomputable def W : ℝ := (n : ℝ) + lam * (P.M : ℝ)

/-- Admissible rows (§5.1, p.17): every inserted normal has `‖v_i‖₂ ≤ 1` and every inserted offset
is at least `δ`. -/
def Admissible : Prop :=
  ∀ i : Fin P.k, (∑ j, P.v i j ^ 2) ≤ 1 ∧ delta n ≤ P.ρ i

/-- The slack `s_i(x) = ρ_i − v_iᵀ x` (§5.3, p.18). -/
noncomputable def slack (i : Row n P.k) (x : Fin n → ℝ) : ℝ := P.rowρ i - P.rowV i ⬝ᵥ x

/-- `x ∈ P`: every slack is non-negative (9). -/
def Mem (x : Fin n → ℝ) : Prop := ∀ i, 0 ≤ P.slack i x

/-- `x ∈ int P`: every slack is positive. -/
def Interior (x : Fin n → ℝ) : Prop := ∀ i, 0 < P.slack i x

/-- `H_fl(x) = Σ_i v_i v_iᵀ / s_i(x)²` (§5.3, p.18). -/
noncomputable def Hfl (x : Fin n → ℝ) : Matrix (Fin n) (Fin n) ℝ :=
  ∑ i, (1 / P.slack i x ^ 2) • vecMulVec (P.rowV i) (P.rowV i)

/-- `A_fl(x)`, the matrix with rows `v_iᵀ / s_i(x)` (§5.3, p.18). -/
noncomputable def Afl (x : Fin n → ℝ) : Matrix (Row n P.k) (Fin n) ℝ :=
  fun i j => P.rowV i j / P.slack i x

/-- `Π_fl(x) = A_fl H_fl⁻¹ A_flᵀ` (§5.3, p.18). -/
noncomputable def Pifl (x : Fin n → ℝ) : Matrix (Row n P.k) (Row n P.k) ℝ :=
  P.Afl x * (P.Hfl x)⁻¹ * (P.Afl x)ᵀ

/-- The leverage score `ℓ_i(x) = Π_fl(x)_{ii}` (§5.3, p.18). -/
noncomputable def lev (x : Fin n → ℝ) (i : Row n P.k) : ℝ := P.Pifl x i i

/-- The barrier (11): `Ψ_fl(x) = ½ log det H_fl(x) − λ Σ_i log(s_i(x)/ρ_i)` (p.18). -/
noncomputable def Psi (x : Fin n → ℝ) : ℝ :=
  (1 / 2) * Real.log (P.Hfl x).det - lam * ∑ i, Real.log (P.slack i x / P.rowρ i)

/-- The body with the row `(b, ρ)` appended (§5.4, p.22: `P₊`). -/
noncomputable def insertRow (b : Fin n → ℝ) (ρ : ℝ) : Body n :=
  ⟨P.k + 1, Fin.snoc (α := fun _ => Fin n → ℝ) P.v b, Fin.snoc (α := fun _ => ℝ) P.ρ ρ⟩

end Body

/-- The partial derivatives `(∂_j f(y))_j` of `f : ℝ^N → ℝ` at `y` (the gradient). -/
noncomputable def grad {N : ℕ} (f : (Fin N → ℝ) → ℝ) (y : Fin N → ℝ) : Fin N → ℝ :=
  fun j => fderiv ℝ f y (Pi.single j 1)

/-- The Hessian matrix `(∂_i ∂_j f(y))_{ij}` of `f : ℝ^N → ℝ` at `y`. -/
noncomputable def hess {N : ℕ} (f : (Fin N → ℝ) → ℝ) (y : Fin N → ℝ) : Matrix (Fin N) (Fin N) ℝ :=
  fun i j => fderiv ℝ (fun y' => fderiv ℝ f y' (Pi.single j 1)) y (Pi.single i 1)

/-- The `k`-th derivative of `f` at `x` along direction `u`: `D^k f(x)[u, …, u]`, the `k`-th
derivative of `t ↦ f(x + t u)` at `t = 0`. -/
noncomputable def dirDeriv {N : ℕ} (k : ℕ) (f : (Fin N → ℝ) → ℝ) (x u : Fin N → ℝ) : ℝ :=
  iteratedDeriv k (fun t : ℝ => f (x + t • u)) 0

/-- `‖g‖²_{H⁻¹} = gᵀ H⁻¹ g`. -/
noncomputable def invNormSq {N : ℕ} (H : Matrix (Fin N) (Fin N) ℝ) (g : Fin N → ℝ) : ℝ :=
  g ⬝ᵥ (H⁻¹ *ᵥ g)

/-- The full Newton step `y₊ = y − ∇²f(y)⁻¹ ∇f(y)` (§2.2, p.4). -/
noncomputable def newtonStep {N : ℕ} (f : (Fin N → ℝ) → ℝ) (y : Fin N → ℝ) : Fin N → ℝ :=
  y - (hess f y)⁻¹ *ᵥ grad f y

/-- The subspace `S` spanned by the columns of `J`. -/
noncomputable def colSpace {n N : ℕ} (J : Matrix (Fin n) (Fin N) ℝ) : Submodule ℝ (Fin n → ℝ) :=
  LinearMap.range (Matrix.toLin' J)

namespace Body

variable {n : ℕ} (P : Body n)

/-- `Ψ_S(y) = Ψ_fl(J y)` (11), p.18. -/
noncomputable def PsiS {N : ℕ} (J : Matrix (Fin n) (Fin N) ℝ) (y : Fin N → ℝ) : ℝ := P.Psi (J *ᵥ y)

/-- `H_S(y) = Jᵀ H_fl(J y) J` (11), p.18. -/
noncomputable def HS {N : ℕ} (J : Matrix (Fin n) (Fin N) ℝ) (y : Fin N → ℝ) :
    Matrix (Fin N) (Fin N) ℝ :=
  Jᵀ * P.Hfl (J *ᵥ y) * J

/-- A certified center (12), p.19: `z = J y` has all slacks positive and
`‖∇Ψ_S(y)‖_{H_S(y)⁻¹} ≤ τ`. -/
def Certified {N : ℕ} (J : Matrix (Fin n) (Fin N) ℝ) (y : Fin N → ℝ) : Prop :=
  P.Interior (J *ᵥ y) ∧ Real.sqrt (invNormSq (P.HS J y) (grad (P.PsiS J) y)) ≤ tau

/-- The potential (13), p.19: `Φ(S, P) = min_{x ∈ P ∩ S} Ψ_fl(x)`, the infimum of `Ψ_fl` over the
points of the subspace `S` with all slacks positive. -/
noncomputable def Phi (S : Submodule ℝ (Fin n → ℝ)) : ℝ :=
  sInf (P.Psi '' {x | x ∈ S ∧ P.Interior x})

/-- The slack of the new row at a center, `υ = (bᵀ H_fl(z)⁻¹ b / γ)^{1/2}` (§5.4, p.21). -/
noncomputable def upsilon (z b : Fin n → ℝ) : ℝ := Real.sqrt (b ⬝ᵥ ((P.Hfl z)⁻¹ *ᵥ b) / gam)

end Body

end FasterSFM


