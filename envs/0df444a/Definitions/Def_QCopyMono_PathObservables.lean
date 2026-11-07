-- Prove2me | Definitions.Def_QCopyMono_PathObservables
-- name    : QCopyMono_PathObservables
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T21:43:21.837408+00:00
-- url     : https://prove2.me/theorems/bb08a274-6ce3-42be-a5dd-37932fdcf710
-- title:
--   The path observables $Q_d$ and $H_d\otimes Z$, the weights $\kappa_d$ and $q_d(f)$
-- statement:
--   Fix a path length $t=t_d\ge1$. Let
--   $$
--   \mathcal P_d=\{(x,y)\in\mathcal B\times\mathcal B: x\preceq y,\ |y|-|x|=t_d\},\qquad
--   \kappa_d(x,y)=\tfrac12\Big(\tbinom{n-|x|}{t_d}^{-1}+\tbinom{|y|}{t_d}^{-1}\Big)\ \text{on }\mathcal P_d,\ 0\text{ otherwise}.
--   $$
--   With $|\xi_{xy}\rangle=\frac{|x\rangle-|y\rangle}{\sqrt2}\otimes|-\rangle$, the observable is $Q_d=\sum_{(x,y)\in\mathcal P_d}\kappa_d(x,y)\,|\xi_{xy}\rangle\langle\xi_{xy}|$. Further $h_d(x)=\sum_y\kappa_d(x,y)-\sum_y\kappa_d(y,x)$, $H_d=\sum_x h_d(x)|x\rangle\langle x|$, and $Z=|0\rangle\langle0|-|1\rangle\langle1|$ acts on the function-value qubit. Finally
--   $$
--   q_d(f)=\frac1{2^n}\sum_{x,y}\kappa_d(x,y)\,\mathbf 1[f(x)\neq f(y)].
--   $$
--   Both $Q_d$ and $H_d\otimes Z$ are Hermitian, which is proved with the definitions.
--
--   **Formalization Note** The objects depend on the band parameter $\varepsilon$ and on $t_d$ only through the integer $t$, which is an explicit argument. The binomials in $\kappa_d$ are positive on $\mathcal P_d$, so the inverses are genuine.
-- source:
--   Naik, Quantum Copy Complexity of Testing Monotonicity and Other Properties, STOC 2027 submission (manuscript sha256 10fb417512cedc538a3dc512c3cd893806335ae8e073ebaf1deeeab8e5dac528), §3.2.2, pp.14–15 (P_d, κ_d, q_d, ξ_xy, eq. (18), h_d, H_d, Z)

import Mathlib
import Definitions.Def_QAlgorithms_Defs_Basic
import Definitions.Def_QCopyMono_IsMonoTester
import Definitions.Def_QCopyMono_PathExperiment

namespace QCopyMono

open QAlgorithms Matrix

/-! # The path observables `Q_d` and `H_d ⊗ Z`

P. Naik, *Quantum Copy Complexity of Testing Monotonicity and Other Properties*, STOC 2027
submission (manuscript sha256 10fb4175…dac528), §3.2.2, pp.14–15.

**Formalization Note.** The path length `t_d` enters only through the integer `t`, so every
object takes `t` (and the band parameter `ε`) directly; the paper's `P_d, κ_d, q_d, Q_d, h_d, H_d`
are the objects below at `t = t_d`. Operators act on one copy, indexed by `X n = Qubits n × Bool`,
the `Bool` being the function-value qubit with `false = |0⟩`. `|−⟩ = (|0⟩ − |1⟩)/√2` and
`Z = |0⟩⟨0| − |1⟩⟨1|`. On `P_d` both binomials in `κ_d` are positive (`x` has at least `t` zero
coordinates and `y` at least `t` one coordinates, since `x ⪯ y` and `|y| − |x| = t`), so the
inverses are genuine. -/

/-- p.14: `(x, y) ∈ P_d = {(x, y) ∈ 𝓑 × 𝓑 : x ⪯ y, |y| − |x| = t_d}`, at `t_d = t`. -/
def PathPair {n : ℕ} (ε : ℝ) (t : ℕ) (x y : Qubits n) : Prop :=
  InBand ε x ∧ InBand ε y ∧ x ≤ y ∧ hammingWeight y = hammingWeight x + t

open Classical in
/-- p.14: `κ_d(x, y) = ½ (C(n − |x|, t_d)⁻¹ + C(|y|, t_d)⁻¹)` on `P_d`, and `0` otherwise. -/
noncomputable def kappa {n : ℕ} (ε : ℝ) (t : ℕ) (x y : Qubits n) : ℝ :=
  if PathPair ε t x y then
    ((((n - hammingWeight x).choose t : ℕ) : ℝ)⁻¹ + (((hammingWeight y).choose t : ℕ) : ℝ)⁻¹) / 2
  else 0

/-- The amplitudes of `|−⟩ = (|0⟩ − |1⟩)/√2` on the function-value qubit. -/
noncomputable def ketMinus (c : Bool) : ℂ :=
  if c then -(((Real.sqrt 2)⁻¹ : ℝ) : ℂ) else (((Real.sqrt 2)⁻¹ : ℝ) : ℂ)

/-- p.14: `|ξ_{xy}⟩ = (|x⟩ − |y⟩)/√2 ⊗ |−⟩`. -/
noncomputable def xi {n : ℕ} (x y : Qubits n) : X n → ℂ :=
  fun a => (((if a.1 = x then 1 else 0) - (if a.1 = y then 1 else 0)) /
    (((Real.sqrt 2 : ℝ)) : ℂ)) * ketMinus a.2

/-- p.14, eq. (18): `Q_d = ∑_{(x,y)∈P_d} κ_d(x, y) |ξ_{xy}⟩⟨ξ_{xy}|` (the sum may run over all
pairs since `κ_d` vanishes off `P_d`). -/
noncomputable def pathQ (n : ℕ) (ε : ℝ) (t : ℕ) : Matrix (X n) (X n) ℂ :=
  fun a b => ∑ x : Qubits n, ∑ y : Qubits n, ((kappa ε t x y : ℝ) : ℂ) * xi x y a * star (xi x y b)

/-- p.14: `h_d(x) = ∑_y κ_d(x, y) − ∑_y κ_d(y, x)`. -/
noncomputable def hFun {n : ℕ} (ε : ℝ) (t : ℕ) (x : Qubits n) : ℝ :=
  ∑ y : Qubits n, kappa ε t x y - ∑ y : Qubits n, kappa ε t y x

/-- pp.14–15: `H_d ⊗ Z` with `H_d = ∑ₓ h_d(x)|x⟩⟨x|` and `Z = |0⟩⟨0| − |1⟩⟨1|` on the
function-value qubit: the diagonal operator with entry `h_d(x)·(±1)` at `(x, c)`. -/
noncomputable def pathHZ (n : ℕ) (ε : ℝ) (t : ℕ) : Matrix (X n) (X n) ℂ :=
  Matrix.diagonal fun a => ((hFun ε t a.1 * (if a.2 then -1 else 1) : ℝ) : ℂ)

/-- p.14: `q_d(f) = 2^{−n} ∑_{x,y} κ_d(x, y) 1[f(x) ≠ f(y)]`. -/
noncomputable def qd {n : ℕ} (ε : ℝ) (t : ℕ) (f : Qubits n → Bool) : ℝ :=
  (∑ x : Qubits n, ∑ y : Qubits n, kappa ε t x y * (if f x ≠ f y then 1 else 0)) / 2 ^ n

/-- `Q_d` is Hermitian (an observable). -/
theorem pathQ_isHermitian (n : ℕ) (ε : ℝ) (t : ℕ) : (pathQ n ε t).IsHermitian := by
  ext a b
  simp only [conjTranspose_apply, pathQ, star_sum, star_mul', Complex.star_def,
    Complex.conj_ofReal, Complex.conj_conj]
  refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => ?_
  ring

/-- `H_d ⊗ Z` is Hermitian (an observable). -/
theorem pathHZ_isHermitian (n : ℕ) (ε : ℝ) (t : ℕ) : (pathHZ n ε t).IsHermitian := by
  ext a b
  by_cases h : a = b
  · subst h; simp [pathHZ, Complex.conj_ofReal]
  · simp [pathHZ, Matrix.diagonal_apply_ne _ h, Matrix.diagonal_apply_ne _ (Ne.symm h)]

end QCopyMono


