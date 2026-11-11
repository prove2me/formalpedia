-- Prove2me | Definitions.Def_FourierSparseTesting1656_Uniform_Basic
-- name    : FourierSparseTesting1656_Uniform_Basic
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-10T06:31:28.614489+00:00
-- url     : https://prove2.me/theorems/c0af0682-79d7-431c-b5a9-1a9a4159700f
-- title:
--   Fourier coefficients, Fourier sparsity, the class $F_s$, distance and restricted spectra on cosets of a subspace
-- statement:
--   Let $V=\mathbb F_2^n$ with characters $\chi_\alpha(x)=(-1)^{\langle\alpha,x\rangle}$. For a real-valued $u:V\to\mathbb R$, the Fourier coefficient is
--   $$\hat u(\alpha)=2^{-n}\sum_{x\in V}u(x)\chi_\alpha(x),$$
--   and the Fourier sparsity is $\operatorname{fs}(u)=|\{\alpha:\hat u(\alpha)\ne0\}|$. A Boolean function is a function $f:V\to\{-1,+1\}$; the class $F_s$ consists of all Boolean $f$ with $\operatorname{fs}(f)\le s$ (support cardinality, not Fourier degree or dimension). The distance between two real-valued functions is $\operatorname{dist}(u,v)=\Pr_x[u(x)\ne v(x)]$ for uniform $x$, and $L(s)=\log_2(2s)$.
--
--   For a subspace $H\le V$ with annihilator $H^\perp$, a complement $W$ means $V=W\oplus H^\perp$. For a real function $g$ on $H$ and $\gamma\in W$, its coefficient is $\hat g(\gamma)=\mathbb E_{h\in H}\,g(h)\chi_\gamma(h)$, and its sparsity is the number of $\gamma\in W$ with $\hat g(\gamma)\ne0$. The restricted spectrum of $u$ on the coset $a+H$ (with origin $a$) is
--   $$\hat u_{a+H}(\gamma)=\mathbb E_{h\in H}\,u(a+h)\chi_\gamma(h),\qquad\gamma\in W.$$
--
--   These are the objects of §2 shared by every statement of the mission.
--
--   **Formalization Note** Boolean functions are bit functions $V\to\mathrm{Bool}$ from the referenced Fourier-dimension model, with bit `false` meaning $+1$ and `true` meaning $-1$; characters, the $\pm1$ form and the annihilator are reused from that model.
-- source:
--   Arijit Ghosh, Manmatha Roy, STOC 2027 submission #1656 (October 2026), pp. 6–7, §2 (Fourier expansion, Fourier support and sparsity, F_k, dist, annihilator, complement W, restrictions and Eq. (2)); p. 16 (Fourier expansion on H over W); PDF SHA256 5374116f8d05176f80f62c5fdaaddae029e1f9e6af853c5a8e1873cb4e83a123

import Mathlib
import Definitions.Def_FourierDimTesting102_Quantum_Model

set_option autoImplicit false

namespace FourierSparseTesting1656.Uniform

open FourierDimTesting102.Quantum

open Classical in
/-- §2, p.6: the Fourier coefficient `û(α) = 2^{-n} ∑_x u(x) χ_α(x)` of a real-valued
`u : F₂ⁿ → ℝ`. -/
noncomputable def realCoeff {n : ℕ} (u : V n → ℝ) (α : V n) : ℝ :=
  ((2 : ℝ) ^ n)⁻¹ * ∑ x : V n, u x * chi α x

open Classical in
/-- §2, p.7: the Fourier sparsity `fs(u) = |supp(û)|` of a real-valued function. -/
noncomputable def realSparsity {n : ℕ} (u : V n → ℝ) : ℕ :=
  (Finset.univ.filter fun α : V n => realCoeff u α ≠ 0).card

/-- §2, p.7: the Fourier sparsity of a Boolean function, through its `{-1,+1}`-valued form. -/
noncomputable def boolSparsity {n : ℕ} (f : BoolFn n) : ℕ := realSparsity (toSign f)

/-- §2, p.7: `F_s`, all Boolean functions on `F₂ⁿ` with at most `s` nonzero Fourier
coefficients (support cardinality, not Fourier dimension). -/
def Fs (n s : ℕ) : Set (BoolFn n) := {g | boolSparsity g ≤ s}

open Classical in
/-- §2, p.6: `dist(u, v) = Pr_x[u(x) ≠ v(x)]` for real-valued functions, `x` uniform. -/
noncomputable def realDist {n : ℕ} (u v : V n → ℝ) : ℝ :=
  ((Finset.univ.filter fun x : V n => u x ≠ v x).card : ℝ) / 2 ^ n

/-- §2, p.6: `log₂(2s)`, the all-`s` reading of the paper's `log s` in the asymptotic bounds. -/
noncomputable def logTwoS (s : ℕ) : ℝ := Real.logb 2 (2 * (s : ℝ))

/-- §2, p.7: `W` is a complement of the annihilator `H^⊥`, `F₂ⁿ = W ⊕ H^⊥`. -/
def IsComplementOfPerp {n : ℕ} (H W : Submodule (ZMod 2) (V n)) : Prop :=
  IsCompl W (perp H)

open Classical in
/-- §4.1, p.16 and §2, p.7: the Fourier coefficient of a real function `g` on `H`, indexed by
`γ ∈ W`: `ĝ(γ) = E_{h ∈ H} g(h) χ_γ(h)` (uniform average over the points of `H`). -/
noncomputable def subCoeff {n : ℕ} (H W : Submodule (ZMod 2) (V n)) (g : H → ℝ) (γ : W) : ℝ :=
  (Fintype.card H : ℝ)⁻¹ * ∑ h : H, g h * chi (γ : V n) (h : V n)

open Classical in
/-- §4.1, p.16: the number of nonzero coefficients of a real function on `H` (indexed by `W`). -/
noncomputable def subSparsity {n : ℕ} (H W : Submodule (ZMod 2) (V n)) (g : H → ℝ) : ℕ :=
  (Finset.univ.filter fun γ : W => subCoeff H W g γ ≠ 0).card

/-- §2, p.7, Eq. (2): the restriction `u_{a+H}(h) = u(a+h)` and its coefficient
`û_{a+H}(γ) = E_{h ∈ H} u(a+h) χ_γ(h)`, `γ ∈ W`. The shift `a` records the origin. -/
noncomputable def restrCoeff {n : ℕ} (H W : Submodule (ZMod 2) (V n)) (u : V n → ℝ) (a : V n)
    (γ : W) : ℝ :=
  subCoeff H W (fun h => u (a + h)) γ

/-! ### Structural sanity facts -/

theorem realSparsity_const_one (n : ℕ) : realSparsity (fun _ : V n => (1 : ℝ)) ≤ 1 := by
  classical
  have h : (Finset.univ.filter fun α : V n => realCoeff (fun _ => (1 : ℝ)) α ≠ 0) ⊆ {0} := by
    intro α hα
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hα
    by_contra h0
    have h0' : α ≠ 0 := by simpa using h0
    apply hα
    simp [realCoeff, sum_chi_eq_zero h0']
  exact (Finset.card_le_card h).trans (by simp)

end FourierSparseTesting1656.Uniform


