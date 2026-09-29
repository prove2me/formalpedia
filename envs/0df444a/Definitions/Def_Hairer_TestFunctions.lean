-- Prove2me | Definitions.Def_Hairer_TestFunctions
-- name    : Hairer_TestFunctions
-- status  : Definition
-- author  : @Lucas
-- created : 2026-09-12T20:35:30.992103+00:00
-- url     : https://prove2.me/theorems/6562f805-5b27-426b-aeda-15391b9f8e93
-- title:
--   Scalings, test functions, distributions and the spaces $\mathcal{C}^\alpha_s$
-- statement:
--   Analytic preliminaries for Hairer's theory of regularity structures.
--
--   A **scaling** of $\mathbb{R}^d$ is a tuple $s = (s_1,\dots,s_d)$ of integers $s_i \ge 1$; its
--   dimension is $|s| = \sum_i s_i$ and the associated quasi-norm is
--   $\|x\|_s = \max_i |x_i|^{1/s_i}$.
--
--   `testFunctions d` is the space $C^\infty_0(\mathbb{R}^d)$ of smooth compactly supported real
--   functions on $\mathbb{R}^d$ (points of $\mathbb{R}^d$ being represented as `Fin d → ℝ`), taken as a
--   submodule of all real-valued functions, and a **distribution** is a linear functional on it.
--   The pairing `Distrib.eval ξ φ` is $\langle \xi,\varphi\rangle$ for a test function $\varphi$
--   and is set to $0$ on functions that are not test functions.
--
--   For $\delta>0$ and $x \in \mathbb{R}^d$, the rescaled test function is
--   $$ (S^{\delta}_{s,x}\varphi)(y) = \delta^{-|s|}\,\varphi\!\left(\frac{y_1-x_1}{\delta^{s_1}},
--   \dots,\frac{y_d-x_d}{\delta^{s_d}}\right), $$
--   and the lemma `scaledTest_mem` records that rescaling maps test functions to test functions.
--
--   `IsTestBall s r η` is Hairer's class $\mathcal{B}^r_{s,0}$: $\eta$ is smooth with compact
--   support contained in $\{\|y\|_s \le 1\}$ and $\|\eta\|_{C^r} \le 1$, i.e. all iterated
--   derivatives of order at most $r$ are bounded by $1$. (Hairer allows all $C^r$ functions of
--   this kind; restricting to smooth ones defines the same spaces below.)
--
--   Finally, `MemCalpha s α ξ` is Definition 3.7: for $\alpha<0$, the distribution $\xi$ lies in
--   the Hölder-Besov space $\mathcal{C}^\alpha_s$ if for every compact $K$ there is a constant
--   $C$ with
--   $$ |\langle \xi, S^{\delta}_{s,x}\eta\rangle| \le C\,\delta^{\alpha} $$
--   for all $x \in K$, all $\delta \in (0,1]$ and all $\eta \in \mathcal{B}^r_{s,0}$ with
--   $r = -\lfloor \alpha \rfloor$.
-- source:
--   M. Hairer, A theory of regularity structures, Inventiones Mathematicae 198 (2014) 269-504, arXiv:1303.5113 (v4), Section 2.3 (scalings, rescaled test functions) and Definition 3.7 (p. 31)

import Mathlib

/-!
# Scalings, test functions, distributions and the spaces `C^α_s`

Analytic preliminaries of

  M. Hairer, *A theory of regularity structures*, Invent. Math. 198 (2014) 269–504,
  arXiv:1303.5113,

namely the scaled quasi-norm on `ℝ^d` (§2.3), the rescaled test functions
`S^δ_{s,x}`, the class `B^r_{s,0}` of test functions, and the Hölder–Besov spaces
`C^α_s` of negative regularity (Definition 3.7).
-/

set_option autoImplicit false

open scoped Classical

noncomputable section

namespace Hairer

/-- Points of `ℝ^d`. -/
abbrev Pt (d : ℕ) : Type := Fin d → ℝ

/-- A *scaling* of `ℝ^d` in the sense of Hairer §2.3: a `d`-tuple of integers `s i ≥ 1`. -/
def IsScaling {d : ℕ} (s : Fin d → ℕ) : Prop := ∀ i, 1 ≤ s i

/-- The effective dimension `|s| = ∑ᵢ sᵢ` of a scaling. -/
def scaleDim {d : ℕ} (s : Fin d → ℕ) : ℕ := ∑ i, s i

/-- The scaled quasi-norm `‖x‖_s = maxᵢ |xᵢ|^{1/sᵢ}` associated with a scaling `s`. -/
def snorm {d : ℕ} (s : Fin d → ℕ) (x : Pt d) : ℝ := ⨆ i, |x i| ^ ((1 : ℝ) / (s i : ℝ))

/-- The space `C^∞_0(ℝ^d)` of smooth, compactly supported test functions, as a
subspace of all real-valued functions on `ℝ^d`. -/
def testFunctions (d : ℕ) : Submodule ℝ (Pt d → ℝ) where
  carrier := {φ | ContDiff ℝ (⊤ : ℕ∞) φ ∧ HasCompactSupport φ}
  add_mem' := fun ⟨h1, h2⟩ ⟨g1, g2⟩ => ⟨h1.add g1, h2.add g2⟩
  zero_mem' := ⟨contDiff_const, by simpa using (HasCompactSupport.zero (α := Pt d) (β := ℝ))⟩
  smul_mem' := fun c _ ⟨h1, h2⟩ => ⟨h1.const_smul c, h2.smul_left⟩

/-- A distribution on `ℝ^d`: a linear functional on smooth compactly supported test
functions. -/
abbrev Distrib (d : ℕ) : Type := testFunctions d →ₗ[ℝ] ℝ

/-- The pairing `⟨ξ, φ⟩` of a distribution with a function, extended by `0` to
functions that are not test functions. -/
def Distrib.eval {d : ℕ} (ξ : Distrib d) (φ : Pt d → ℝ) : ℝ :=
  if h : φ ∈ testFunctions d then ξ ⟨φ, h⟩ else 0

/-- The rescaled test function
`(S^δ_{s,x} φ)(y) = δ^{-|s|} φ((y₁-x₁)/δ^{s₁}, …, (y_d-x_d)/δ^{s_d})`. -/
def scaledTest {d : ℕ} (s : Fin d → ℕ) (δ : ℝ) (x : Pt d) (φ : Pt d → ℝ) : Pt d → ℝ :=
  fun y => δ ^ (-(scaleDim s : ℝ)) * φ fun i => (y i - x i) / δ ^ (s i)

/-- The homeomorphism `y ↦ ((yᵢ - xᵢ)/δ^{sᵢ})ᵢ` of `ℝ^d` underlying `scaledTest`. -/
def scaleHomeo {d : ℕ} (s : Fin d → ℕ) {δ : ℝ} (hδ : δ ≠ 0) (x : Pt d) : Pt d ≃ₜ Pt d :=
  Homeomorph.piCongrRight fun i =>
    (Homeomorph.subRight (x i)).trans (Homeomorph.mulRight₀ (δ ^ (s i))⁻¹ (by simp [hδ]))

@[simp] theorem scaleHomeo_apply {d : ℕ} (s : Fin d → ℕ) {δ : ℝ} (hδ : δ ≠ 0) (x y : Pt d) :
    scaleHomeo s hδ x y = fun i => (y i - x i) / δ ^ (s i) := by
  funext i
  simp [scaleHomeo, Homeomorph.piCongrRight, Homeomorph.subRight, Homeomorph.mulRight₀,
    Equiv.mulRight₀, div_eq_mul_inv]

/-- Rescaling maps test functions to test functions. -/
theorem scaledTest_mem {d : ℕ} (s : Fin d → ℕ) {δ : ℝ} (hδ : 0 < δ) (x : Pt d)
    {φ : Pt d → ℝ} (hφ : φ ∈ testFunctions d) : scaledTest s δ x φ ∈ testFunctions d := by
  obtain ⟨hs, hc⟩ := hφ
  refine ⟨contDiff_const.mul (hs.comp (contDiff_pi.2 fun i =>
    ((contDiff_apply ℝ ℝ i).sub contDiff_const).div_const _)), ?_⟩
  have h2 : scaledTest s δ x φ =
      (fun _ : Pt d => δ ^ (-(scaleDim s : ℝ))) * (φ ∘ (scaleHomeo s hδ.ne' x)) := by
    funext y
    simp [scaledTest, Function.comp]
  rw [h2]
  exact (hc.comp_homeomorph _).mul_left

/-- The class `B^r_{s,0}` of test functions of Hairer §3.2: smooth functions supported in
the unit ball of the scaled distance `‖·‖_s`, all of whose derivatives up to order `r`
are bounded by `1` (that is, `‖η‖_{C^r} ≤ 1`).

Hairer tests against all `C^r` functions of this kind; restricting to smooth ones
defines the same spaces `C^α_s`. -/
structure IsTestBall {d : ℕ} (s : Fin d → ℕ) (r : ℕ) (η : Pt d → ℝ) : Prop where
  smooth : ContDiff ℝ (⊤ : ℕ∞) η
  compactSupport : HasCompactSupport η
  support : tsupport η ⊆ {y | snorm s y ≤ 1}
  derivBound : ∀ k ≤ r, ∀ y, ‖iteratedFDeriv ℝ k η y‖ ≤ 1

/-- The integer `r = -⌊α⌋` used in Hairer's Definition 3.7 to test distributions of
regularity `α < 0`. -/
def negReg (α : ℝ) : ℕ := (-⌊α⌋).toNat

/-- **Definition 3.7 (Hairer).** For `α < 0`, a distribution `ξ` belongs to `C^α_s` if,
for every compact set `K`, there is a constant `C` such that
`|⟨ξ, S^δ_{s,x} η⟩| ≤ C δ^α` uniformly over `x ∈ K`, `δ ∈ (0,1]` and `η ∈ B^r_{s,0}`,
where `r = -⌊α⌋`. -/
def MemCalpha {d : ℕ} (s : Fin d → ℕ) (α : ℝ) (ξ : Distrib d) : Prop :=
  ∀ K : Set (Pt d), IsCompact K → ∃ C : ℝ, ∀ x ∈ K, ∀ δ : ℝ, 0 < δ → δ ≤ 1 →
    ∀ η : Pt d → ℝ, IsTestBall s (negReg α) η →
      |ξ.eval (scaledTest s δ x η)| ≤ C * δ ^ α

end Hairer


