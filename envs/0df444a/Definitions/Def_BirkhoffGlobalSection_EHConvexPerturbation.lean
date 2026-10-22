-- Prove2me | Definitions.Def_BirkhoffGlobalSection_EHConvexPerturbation
-- name    : BirkhoffGlobalSection_EHConvexPerturbation
-- status  : Definition
-- author  : @Mazecto
-- created : 2026-10-02T13:18:37.841312+00:00
-- url     : https://prove2.me/theorems/cef5fe59-6113-4ff3-b9f0-9b282804f85a
-- title:
--   Perturbation framework and radial graphs for the local EH convexity leaves
-- statement:
--   Topology and calculus layer that reduces the three local subcritical EH leaves to estimates at $\mu=\tfrac12$, $c=c_0$.
--
--   - `tube_pos_of_compact` (tube lemma): a strict inequality on a closed condition over a compact set persists for nearby parameters. `exists_eps_eta_of_eventually` turns this into the $\varepsilon,\eta$ windows.
--   - `Ghat`, `fderiv_G_apply`, `hess_G_eq`: $G_{\mu,c}(s)$, $dG_{\mu,c}(s)v$ and $D^2G_{\mu,c}(s)[v,v]$ as jointly continuous functions of $(\mu,c,s,v)$.
--   - `box c₀` $=\{\cosh^2x_1\le2c_0,\ |x_2|\le\pi/2,\ |y_i|\le4c_0+4\}$. `G_pos_on_faces`: at $\mu=\tfrac12$, $c=c_0>2$, $G>0$ on its faces. `eventually_component_subset`: near $(1/2,c_0)$ the selected component stays inside the box.
--   - `no_two_zeros`: a continuous function whose derivative is positive at its zeros has at most one zero on an interval.
--   - `radial_graph_generic`: in a star-shaped compact box with $G(0)<0$, $G>0$ on the faces and $dG(s)s>0$ on the zero level, the component through a zero is a radial graph over $S^3$ with $G<0$ inside. The proof uses the IVT for existence, `no_two_zeros` for uniqueness, and the compact-to-Hausdorff homeomorphism onto $S^3$ to show the zero level in the box is connected.
--   - Generic facts: components of closed sets are closed, and $S^3$ is connected as the radial image of $\mathbb{R}^4\setminus\{0\}$.
-- source:
--   Constructed here (standard compactness, intermediate-value and connectedness arguments); parameter window as in Liu--Salomao, https://arxiv.org/html/2506.17867v2#S10.

import Definitions.Def_BirkhoffGlobalSection_EHSubcritical
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.Normed.Module.Connected
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Topology.Compactness.Compact
import Mathlib.Topology.Order.IntermediateValue

/-! Perturbation framework for the local subcritical EH convexity leaves.

* `EHConvex.tube_pos_of_compact`: tube lemma (strict inequality on a closed condition over a
  compact set persists for nearby parameters); `exists_eps_eta_of_eventually`.
* `EHConvex.Ghat`, `fderiv_G_apply`, `hess_G_eq`: the EH Hamiltonian, its derivative and its
  second derivative as jointly continuous functions of `(μ, c, s, v)`.
* `EHConvex.box c₀` (`cosh² x₁ ≤ 2c₀`, `|x₂| ≤ π/2`, `|yᵢ| ≤ 4c₀+4`) and its open core;
  `G_pos_on_faces`: at `μ = 1/2`, `c = c₀ > 2`, the Hamiltonian is positive on the faces.
* `component_subset_core`, `eventually_component_subset`: near `(1/2, c₀)` the selected
  component stays in the core of the box.
* `no_two_zeros`, `radial_graph_generic`: a level set inside a star-shaped compact box on which
  `dG(y)y > 0` is a radial graph over `S³` (existence by IVT, uniqueness, and connectedness via
  the compact-to-Hausdorff homeomorphism onto the sphere), with `G < 0` inside.
-/

namespace BirkhoffGlobalSection

namespace EHConvex

open Filter Topology Set

noncomputable section

/-- Tube lemma: a strict inequality on a closed condition over a compact set
persists for nearby parameters. -/
theorem tube_pos_of_compact {P E : Type*} [TopologicalSpace P] [TopologicalSpace E]
    {K : Set E} (hK : IsCompact K) {C : Set (P × E)} (hC : IsClosed C)
    {Φ : P × E → ℝ} (hΦ : Continuous Φ) {p₀ : P}
    (h0 : ∀ y ∈ K, (p₀, y) ∈ C → 0 < Φ (p₀, y)) :
    ∀ᶠ p in 𝓝 p₀, ∀ y ∈ K, (p, y) ∈ C → 0 < Φ (p, y) := by
  apply hK.eventually_forall_of_forall_eventually (P := fun p y => (p, y) ∈ C → 0 < Φ (p, y))
  intro y hy
  by_cases hm : (p₀, y) ∈ C
  · filter_upwards [hΦ.continuousAt.eventually (lt_mem_nhds (h0 y hy hm))] with z hz _
    exact hz
  · filter_upwards [hC.isOpen_compl.mem_nhds hm] with z hz hz'
    exact absurd hz' hz

/-- The EH Hamiltonian as a jointly smooth function of `(μ, c, s)`. -/
def Ghat (q : ℝ × ℝ × Phase) : ℝ := ehLeftHamiltonian q.1 q.2.1 q.2.2

theorem contDiff_Ghat {n : WithTop ℕ∞} : ContDiff ℝ n Ghat := by
  unfold Ghat ehLeftHamiltonian
  fun_prop

theorem continuous_Ghat : Continuous Ghat := contDiff_Ghat (n := 0).continuous

/-- Convert a neighbourhood of `(1/2, c₀)` into the `ε, η` windows of the leaves. -/
theorem exists_eps_eta_of_eventually {c₀ : ℝ} {Q : ℝ × ℝ → Prop}
    (h : ∀ᶠ p : ℝ × ℝ in 𝓝 ((1 : ℝ) / 2, c₀), Q p) :
    ∃ ε η : ℝ, 0 < ε ∧ 0 < η ∧ ∀ μ c : ℝ, |μ - 1 / 2| < ε → |c - c₀| < η → Q (μ, c) := by
  rw [Metric.eventually_nhds_iff] at h
  obtain ⟨δ, hδ, h⟩ := h
  refine ⟨δ, δ, hδ, hδ, fun μ c hμ hc => h (y := (μ, c)) ?_⟩
  rw [Prod.dist_eq]
  simp only [Real.dist_eq]
  exact max_lt hμ hc

/-- The comparison box at energy `c₀`. -/
def box (c₀ : ℝ) : Set Phase :=
  {s | Real.cosh (s 0) ^ 2 ≤ 2 * c₀ ∧ |s 1| ≤ Real.pi / 2 ∧
    |s 2| ≤ 4 * c₀ + 4 ∧ |s 3| ≤ 4 * c₀ + 4}

/-- Its open core. -/
def boxCore (c₀ : ℝ) : Set Phase :=
  {s | Real.cosh (s 0) ^ 2 < 2 * c₀ ∧ |s 1| < Real.pi / 2 ∧
    |s 2| < 4 * c₀ + 4 ∧ |s 3| < 4 * c₀ + 4}

theorem isClosed_box (c₀ : ℝ) : IsClosed (box c₀) := by
  simp only [box, Set.setOf_and]
  apply_rules [IsClosed.inter, isClosed_le] <;> fun_prop

theorem isOpen_boxCore (c₀ : ℝ) : IsOpen (boxCore c₀) := by
  simp only [boxCore, Set.setOf_and]
  apply_rules [IsOpen.inter, isOpen_lt] <;> fun_prop

theorem boxCore_subset_box (c₀ : ℝ) : boxCore c₀ ⊆ box c₀ := fun s hs =>
  ⟨hs.1.le, hs.2.1.le, hs.2.2.1.le, hs.2.2.2.le⟩

theorem abs_le_cosh (x : ℝ) : |x| ≤ Real.cosh x := by
  rw [← Real.cosh_abs]
  have h := Real.self_le_sinh_iff.mpr (abs_nonneg x)
  linarith [Real.sinh_lt_cosh |x|]

theorem isCompact_box (c₀ : ℝ) : IsCompact (box c₀) := by
  refine Metric.isCompact_of_isClosed_isBounded (isClosed_box c₀) ?_
  rw [Metric.isBounded_iff_subset_closedBall 0]
  refine ⟨2 * c₀ + 4 * c₀ + 6, fun s hs => ?_⟩
  obtain ⟨h0, h1, h2, h3⟩ := hs
  rw [Metric.mem_closedBall, dist_zero_right, pi_norm_le_iff_of_nonneg (by
    have := Real.one_le_cosh (s 0); nlinarith [abs_nonneg (s 2)])]
  have hc1 := Real.one_le_cosh (s 0)
  have hpi := Real.pi_le_four
  intro i
  rw [Real.norm_eq_abs]
  fin_cases i <;> simp
  · have := abs_le_cosh (s 0); nlinarith [abs_nonneg (s 2)]
  · nlinarith [abs_nonneg (s 2), Real.one_le_cosh (s 0)]
  · nlinarith [abs_nonneg (s 2), Real.one_le_cosh (s 0)]
  · nlinarith [abs_nonneg (s 2), Real.one_le_cosh (s 0)]

theorem sinh_two_sq (x : ℝ) :
    Real.sinh (2 * x) ^ 2 = 4 * Real.cosh x ^ 2 * (Real.cosh x ^ 2 - 1) := by
  rw [Real.sinh_two_mul]
  have := Real.cosh_sq x
  nlinarith [Real.cosh_sq x]

theorem sin_two_sq (x : ℝ) :
    Real.sin (2 * x) ^ 2 = 4 * Real.cos x ^ 2 * (1 - Real.cos x ^ 2) := by
  rw [Real.sin_two_mul]
  have := Real.sin_sq_add_cos_sq x
  nlinarith [Real.sin_sq_add_cos_sq x]

/-- The half-mass EH Hamiltonian in kinetic-plus-potential form. -/
theorem G_half (c : ℝ) (s : Phase) :
    ehLeftHamiltonian (1 / 2) c s =
      ((s 2 + Real.sin (2 * s 1) / 8) ^ 2 + (s 3 + Real.sinh (2 * s 0) / 8) ^ 2) / 2 +
        (c * (Real.cosh (s 0) ^ 2 - Real.cos (s 1) ^ 2) / 4 - Real.cosh (s 0) / 2 -
          Real.cosh (s 0) ^ 2 * (Real.cosh (s 0) ^ 2 - 1) / 32 -
          Real.cos (s 1) ^ 2 * (1 - Real.cos (s 1) ^ 2) / 32) := by
  unfold ehLeftHamiltonian
  simp only
  rw [sinh_two_sq, sin_two_sq]
  ring

/-- Lower bound of the potential over the box. -/
theorem potential_lower (c a b : ℝ) (hc : 2 < c) (ha : 1 ≤ a) (ha2 : a ^ 2 ≤ 2 * c)
    (hb0 : 0 ≤ b ^ 2) (hb1 : b ^ 2 ≤ 1) :
    -(4 * c ^ 2 + 2 * c + 1) ≤
      c * (a ^ 2 - b ^ 2) / 4 - a / 2 - a ^ 2 * (a ^ 2 - 1) / 32 -
        b ^ 2 * (1 - b ^ 2) / 32 := by
  have h1 : a ^ 2 * (a ^ 2 - 1) ≤ 2 * c * (2 * c) := by
    have : a ^ 2 - 1 ≤ 2 * c := by linarith
    calc a ^ 2 * (a ^ 2 - 1) ≤ (2 * c) * (2 * c) :=
          mul_le_mul ha2 this (by nlinarith) (by linarith)
      _ = 2 * c * (2 * c) := rfl
  have h2 : b ^ 2 * (1 - b ^ 2) ≤ 1 := by nlinarith
  have h3 : a ≤ 2 * c := by nlinarith
  nlinarith

theorem face_cosh (c a b k : ℝ) (hc : 2 < c) (ha : 1 ≤ a) (ha2 : a ^ 2 = 2 * c)
    (hb0 : 0 ≤ b ^ 2) (hb1 : b ^ 2 ≤ 1) (hk : 0 ≤ k) :
    0 < k + (c * (a ^ 2 - b ^ 2) / 4 - a / 2 - a ^ 2 * (a ^ 2 - 1) / 32 -
        b ^ 2 * (1 - b ^ 2) / 32) := by
  have hkey : a < 3 * c * (2 * c - 1) / 8 := by
    have h8 : 0 < 3 * c * (2 * c - 1) / 8 := by nlinarith
    rw [← abs_of_pos (by linarith : (0:ℝ) < a), ← abs_of_pos h8]
    apply sq_lt_sq.mp
    rw [ha2]
    nlinarith [mul_pos (by linarith : (0:ℝ) < c - 2) (by linarith : (0:ℝ) < c),
      mul_pos (mul_pos (by linarith : (0:ℝ) < c - 2) (by linarith : (0:ℝ) < c))
        (by linarith : (0:ℝ) < c)]
  have hb : b ^ 2 * (1 - b ^ 2) / 32 ≤ c * (1 - b ^ 2) / 4 := by
    have := mul_le_mul_of_nonneg_right (by linarith : b ^ 2 ≤ 8 * c) (by linarith : (0:ℝ) ≤ 1 - b ^ 2)
    linarith
  have : c * (a ^ 2 - b ^ 2) / 4 - a / 2 - a ^ 2 * (a ^ 2 - 1) / 32 - b ^ 2 * (1 - b ^ 2) / 32
      ≥ 3 * c * (2 * c - 1) / 16 - a / 2 := by
    rw [ha2]; nlinarith
  linarith

theorem face_pi (c a k : ℝ) (hc : 2 < c) (ha : 1 ≤ a) (ha2 : a ^ 2 ≤ 2 * c) (hk : 0 ≤ k) :
    0 < k + (c * (a ^ 2 - 0 ^ 2) / 4 - a / 2 - a ^ 2 * (a ^ 2 - 1) / 32 -
        0 ^ 2 * (1 - 0 ^ 2) / 32) := by
  obtain ⟨A, hA0, hA⟩ : ∃ A : ℝ, 0 ≤ A ∧ A ^ 2 = 2 * c :=
    ⟨Real.sqrt (2 * c), Real.sqrt_nonneg _, Real.sq_sqrt (by linarith)⟩
  have haA : a ≤ A := by nlinarith
  have hA2 : 2 ≤ A := by nlinarith
  have hgA : 0 < (c / 4 + 1 / 32) * A - A ^ 3 / 32 - 1 / 2 := by
    have : A ^ 3 = A * (2 * c) := by rw [← hA]; ring
    rw [this]; nlinarith
  have hkey : (A - 1) * ((c / 4 + 1 / 32) * a - a ^ 3 / 32 - 1 / 2) =
      (A - a) * (c / 4 - 1 / 2) +
        (a - 1) * ((c / 4 + 1 / 32) * A - A ^ 3 / 32 - 1 / 2) +
        (A - 1) * ((a - 1) * (A - a) * (a + 1 + A) / 32) := by ring
  have hpos : 0 < (A - 1) * ((c / 4 + 1 / 32) * a - a ^ 3 / 32 - 1 / 2) := by
    rw [hkey]
    have t3 : 0 ≤ (A - 1) * ((a - 1) * (A - a) * (a + 1 + A) / 32) :=
      mul_nonneg (by linarith) (div_nonneg (mul_nonneg (mul_nonneg (by linarith)
        (by linarith)) (by linarith)) (by norm_num))
    have t2 : 0 ≤ (a - 1) * ((c / 4 + 1 / 32) * A - A ^ 3 / 32 - 1 / 2) :=
      mul_nonneg (by linarith) hgA.le
    rcases eq_or_lt_of_le haA with h | h
    · rw [h] at t2 ⊢
      have : 0 < (A - 1) * ((c / 4 + 1 / 32) * A - A ^ 3 / 32 - 1 / 2) :=
        mul_pos (by linarith) hgA
      nlinarith
    · have t1 : 0 < (A - a) * (c / 4 - 1 / 2) := mul_pos (by linarith) (by linarith)
      linarith
  have hg : 0 < (c / 4 + 1 / 32) * a - a ^ 3 / 32 - 1 / 2 :=
    (pos_iff_pos_of_mul_pos hpos).mp (by linarith)
  have e : c * (a ^ 2 - 0 ^ 2) / 4 - a / 2 - a ^ 2 * (a ^ 2 - 1) / 32 - 0 ^ 2 * (1 - 0 ^ 2) / 32
      = a * ((c / 4 + 1 / 32) * a - a ^ 3 / 32 - 1 / 2) := by ring
  rw [e]
  have := mul_pos (by linarith : (0:ℝ) < a) hg
  linarith

theorem face_y (c P X Y : ℝ) (hc : 2 < c) (hP : -(4 * c ^ 2 + 2 * c + 1) ≤ P)
    (hX : 4 * c + 4 - c / 2 ≤ |X|) : 0 < (X ^ 2 + Y ^ 2) / 2 + P := by
  have h1 : (4 * c + 4 - c / 2) ^ 2 ≤ X ^ 2 := by
    rw [← sq_abs X]; exact pow_le_pow_left₀ (by linarith) hX 2
  nlinarith [sq_nonneg Y]

theorem abs_shift_ge (u v B : ℝ) (hv : |v| ≤ B) : |u| - B ≤ |u + v| := by
  have := abs_add_le (u + v) (-v)
  rw [abs_neg, add_neg_cancel_right] at this
  linarith

/-- Barrier: at `μ = 1/2`, `c = c₀ > 2`, the Hamiltonian is positive on the
faces of the box. -/
theorem G_pos_on_faces {c₀ : ℝ} (hc₀ : 2 < c₀) :
    ∀ s ∈ box c₀ ∩ (boxCore c₀)ᶜ, 0 < ehLeftHamiltonian (1 / 2) c₀ s := by
  rintro s ⟨⟨h0, h1, h2, h3⟩, hcore⟩
  rw [G_half]
  have ha : 1 ≤ Real.cosh (s 0) := Real.one_le_cosh _
  have hb1 : Real.cos (s 1) ^ 2 ≤ 1 := by
    rw [sq_le_one_iff_abs_le_one]; exact Real.abs_cos_le_one _
  have hb0 : 0 ≤ Real.cos (s 1) ^ 2 := sq_nonneg _
  have hpot := potential_lower c₀ _ _ hc₀ ha h0 hb0 hb1
  have hkin : 0 ≤ ((s 2 + Real.sin (2 * s 1) / 8) ^ 2 +
      (s 3 + Real.sinh (2 * s 0) / 8) ^ 2) / 2 := by positivity
  simp only [boxCore, Set.mem_compl_iff, Set.mem_ofPred_eq, not_and_or, not_lt] at hcore
  rcases hcore with hf | hf | hf | hf
  · exact face_cosh c₀ _ _ _ hc₀ ha (le_antisymm h0 hf) hb0 hb1 hkin
  · have hs1 : |s 1| = Real.pi / 2 := le_antisymm h1 hf
    have hb : Real.cos (s 1) = 0 := by
      rcases (abs_eq (by positivity)).mp hs1 with h | h <;> rw [h] <;> simp
    rw [hb]
    exact face_pi c₀ _ _ hc₀ ha h0 hkin
  · apply face_y c₀ _ _ _ hc₀ hpot
    have hsn : |Real.sin (2 * s 1) / 8| ≤ c₀ / 2 := by
      rw [abs_div, abs_of_pos (by norm_num : (0:ℝ) < 8)]
      have := Real.abs_sin_le_one (2 * s 1); linarith
    have := abs_shift_ge (s 2) _ _ hsn
    linarith [le_antisymm h2 hf]
  · rw [add_comm ((s 2 + _) ^ 2)]
    apply face_y c₀ _ _ _ hc₀ hpot
    have hsh : |Real.sinh (2 * s 0) / 8| ≤ c₀ / 2 := by
      rw [abs_div, abs_of_pos (by norm_num : (0:ℝ) < 8)]
      have hsq : Real.sinh (2 * s 0) ^ 2 ≤ (4 * c₀) ^ 2 := by
        rw [sinh_two_sq]
        have := mul_le_mul h0 (by linarith : Real.cosh (s 0) ^ 2 - 1 ≤ 2 * c₀) (by nlinarith)
          (by linarith)
        nlinarith
      have := sq_le_sq.mp hsq
      rw [abs_of_pos (by linarith : (0:ℝ) < 4 * c₀)] at this
      linarith
    have := abs_shift_ge (s 3) _ _ hsh
    linarith [le_antisymm h3 hf]

/-- Inclusion of the phase directions into parameter-phase space. -/
def L : Phase →L[ℝ] ℝ × ℝ × Phase :=
  (ContinuousLinearMap.inr ℝ ℝ (ℝ × Phase)).comp (ContinuousLinearMap.inr ℝ ℝ Phase)

@[simp] theorem L_apply (v : Phase) : L v = (0, 0, v) := rfl

theorem hasFDerivAt_iota (μ c : ℝ) (s : Phase) :
    HasFDerivAt (fun x : Phase => ((μ, c, x) : ℝ × ℝ × Phase)) L s := by
  have e : (fun x : Phase => ((μ, c, x) : ℝ × ℝ × Phase)) =
      fun x => L x + ((μ, c, 0) : ℝ × ℝ × Phase) := by
    funext x; simp
  rw [e]
  exact L.hasFDerivAt.add_const _

theorem fderiv_G_eq (μ c : ℝ) (x : Phase) :
    fderiv ℝ (ehLeftHamiltonian μ c) x = (fderiv ℝ Ghat (μ, c, x)).comp L := by
  have hd : DifferentiableAt ℝ Ghat (μ, c, x) :=
    (contDiff_Ghat (n := 1)).differentiable one_ne_zero _
  have := hd.hasFDerivAt.comp x (hasFDerivAt_iota μ c x)
  exact this.fderiv

theorem fderiv_G_apply (μ c : ℝ) (x v : Phase) :
    fderiv ℝ (ehLeftHamiltonian μ c) x v = fderiv ℝ Ghat (μ, c, x) (L v) := by
  rw [fderiv_G_eq]; rfl

theorem hess_G_eq (μ c : ℝ) (s v : Phase) :
    fderiv ℝ (fun x => fderiv ℝ (ehLeftHamiltonian μ c) x v) s v =
      fderiv ℝ (fderiv ℝ Ghat) (μ, c, s) (L v) (L v) := by
  have e : (fun x => fderiv ℝ (ehLeftHamiltonian μ c) x v) =
      (fun q => fderiv ℝ Ghat q (L v)) ∘ (fun x : Phase => ((μ, c, x) : ℝ × ℝ × Phase)) := by
    funext x; simp [fderiv_G_apply]
  rw [e]
  have h2 : ContDiff ℝ 2 Ghat := contDiff_Ghat
  have hd : DifferentiableAt ℝ (fderiv ℝ Ghat) (μ, c, s) :=
    ((h2.fderiv_right (m := 1) (by norm_num)).differentiable one_ne_zero) _
  have h1 : HasFDerivAt (fun q => fderiv ℝ Ghat q (L v))
      ((fderiv ℝ Ghat (μ, c, s)).comp (0 : (ℝ × ℝ × Phase) →L[ℝ] (ℝ × ℝ × Phase)) +
        (fderiv ℝ (fderiv ℝ Ghat) (μ, c, s)).flip (L v)) (μ, c, s) :=
    hd.hasFDerivAt.clm_apply (hasFDerivAt_const (L v) _)
  rw [(h1.comp s (hasFDerivAt_iota μ c s)).fderiv]
  simp

theorem continuous_fderiv_Ghat : Continuous (fderiv ℝ Ghat) :=
  (contDiff_Ghat (n := 1)).continuous_fderiv one_ne_zero

theorem continuous_fderiv2_Ghat : Continuous (fderiv ℝ (fderiv ℝ Ghat)) :=
  ((contDiff_Ghat (n := 2)).fderiv_right (m := 1) (by norm_num)).continuous_fderiv one_ne_zero

/-- The collision point lies on the zero level. -/
theorem G_collision (μ c : ℝ) (hμ : μ ≤ 1) :
    ehLeftHamiltonian μ c (ehLeftCollisionPoint μ) = 0 := by
  unfold ehLeftHamiltonian ehLeftCollisionPoint
  simp
  rw [mul_pow, Real.sq_sqrt (by norm_num), Real.sq_sqrt (by linarith)]
  ring

theorem collision_mem_boxCore {μ c₀ : ℝ} (hc₀ : 2 < c₀) (hμ : 0 < μ) :
    ehLeftCollisionPoint μ ∈ boxCore c₀ := by
  unfold boxCore ehLeftCollisionPoint
  refine ⟨?_, ?_, ?_, ?_⟩ <;> simp
  · linarith
  · positivity
  · linarith
  · have h1 : Real.sqrt (1 - μ) ≤ 1 := Real.sqrt_le_one.mpr (by linarith)
    have h2 : Real.sqrt 2 < 2 := by
      rw [Real.sqrt_lt' (by norm_num)]; norm_num
    have h3 : |Real.sqrt (1 - μ)| ≤ 1 := by
      rw [abs_of_nonneg (Real.sqrt_nonneg _)]; exact h1
    have h4 : |Real.sqrt 2| < 2 := by rw [abs_of_nonneg (Real.sqrt_nonneg _)]; exact h2
    nlinarith [abs_nonneg (Real.sqrt 2), abs_nonneg (Real.sqrt (1 - μ))]

/-- A component that misses the faces of the box and starts in its core stays
in the core. -/
theorem component_subset_core {μ c c₀ : ℝ} (hμ1 : μ ≤ 1)
    (hfaces : ∀ s ∈ box c₀ ∩ (boxCore c₀)ᶜ, 0 < ehLeftHamiltonian μ c s)
    (hcol : ehLeftCollisionPoint μ ∈ boxCore c₀) :
    ehLeftEnergyComponent μ c ⊆ boxCore c₀ := by
  have hpre := isPreconnected_connectedComponentIn (F := {s : Phase | ehLeftHamiltonian μ c s = 0})
    (x := ehLeftCollisionPoint μ)
  have hsub : ehLeftEnergyComponent μ c ⊆ boxCore c₀ ∪ (box c₀)ᶜ := by
    intro s hs
    have hz : ehLeftHamiltonian μ c s = 0 := by
      have h := connectedComponentIn_subset {s : Phase | ehLeftHamiltonian μ c s = 0}
        (ehLeftCollisionPoint μ)
      exact h hs
    by_contra hn
    simp only [Set.mem_union, Set.mem_compl_iff, not_or, not_not] at hn
    have := hfaces s ⟨hn.2, hn.1⟩
    linarith
  refine hpre.subset_left_of_subset_union (isOpen_boxCore c₀) (isClosed_box c₀).isOpen_compl
    ?_ hsub ?_
  · exact Set.disjoint_compl_right_iff_subset.mpr (boxCore_subset_box c₀)
  · exact ⟨_, mem_connectedComponentIn (G_collision μ c hμ1), hcol⟩

theorem eventually_neg_left {φ : ℝ → ℝ} {m d : ℝ} (h : HasDerivAt φ d m) (hd : 0 < d)
    (h0 : φ m = 0) : ∀ᶠ t in 𝓝[<] m, φ t < 0 := by
  have := (h.tendsto_slope.mono_left (nhdsLT_le_nhdsNE m)).eventually (lt_mem_nhds hd)
  filter_upwards [this, self_mem_nhdsWithin] with t ht htm
  rw [slope_def_field, h0, sub_zero] at ht
  have hneg : t - m < 0 := sub_neg.mpr htm
  rcases div_pos_iff.mp ht with h | h
  · exact absurd h.2 (not_lt.mpr hneg.le)
  · exact h.1

theorem eventually_pos_right {φ : ℝ → ℝ} {m d : ℝ} (h : HasDerivAt φ d m) (hd : 0 < d)
    (h0 : φ m = 0) : ∀ᶠ t in 𝓝[>] m, 0 < φ t := by
  have := (h.tendsto_slope.mono_left (nhdsGT_le_nhdsNE m)).eventually (lt_mem_nhds hd)
  filter_upwards [this, self_mem_nhdsWithin] with t ht htm
  rw [slope_def_field, h0, sub_zero] at ht
  have hpos : 0 < t - m := sub_pos.mpr htm
  rcases div_pos_iff.mp ht with h | h
  · exact h.1
  · exact absurd h.2 (not_lt.mpr hpos.le)

/-- A continuous function whose derivative is positive at each of its zeros in
`[a, b]` cannot vanish at both ends. -/
theorem no_two_zeros {φ : ℝ → ℝ} (hφ : Continuous φ) {a b : ℝ} (hab : a < b)
    (hder : ∀ t ∈ Icc a b, φ t = 0 → ∃ d, 0 < d ∧ HasDerivAt φ d t)
    (ha : φ a = 0) (hb : φ b = 0) : False := by
  obtain ⟨da, hda, hHa⟩ := hder a ⟨le_rfl, hab.le⟩ ha
  obtain ⟨db, hdb, hHb⟩ := hder b ⟨hab.le, le_rfl⟩ hb
  obtain ⟨u, hu, hu'⟩ :=
    ((eventually_pos_right hHa hda ha).and (Ioo_mem_nhdsGT hab)).exists
  obtain ⟨w, hw, hw'⟩ :=
    ((eventually_neg_left hHb hdb hb).and (Ioo_mem_nhdsLT hu'.2)).exists
  set S : Set ℝ := {t | t ∈ Icc u w ∧ φ t ≤ 0} with hS
  have hSc : IsClosed S := isClosed_Icc.inter (isClosed_le hφ continuous_const)
  have hSne : S.Nonempty := ⟨w, ⟨hw'.1.le, le_rfl⟩, hw.le⟩
  have hSbdd : BddBelow S := ⟨u, fun t ht => ht.1.1⟩
  set m := sInf S with hm
  have hmS : m ∈ S := hSc.csInf_mem hSne hSbdd
  have hum : u < m := by
    rcases eq_or_lt_of_le hmS.1.1 with h | h
    · rw [← h] at hmS; exact absurd hmS.2 (not_le.mpr hu)
    · exact h
  have hleft : ∀ᶠ t in 𝓝[<] m, φ t < 0 := by
    rcases eq_or_lt_of_le hmS.2 with h | h
    · obtain ⟨d, hd, hH⟩ := hder m ⟨(hu'.1.trans hum).le, hmS.1.2.trans hw'.2.le⟩ h
      exact eventually_neg_left hH hd h
    · exact nhdsWithin_le_nhds (hφ.continuousAt.eventually (gt_mem_nhds h))
  obtain ⟨t, ht, ht'⟩ := (hleft.and (Ioo_mem_nhdsLT hum)).exists
  have htS : t ∈ S := ⟨⟨ht'.1.le, ht'.2.le.trans hmS.1.2⟩, ht.le⟩
  exact absurd (csInf_le hSbdd htS) (not_le.mpr ht'.2)

/-- Squared Euclidean norm in the four phase coordinates. -/
def Q (s : Phase) : ℝ := zNormSq s + wNormSq s

theorem Q_smul (t : ℝ) (x : Phase) : Q (t • x) = t ^ 2 * Q x := by
  simp [Q, zNormSq, wNormSq]; ring

theorem Q_pos {s : Phase} (hs : s ≠ 0) : 0 < Q s := by
  unfold Q zNormSq wNormSq
  by_contra h
  apply hs
  funext i
  have h0 := sq_nonneg (s 0); have h1 := sq_nonneg (s 1)
  have h2 := sq_nonneg (s 2); have h3 := sq_nonneg (s 3)
  fin_cases i <;> simp <;> nlinarith

/-- Radial projection to the round sphere. -/
def normalize (s : Phase) : Phase := (Real.sqrt (Q s))⁻¹ • s

theorem Q_normalize {s : Phase} (hs : s ≠ 0) : Q (normalize s) = 1 := by
  unfold normalize
  rw [Q_smul, inv_pow, Real.sq_sqrt (Q_pos hs).le, inv_mul_cancel₀ (Q_pos hs).ne']

theorem normalize_mem {s : Phase} (hs : s ≠ 0) : normalize s ∈ unitThreeSphere :=
  Q_normalize hs

theorem ne_zero_of_mem_sphere {x : Phase} (hx : x ∈ unitThreeSphere) : x ≠ 0 := by
  rintro rfl; simp [unitThreeSphere, zNormSq, wNormSq] at hx

theorem normalize_smul {x : Phase} (hx : x ∈ unitThreeSphere) {r : ℝ} (hr : 0 < r) :
    normalize (r • x) = x := by
  unfold normalize
  have hQ : Q x = 1 := hx
  rw [Q_smul, hQ, mul_one, Real.sqrt_sq hr.le, smul_smul, inv_mul_cancel₀ hr.ne', one_smul]

theorem smul_normalize {s : Phase} (hs : s ≠ 0) : Real.sqrt (Q s) • normalize s = s := by
  unfold normalize
  rw [smul_smul, mul_inv_cancel₀ (Real.sqrt_pos.mpr (Q_pos hs)).ne', one_smul]

theorem continuousOn_normalize : ContinuousOn normalize {0}ᶜ := by
  have h1 : ContinuousOn (fun s : Phase => (Real.sqrt (Q s))⁻¹) {0}ᶜ := by
    refine ContinuousOn.inv₀ ?_ (fun s hs => (Real.sqrt_pos.mpr (Q_pos hs)).ne')
    unfold Q zNormSq wNormSq; fun_prop
  exact h1.smul continuousOn_id

theorem isConnected_unitThreeSphere : IsConnected unitThreeSphere := by
  have hc : IsConnected ({0}ᶜ : Set Phase) :=
    isConnected_compl_singleton_of_one_lt_rank (by rw [rank_fin_fun]; norm_num) 0
  have himg : normalize '' {0}ᶜ = unitThreeSphere := by
    ext x
    constructor
    · rintro ⟨s, hs, rfl⟩; exact normalize_mem hs
    · intro hx
      refine ⟨x, ne_zero_of_mem_sphere hx, ?_⟩
      have := normalize_smul hx one_pos
      rwa [one_smul] at this
  rw [← himg]
  exact hc.image _ continuousOn_normalize

section Generic

variable {G : Phase → ℝ} {B Bc : Set Phase}

theorem ray_hasDerivAt (hG : ContDiff ℝ 1 G) (x : Phase) (t : ℝ) :
    HasDerivAt (fun t : ℝ => G (t • x)) (fderiv ℝ G (t • x) x) t := by
  have hd : DifferentiableAt ℝ G (t • x) := (hG.differentiable one_ne_zero) _
  have := hd.hasFDerivAt.comp_hasDerivAt t ((hasDerivAt_id t).smul_const x)
  rw [one_smul] at this
  exact this

theorem ray_deriv_pos (hstar : ∀ s ∈ B, G s = 0 → 0 < fderiv ℝ G s s)
    {x : Phase} {t : ℝ} (ht : 0 < t) (hB : t • x ∈ B) (hz : G (t • x) = 0) :
    0 < fderiv ℝ G (t • x) x := by
  have h := hstar _ hB hz
  rw [map_smul, smul_eq_mul] at h
  exact pos_of_mul_pos_right h ht.le

theorem ray_unique (hG : ContDiff ℝ 1 G)
    (hstarB : ∀ s ∈ B, ∀ t : ℝ, 0 ≤ t → t ≤ 1 → t • s ∈ B)
    (hstar : ∀ s ∈ B, G s = 0 → 0 < fderiv ℝ G s s)
    {x : Phase} {r t : ℝ} (hr : 0 < r) (hrt : r < t) (htB : t • x ∈ B)
    (hrz : G (r • x) = 0) (htz : G (t • x) = 0) : False := by
  have ht : 0 < t := hr.trans hrt
  refine no_two_zeros (φ := fun u : ℝ => G (u • x))
    ((hG.continuous).comp (continuous_id.smul continuous_const)) hrt ?_ hrz htz
  intro u hu hz
  have hu0 : 0 < u := hr.trans_le hu.1
  have huB : u • x ∈ B := by
    have := hstarB _ htB (u / t) (div_nonneg hu0.le ht.le) ((div_le_one ht).mpr hu.2)
    rwa [smul_smul, div_mul_cancel₀ _ ht.ne'] at this
  exact ⟨_, ray_deriv_pos hstar hu0 huB hz, ray_hasDerivAt hG x u⟩

theorem ray_exists (hG : ContDiff ℝ 1 G) (hBc : IsCompact B) (hBco : IsOpen Bc)
    (hsub : Bc ⊆ B) (hstarB : ∀ s ∈ B, ∀ t : ℝ, 0 ≤ t → t ≤ 1 → t • s ∈ B)
    (h0 : G 0 < 0) (hfaces : ∀ s ∈ B ∩ Bcᶜ, 0 < G s) {p : Phase} (hpB : p ∈ B)
    {x : Phase} (hx : x ≠ 0) : ∃ r : ℝ, 0 < r ∧ r • x ∈ B ∧ G (r • x) = 0 := by
  have hcont : Continuous fun t : ℝ => t • x := continuous_id.smul continuous_const
  obtain ⟨M, hM⟩ := (Metric.isBounded_iff_subset_closedBall (0 : Phase)).mp hBc.isBounded
  have hnx : 0 < ‖x‖ := norm_pos_iff.mpr hx
  set t₁ : ℝ := (|M| + 1) / ‖x‖ with ht₁
  have ht₁pos : 0 < t₁ := div_pos (by positivity) hnx
  have ht₁B : t₁ • x ∉ B := by
    intro h
    have := hM h
    rw [Metric.mem_closedBall, dist_zero_right, norm_smul, Real.norm_eq_abs,
      abs_of_pos ht₁pos, ht₁, div_mul_cancel₀ _ hnx.ne'] at this
    linarith [le_abs_self M]
  have h0B : (0 : Phase) ∈ B := by
    have := hstarB p hpB 0 le_rfl zero_le_one; rwa [zero_smul] at this
  set S : Set ℝ := Icc 0 t₁ ∩ {t | t • x ∈ B} with hS
  have hSc : IsClosed S := isClosed_Icc.inter (hBc.isClosed.preimage hcont)
  have hSne : S.Nonempty := ⟨0, ⟨le_rfl, ht₁pos.le⟩, by simpa using h0B⟩
  have hSbdd : BddAbove S := ⟨t₁, fun t ht => ht.1.2⟩
  set T := sSup S with hT
  have hTS : T ∈ S := hSc.csSup_mem hSne hSbdd
  have hTt₁ : T < t₁ := by
    rcases eq_or_lt_of_le hTS.1.2 with h | h
    · rw [h] at hTS; exact absurd hTS.2 ht₁B
    · exact h
  have hTnc : T • x ∉ Bc := by
    intro h
    have hev : ∀ᶠ t in 𝓝 T, t • x ∈ Bc := hcont.continuousAt.preimage_mem_nhds (hBco.mem_nhds h)
    obtain ⟨t', ht', ht''⟩ := ((hev.filter_mono nhdsWithin_le_nhds).and (Ioo_mem_nhdsGT hTt₁)).exists
    have : t' ∈ S := ⟨⟨hTS.1.1.trans ht''.1.le, ht''.2.le⟩, hsub ht'⟩
    exact absurd (le_csSup hSbdd this) (not_le.mpr ht''.1)
  have hGT : 0 < G (T • x) := hfaces _ ⟨hTS.2, hTnc⟩
  have hφ0 : (fun t : ℝ => G (t • x)) 0 = G 0 := by simp
  have hT0 : 0 < T := by
    rcases eq_or_lt_of_le hTS.1.1 with h | h
    · rw [← h, zero_smul] at hGT; linarith
    · exact h
  obtain ⟨r, hr, hrz⟩ := intermediate_value_Ioo hT0.le
    ((hG.continuous.comp hcont).continuousOn) (show (0 : ℝ) ∈ Ioo _ _ by
      simp only [Function.comp_def, zero_smul]; exact ⟨h0, hGT⟩)
  refine ⟨r, hr.1, ?_, hrz⟩
  have := hstarB _ hTS.2 (r / T) (div_nonneg hr.1.le hT0.le) ((div_le_one hT0).mpr hr.2.le)
  rwa [smul_smul, div_mul_cancel₀ _ hT0.ne'] at this

theorem smul_mem_of_le (hstarB : ∀ s ∈ B, ∀ t : ℝ, 0 ≤ t → t ≤ 1 → t • s ∈ B)
    {x : Phase} {r R : ℝ} (hr : 0 ≤ r) (hrR : r ≤ R) (hR : 0 < R) (hRB : R • x ∈ B) :
    r • x ∈ B := by
  have := hstarB _ hRB (r / R) (div_nonneg hr hR.le) ((div_le_one hR).mpr hrR)
  rwa [smul_smul, div_mul_cancel₀ _ hR.ne'] at this

theorem zeroBox_isPreconnected (hG : ContDiff ℝ 1 G) (hBc : IsCompact B) (hBco : IsOpen Bc)
    (hsub : Bc ⊆ B) (hstarB : ∀ s ∈ B, ∀ t : ℝ, 0 ≤ t → t ≤ 1 → t • s ∈ B)
    (h0 : G 0 < 0) (hfaces : ∀ s ∈ B ∩ Bcᶜ, 0 < G s)
    (hstar : ∀ s ∈ B, G s = 0 → 0 < fderiv ℝ G s s) {p : Phase} (hpB : p ∈ B) :
    IsPreconnected ({s | G s = 0} ∩ B) := by
  set Z := {s | G s = 0} ∩ B with hZ
  have hZc : IsCompact Z := hBc.inter_left (isClosed_eq hG.continuous continuous_const)
  have hne : ∀ s ∈ Z, s ≠ 0 := by
    rintro s hs rfl
    have := hs.1
    simp only [mem_setOf_eq] at this
    linarith
  haveI : CompactSpace Z := isCompact_iff_compactSpace.mp hZc
  let f : Z → unitThreeSphere := fun s => ⟨normalize s, normalize_mem (hne s s.2)⟩
  have hf : Continuous f :=
    Continuous.subtype_mk ((continuousOn_normalize.mono (fun s hs => hne s hs)).restrict) _
  have hinj : Function.Injective f := by
    intro s s' h
    have h' : normalize (s : Phase) = normalize (s' : Phase) := congrArg Subtype.val h
    have hs0 := hne s s.2
    have hs0' := hne s' s'.2
    set x := normalize (s : Phase)
    have e1 : Real.sqrt (Q s) • x = s := smul_normalize hs0
    have e2 : Real.sqrt (Q s') • x = s' := by rw [h']; exact smul_normalize hs0'
    have p1 : 0 < Real.sqrt (Q s) := Real.sqrt_pos.mpr (Q_pos hs0)
    have p2 : 0 < Real.sqrt (Q s') := Real.sqrt_pos.mpr (Q_pos hs0')
    have z1 : G (Real.sqrt (Q s) • x) = 0 := by rw [e1]; exact s.2.1
    have z2 : G (Real.sqrt (Q s') • x) = 0 := by rw [e2]; exact s'.2.1
    have b1 : Real.sqrt (Q s) • x ∈ B := by rw [e1]; exact s.2.2
    have b2 : Real.sqrt (Q s') • x ∈ B := by rw [e2]; exact s'.2.2
    rcases lt_trichotomy (Real.sqrt (Q s)) (Real.sqrt (Q s')) with hl | he | hl
    · exact (ray_unique hG hstarB hstar p1 hl b2 z1 z2).elim
    · apply Subtype.ext; rw [← e1, ← e2, he]
    · exact (ray_unique hG hstarB hstar p2 hl b1 z2 z1).elim
  have hsurj : Function.Surjective f := by
    rintro ⟨x, hx⟩
    obtain ⟨r, hr, hrB, hrz⟩ :=
      ray_exists hG hBc hBco hsub hstarB h0 hfaces hpB (ne_zero_of_mem_sphere hx)
    exact ⟨⟨r • x, hrz, hrB⟩, Subtype.ext (normalize_smul hx hr)⟩
  let e := (show Continuous (Equiv.ofBijective f ⟨hinj, hsurj⟩) from hf).homeoOfEquivCompactToT2
  haveI : ConnectedSpace unitThreeSphere :=
    isConnected_iff_connectedSpace.mp isConnected_unitThreeSphere
  haveI : ConnectedSpace Z := e.symm.surjective.connectedSpace e.symm.continuous
  exact isPreconnected_iff_preconnectedSpace.mpr inferInstance

/-- The radial-graph conclusions for a component trapped in a star-shaped box. -/
theorem radial_graph_generic (hG : ContDiff ℝ 1 G) (hBc : IsCompact B) (hBco : IsOpen Bc)
    (hsub : Bc ⊆ B) (hstarB : ∀ s ∈ B, ∀ t : ℝ, 0 ≤ t → t ≤ 1 → t • s ∈ B)
    (h0 : G 0 < 0) (hfaces : ∀ s ∈ B ∩ Bcᶜ, 0 < G s)
    (hstar : ∀ s ∈ B, G s = 0 → 0 < fderiv ℝ G s s) {p : Phase} (hp : G p = 0)
    (hpB : p ∈ B) (hcompB : connectedComponentIn {s | G s = 0} p ⊆ B) :
    (∀ x ∈ unitThreeSphere, ∃ r : ℝ, 0 < r ∧
        r • x ∈ connectedComponentIn {s | G s = 0} p) ∧
      (∀ x ∈ unitThreeSphere, ∀ r t : ℝ, 0 < r → 0 < t →
        r • x ∈ connectedComponentIn {s | G s = 0} p →
        t • x ∈ connectedComponentIn {s | G s = 0} p → r = t) ∧
      (∀ x ∈ unitThreeSphere, ∀ R : ℝ, 0 < R →
        R • x ∈ connectedComponentIn {s | G s = 0} p →
        ∀ r : ℝ, 0 ≤ r → r < R → G (r • x) < 0) := by
  have hZsub : {s | G s = 0} ∩ B ⊆ connectedComponentIn {s | G s = 0} p :=
    (zeroBox_isPreconnected hG hBc hBco hsub hstarB h0 hfaces hstar hpB).subset_connectedComponentIn
      ⟨hp, hpB⟩ inter_subset_left
  have hsubZ : ∀ s, s ∈ connectedComponentIn {s | G s = 0} p → G s = 0 ∧ s ∈ B := by
    intro s hs
    have h := connectedComponentIn_subset {s : Phase | G s = 0} p
    exact ⟨h hs, hcompB hs⟩
  refine ⟨fun x hx => ?_, fun x _ r t hr ht hrc htc => ?_, fun x _ R hR hRc r hr hrR => ?_⟩
  · obtain ⟨r, hr, hrB, hrz⟩ :=
      ray_exists hG hBc hBco hsub hstarB h0 hfaces hpB (ne_zero_of_mem_sphere hx)
    exact ⟨r, hr, hZsub ⟨hrz, hrB⟩⟩
  · obtain ⟨hrz, hrB⟩ := hsubZ _ hrc
    obtain ⟨htz, htB⟩ := hsubZ _ htc
    rcases lt_trichotomy r t with h | h | h
    · exact (ray_unique hG hstarB hstar hr h htB hrz htz).elim
    · exact h
    · exact (ray_unique hG hstarB hstar ht h hrB htz hrz).elim
  · obtain ⟨hRz, hRB⟩ := hsubZ _ hRc
    rcases eq_or_lt_of_le hr with h | h
    · rw [← h, zero_smul]; exact h0
    by_contra hneg
    push_neg at hneg
    rcases eq_or_lt_of_le hneg with hz | hpos
    · exact ray_unique hG hstarB hstar h hrR hRB hz.symm hRz
    · have hcont : Continuous fun t : ℝ => G (t • x) :=
        hG.continuous.comp (continuous_id.smul continuous_const)
      obtain ⟨r', hr', hr'z⟩ := intermediate_value_Ioo hr hcont.continuousOn
        (show (0 : ℝ) ∈ Ioo _ _ by simp only [zero_smul]; exact ⟨h0, hpos⟩)
      exact ray_unique hG hstarB hstar hr'.1 (hr'.2.trans hrR) hRB hr'z hRz

end Generic

theorem isClosed_connectedComponentIn_of_isClosed {F : Set Phase} (hF : IsClosed F)
    (x : Phase) : IsClosed (connectedComponentIn F x) := by
  by_cases hx : x ∈ F
  · have hsub : closure (connectedComponentIn F x) ⊆ connectedComponentIn F x := by
      apply (isPreconnected_connectedComponentIn.closure).subset_connectedComponentIn
      · exact subset_closure (mem_connectedComponentIn hx)
      · exact closure_minimal (connectedComponentIn_subset F x) hF
    exact closure_subset_iff_isClosed.mp hsub
  · rw [connectedComponentIn_eq_empty hx]; exact isClosed_empty

theorem isClosed_ehLeftEnergyComponent (μ c : ℝ) : IsClosed (ehLeftEnergyComponent μ c) :=
  isClosed_connectedComponentIn_of_isClosed
    (isClosed_eq (EHConvex.contDiff_Ghat (n := 0) |>.continuous.comp
      (by fun_prop : Continuous fun s : Phase => ((μ, c, s) : ℝ × ℝ × Phase)))
      continuous_const) _

theorem G_zero_of_mem_component {μ c : ℝ} {s : Phase} (hs : s ∈ ehLeftEnergyComponent μ c) :
    ehLeftHamiltonian μ c s = 0 := by
  have h := connectedComponentIn_subset {s : Phase | ehLeftHamiltonian μ c s = 0}
    (ehLeftCollisionPoint μ)
  exact h hs

theorem eventually_faces {c₀ : ℝ} (hc₀ : 2 < c₀) :
    ∀ᶠ p : ℝ × ℝ in 𝓝 ((1 : ℝ) / 2, c₀),
      ∀ s ∈ box c₀ ∩ (boxCore c₀)ᶜ, 0 < ehLeftHamiltonian p.1 p.2 s := by
  have h := tube_pos_of_compact (P := ℝ × ℝ) (E := Phase)
    ((isCompact_box c₀).inter_right (isOpen_boxCore c₀).isClosed_compl)
    (C := Set.univ) isClosed_univ
    (Φ := fun q => Ghat (q.1.1, q.1.2, q.2)) (continuous_Ghat.comp (by fun_prop))
    (p₀ := ((1 : ℝ) / 2, c₀)) (fun s hs _ => G_pos_on_faces hc₀ s hs)
  filter_upwards [h] with p hp s hs using hp s hs trivial

theorem eventually_component_subset {c₀ : ℝ} (hc₀ : 2 < c₀) :
    ∀ᶠ p : ℝ × ℝ in 𝓝 ((1 : ℝ) / 2, c₀), 0 < p.1 → p.1 < 1 →
      ehLeftEnergyComponent p.1 p.2 ⊆ boxCore c₀ := by
  filter_upwards [eventually_faces hc₀] with p hp h0 h1
  exact component_subset_core h1.le hp (collision_mem_boxCore hc₀ h0)

theorem box_smul {c₀ : ℝ} : ∀ s ∈ box c₀, ∀ t : ℝ, 0 ≤ t → t ≤ 1 → t • s ∈ box c₀ := by
  rintro s ⟨h0, h1, h2, h3⟩ t ht0 ht1
  have key : ∀ i, |(t • s) i| ≤ |s i| := by
    intro i
    rw [Pi.smul_apply, smul_eq_mul, abs_mul, abs_of_nonneg ht0]
    exact mul_le_of_le_one_left (abs_nonneg _) ht1
  refine ⟨?_, (key 1).trans h1, (key 2).trans h2, (key 3).trans h3⟩
  have hc : Real.cosh ((t • s) 0) ≤ Real.cosh (s 0) := Real.cosh_le_cosh.mpr (key 0)
  have hp : 0 ≤ Real.cosh ((t • s) 0) := (Real.cosh_pos _).le
  nlinarith

theorem G_at_zero (μ c : ℝ) : ehLeftHamiltonian μ c 0 = μ - 1 := by
  unfold ehLeftHamiltonian
  simp
  ring

end

end EHConvex

end BirkhoffGlobalSection


