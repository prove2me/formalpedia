-- Prove2me | solution 1 for AnosovPlugs.plugGluing_localSteps_seam
-- status  : ACCEPTED   (prove)
-- author  : @ebayuser
-- created : 2026-10-04T21:22:45.04228+00:00
-- url     : https://prove2.me/submissions/9c227c3d-0e34-4085-b2f4-007a5e9f1f63

import Mathlib
import Definitions.Def_AnosovPlugs_Gluing
import Theorems.Thm_AnosovPlugs_exists_localFlow_contDiffOn_of_contDiffAt

open scoped Manifold ContDiff Topology
open Set AnosovPlugs



theorem sm_paste {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    {A B Ω : Set E} [DecidablePred (· ∈ A)] (hΩ : IsOpen Ω) (hA : IsClosed A)
    (hB : IsClosed B) (hcov : Ω ⊆ A ∪ B) {g h : E → F} {g' h' : E → E →L[ℝ] F}
    (hg : ∀ z ∈ A ∩ Ω, HasFDerivWithinAt g (g' z) A z)
    (hh : ∀ z ∈ B ∩ Ω, HasFDerivWithinAt h (h' z) B z)
    (hg' : ContinuousOn g' (A ∩ Ω)) (hh' : ContinuousOn h' (B ∩ Ω))
    (heq : ∀ z ∈ A ∩ B ∩ Ω, g z = h z) (heq' : ∀ z ∈ A ∩ B ∩ Ω, g' z = h' z) :
    (∀ z ∈ Ω, HasFDerivAt (fun z => if z ∈ A then g z else h z)
      (if z ∈ A then g' z else h' z) z) ∧
    ContDiffOn ℝ 1 (fun z => if z ∈ A then g z else h z) Ω := by
  set Fn : E → F := fun z => if z ∈ A then g z else h z with hFn
  set Fd : E → E →L[ℝ] F := fun z => if z ∈ A then g' z else h' z with hFd
  -- Fn agrees with g on A and with h on B ∩ Ω
  have hFA : ∀ z ∈ A, Fn z = g z := fun z hz => by simp [hFn, hz]
  have hFB : ∀ z ∈ B ∩ Ω, Fn z = h z := by
    intro z hz
    by_cases hzA : z ∈ A
    · simp only [hFn, hzA, if_true]; exact heq z ⟨⟨hzA, hz.1⟩, hz.2⟩
    · simp [hFn, hzA]
  have hdA : ∀ z ∈ A, Fd z = g' z := fun z hz => by simp [hFd, hz]
  have hdB : ∀ z ∈ B ∩ Ω, Fd z = h' z := by
    intro z hz
    by_cases hzA : z ∈ A
    · simp only [hFd, hzA, if_true]; exact heq' z ⟨⟨hzA, hz.1⟩, hz.2⟩
    · simp [hFd, hzA]
  -- within-A derivative of Fn at points of A ∩ Ω
  have hwA : ∀ z ∈ A ∩ Ω, HasFDerivWithinAt Fn (Fd z) (A ∩ Ω) z := by
    intro z hz
    rw [hdA z hz.1]
    exact ((hg z hz).mono inter_subset_left).congr (fun y hy => hFA y hy.1) (hFA z hz.1)
  have hwB : ∀ z ∈ B ∩ Ω, HasFDerivWithinAt Fn (Fd z) (B ∩ Ω) z := by
    intro z hz
    rw [hdB z hz]
    exact ((hh z hz).mono inter_subset_left).congr (fun y hy => hFB y hy) (hFB z hz)
  have hcA : ∀ z ∈ Ω, ContinuousWithinAt Fd (A ∩ Ω) z := by
    intro z hz
    by_cases hzA : z ∈ A
    · exact ((hg' z ⟨hzA, hz⟩).congr (fun y hy => hdA y hy.1) (hdA z hzA))
    · exact continuousWithinAt_of_notMem_closure (fun hc =>
        hzA ((closure_mono inter_subset_left).trans_eq hA.closure_eq hc))
  have hcB : ∀ z ∈ Ω, ContinuousWithinAt Fd (B ∩ Ω) z := by
    intro z hz
    by_cases hzB : z ∈ B
    · exact ((hh' z ⟨hzB, hz⟩).congr (fun y hy => hdB y hy) (hdB z ⟨hzB, hz⟩))
    · exact continuousWithinAt_of_notMem_closure (fun hc =>
        hzB ((closure_mono inter_subset_left).trans_eq hB.closure_eq hc))
  have hun : ∀ z ∈ Ω, (A ∩ Ω) ∪ (B ∩ Ω) ∈ 𝓝 z := by
    intro z hz
    refine Filter.mem_of_superset (hΩ.mem_nhds hz) ?_
    intro y hy
    rcases hcov hy with h1 | h1
    · exact Or.inl ⟨h1, hy⟩
    · exact Or.inr ⟨h1, hy⟩
  have hD : ∀ z ∈ Ω, HasFDerivAt Fn (Fd z) z := by
    intro z hz
    by_cases hzA : z ∈ A
    · by_cases hzB : z ∈ B
      · exact ((hwA z ⟨hzA, hz⟩).union (hwB z ⟨hzB, hz⟩)).hasFDerivAt (hun z hz)
      · -- near z, Ω \ B is a neighbourhood contained in A
        have hn : A ∩ Ω ∈ 𝓝 z := by
          refine Filter.mem_of_superset ((hΩ.sdiff hB).mem_nhds ⟨hz, hzB⟩) ?_
          intro y hy
          rcases hcov hy.1 with h1 | h1
          · exact ⟨h1, hy.1⟩
          · exact absurd h1 hy.2
        exact (hwA z ⟨hzA, hz⟩).hasFDerivAt hn
    · have hzB : z ∈ B := (hcov hz).resolve_left hzA
      have hn : B ∩ Ω ∈ 𝓝 z := by
        refine Filter.mem_of_superset ((hΩ.sdiff hA).mem_nhds ⟨hz, hzA⟩) ?_
        intro y hy
        rcases hcov hy.1 with h1 | h1
        · exact absurd h1 hy.2
        · exact ⟨h1, hy.1⟩
      exact (hwB z ⟨hzB, hz⟩).hasFDerivAt hn
  have hC : ContinuousOn Fd Ω := by
    intro z hz
    exact (((hcA z hz).union (hcB z hz)).continuousAt (hun z hz)).continuousWithinAt
  refine ⟨hD, ?_⟩
  intro z hz
  apply ContDiffAt.contDiffWithinAt
  rw [contDiffAt_one_iff]
  exact ⟨Fd, Ω, hΩ.mem_nhds hz, hC, hD⟩


noncomputable section


/-- `v ↦ v 0 • e₀`. -/
def sm_L : EuclideanSpace ℝ (Fin 3) →L[ℝ] EuclideanSpace ℝ (Fin 3) :=
  (EuclideanSpace.proj (0 : Fin 3)).smulRight (EuclideanSpace.single (0 : Fin 3) (1 : ℝ))

/-- projection onto the hyperplane `z 0 = 0`. -/
def sm_P : EuclideanSpace ℝ (Fin 3) →L[ℝ] EuclideanSpace ℝ (Fin 3) :=
  ContinuousLinearMap.id ℝ _ - sm_L

/-- reflection in the hyperplane `z 0 = 0`. -/
def sm_R : EuclideanSpace ℝ (Fin 3) →L[ℝ] EuclideanSpace ℝ (Fin 3) :=
  ContinuousLinearMap.id ℝ _ - (2 : ℝ) • sm_L

theorem sm_L_apply (v : EuclideanSpace ℝ (Fin 3)) :
    sm_L v = v 0 • EuclideanSpace.single (0 : Fin 3) (1 : ℝ) := rfl

theorem sm_P_apply0 (v : EuclideanSpace ℝ (Fin 3)) : (sm_P v) 0 = 0 := by
  simp [sm_P, sm_L_apply]

theorem sm_R_apply0 (v : EuclideanSpace ℝ (Fin 3)) : (sm_R v) 0 = - v 0 := by
  simp [sm_R, sm_L_apply]; ring

theorem sm_P_of (v : EuclideanSpace ℝ (Fin 3)) (hv : v 0 = 0) : sm_P v = v := by
  simp [sm_P, sm_L_apply, hv]

theorem sm_R_of (v : EuclideanSpace ℝ (Fin 3)) (hv : v 0 = 0) : sm_R v = v := by
  simp [sm_R, sm_L_apply, hv]

theorem sm_P_P (v : EuclideanSpace ℝ (Fin 3)) : sm_P (sm_P v) = sm_P v :=
  sm_P_of _ (sm_P_apply0 v)

theorem sm_P_R (v : EuclideanSpace ℝ (Fin 3)) : sm_P (sm_R v) = sm_P v := by
  simp only [sm_P, sm_R, sub_apply, ContinuousLinearMap.id_apply,
    smul_apply, map_sub, map_smul, sm_L_apply]
  ext i
  fin_cases i <;> simp

theorem sm_two_P_sub_R : (2 : ℝ) • sm_P - sm_R = ContinuousLinearMap.id ℝ _ := by
  ext v : 1
  simp only [sm_P, sm_R, sub_apply, smul_apply,
    ContinuousLinearMap.id_apply]
  module

theorem sm_decomp (v : EuclideanSpace ℝ (Fin 3)) :
    v = sm_P v + v 0 • EuclideanSpace.single (0 : Fin 3) (1 : ℝ) := by
  simp [sm_P, sm_L_apply]

/-- M2: first-order extension across the boundary hyperplane of the half-space. -/
theorem sm_ext {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {f : EuclideanSpace ℝ (Fin 3) → F} {a : EuclideanSpace ℝ (Fin 3)}
    (hf : ContDiffWithinAt ℝ 1 f {z | 0 ≤ z 0} a) (ha : a 0 = 0) :
    ∃ g : EuclideanSpace ℝ (Fin 3) → F, ContDiffAt ℝ 1 g a ∧
      ∃ r > (0 : ℝ), ∀ z ∈ Metric.ball a r, 0 ≤ z 0 → g z = f z := by
  classical
  set A : Set (EuclideanSpace ℝ (Fin 3)) := {z | 0 ≤ z 0} with hAdef
  set B : Set (EuclideanSpace ℝ (Fin 3)) := {z | z 0 ≤ 0} with hBdef
  have haA : a ∈ A := by simp [hAdef, ha]
  obtain ⟨u, hu, hau, hfu⟩ := hf.contDiffOn' le_rfl (by simp)
  rw [insert_eq_of_mem haA] at hfu
  obtain ⟨r0, hr0, hr0u⟩ := Metric.isOpen_iff.1 hu a hau
  set S := A ∩ Metric.ball a r0 with hS
  have hfS : ContDiffOn ℝ 1 f S := hfu.mono (inter_subset_inter_right _ hr0u)
  have hAc : IsClosed A := isClosed_le continuous_const (EuclideanSpace.proj (0 : Fin 3)).continuous
  have hBc : IsClosed B := isClosed_le (EuclideanSpace.proj (0 : Fin 3)).continuous continuous_const
  have hSconv : Convex ℝ S := by
    refine Convex.inter ?_ (convex_ball a r0)
    exact convex_halfSpace_ge (EuclideanSpace.proj (0 : Fin 3)).isLinear 0
  have hSint : (interior S).Nonempty := by
    refine ⟨a + (r0 / 2) • EuclideanSpace.single (0 : Fin 3) (1 : ℝ), ?_⟩
    have ho : IsOpen ({z : EuclideanSpace ℝ (Fin 3) | 0 < z 0} ∩ Metric.ball a r0) :=
      (isOpen_lt continuous_const (EuclideanSpace.proj (0 : Fin 3)).continuous).inter
        Metric.isOpen_ball
    have hsub : {z : EuclideanSpace ℝ (Fin 3) | 0 < z 0} ∩ Metric.ball a r0 ⊆ S :=
      fun z hz => ⟨show (0:ℝ) ≤ z 0 from le_of_lt hz.1, hz.2⟩
    refine interior_maximal hsub ho ⟨?_, ?_⟩
    · simp [ha]; linarith
    · rw [Metric.mem_ball, dist_eq_norm, add_sub_cancel_left, norm_smul, PiLp.norm_single]
      simp [abs_of_pos hr0]; linarith
  have hSu : UniqueDiffOn ℝ S := uniqueDiffOn_convex hSconv hSint
  set f' := fderivWithin ℝ f S with hf'def
  have hf'c : ContinuousOn f' S := hfS.continuousOn_fderivWithin hSu le_rfl
  have hfd : ∀ z ∈ S, HasFDerivWithinAt f (f' z) S z := fun z hz =>
    ((hfS.differentiableOn one_ne_zero) z hz).hasFDerivWithinAt
  set r := r0 / 2 with hr
  have hrpos : 0 < r := by positivity
  set Ω : Set (EuclideanSpace ℝ (Fin 3)) := {z | ‖sm_P z - a‖ < r ∧ |z 0| < r} with hΩ
  have hΩo : IsOpen Ω := by
    refine IsOpen.inter ?_ ?_
    · exact isOpen_lt ((sm_P.continuous.sub continuous_const).norm) continuous_const
    · exact isOpen_lt ((EuclideanSpace.proj (0 : Fin 3)).continuous.abs) continuous_const
  have hPa : sm_P a = a := sm_P_of a ha
  have haΩ : a ∈ Ω := by simp [hΩ, hPa, ha, hrpos]
  have hΩball : Ω ⊆ Metric.ball a r0 := by
    intro z hz
    rw [Metric.mem_ball, dist_eq_norm]
    have hd : z - a = (sm_P z - a) + z 0 • EuclideanSpace.single (0 : Fin 3) (1 : ℝ) := by
      conv_lhs => rw [sm_decomp z]
      abel
    rw [hd]
    calc ‖(sm_P z - a) + z 0 • EuclideanSpace.single (0 : Fin 3) (1 : ℝ)‖
        ≤ ‖sm_P z - a‖ + ‖z 0 • EuclideanSpace.single (0 : Fin 3) (1 : ℝ)‖ := norm_add_le _ _
      _ = ‖sm_P z - a‖ + |z 0| := by rw [norm_smul, PiLp.norm_single]; simp
      _ < r + r := add_lt_add hz.1 hz.2
      _ = r0 := by rw [hr]; ring
  have hPΩ : ∀ z ∈ Ω, sm_P z ∈ Ω := fun z hz => ⟨by rw [sm_P_P]; exact hz.1,
    by rw [sm_P_apply0]; simp [hrpos]⟩
  have hRΩ : ∀ z ∈ Ω, sm_R z ∈ Ω := fun z hz => ⟨by rw [sm_P_R]; exact hz.1,
    by rw [sm_R_apply0, abs_neg]; exact hz.2⟩
  have hPA : ∀ z, sm_P z ∈ A := fun z => by simp [hAdef, sm_P_apply0]
  have hRA : ∀ z ∈ B, sm_R z ∈ A := fun z hz => by
    simp only [hAdef, mem_ofPred_eq, sm_R_apply0]; simp only [hBdef, mem_ofPred_eq] at hz; linarith
  have hAΩS : ∀ z ∈ A ∩ Ω, z ∈ S := fun z hz => ⟨hz.1, hΩball hz.2⟩
  have hSnhds : ∀ z ∈ A ∩ Ω, S ∈ 𝓝[A] z := fun z hz =>
    inter_mem_nhdsWithin A (Metric.isOpen_ball.mem_nhds (hΩball hz.2))
  have hgA : ∀ z ∈ A ∩ Ω, HasFDerivWithinAt f (f' z) A z := fun z hz =>
    (hfd z (hAΩS z hz)).mono_of_mem_nhdsWithin (hSnhds z hz)
  set h : EuclideanSpace ℝ (Fin 3) → F := fun z => (2 : ℝ) • f (sm_P z) - f (sm_R z) with hhdef
  set h' : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3) →L[ℝ] F :=
    fun z => (2 : ℝ) • (f' (sm_P z)).comp sm_P - (f' (sm_R z)).comp sm_R with hh'def
  have hhB : ∀ z ∈ B ∩ Ω, HasFDerivWithinAt h (h' z) B z := by
    intro z hz
    have h1 : HasFDerivWithinAt (fun z => f (sm_P z)) ((f' (sm_P z)).comp sm_P) B z :=
      (hgA (sm_P z) ⟨hPA z, hPΩ z hz.2⟩).comp z sm_P.hasFDerivWithinAt (fun y _ => hPA y)
    have h2 : HasFDerivWithinAt (fun z => f (sm_R z)) ((f' (sm_R z)).comp sm_R) B z :=
      (hgA (sm_R z) ⟨hRA z hz.1, hRΩ z hz.2⟩).comp z sm_R.hasFDerivWithinAt
        (fun y hy => hRA y hy)
    exact (h1.const_smul (2 : ℝ)).sub h2
  have hgc : ContinuousOn f' (A ∩ Ω) := hf'c.mono (fun z hz => hAΩS z hz)
  have hhc : ContinuousOn h' (B ∩ Ω) := by
    have c1 : ContinuousOn (fun z => f' (sm_P z)) (B ∩ Ω) :=
      hf'c.comp sm_P.continuous.continuousOn
        (fun z hz => hAΩS _ ⟨hPA z, hPΩ z hz.2⟩)
    have c2 : ContinuousOn (fun z => f' (sm_R z)) (B ∩ Ω) :=
      hf'c.comp sm_R.continuous.continuousOn
        (fun z hz => hAΩS _ ⟨hRA z hz.1, hRΩ z hz.2⟩)
    exact ((c1.clm_comp continuousOn_const).const_smul (2 : ℝ)).sub
      (c2.clm_comp continuousOn_const)
  have hcov : Ω ⊆ A ∪ B := fun z _ => by
    rcases le_total 0 (z 0) with h0 | h0
    · exact Or.inl h0
    · exact Or.inr h0
  have hzero : ∀ z ∈ A ∩ B ∩ Ω, z 0 = 0 := fun z hz => le_antisymm hz.1.2 hz.1.1
  have heq : ∀ z ∈ A ∩ B ∩ Ω, f z = h z := by
    intro z hz
    simp only [hhdef, sm_P_of z (hzero z hz), sm_R_of z (hzero z hz)]
    module
  have heq' : ∀ z ∈ A ∩ B ∩ Ω, f' z = h' z := by
    intro z hz
    simp only [hh'def, sm_P_of z (hzero z hz), sm_R_of z (hzero z hz)]
    rw [← ContinuousLinearMap.comp_smul, ← ContinuousLinearMap.comp_sub, sm_two_P_sub_R]
    rfl
  obtain ⟨-, hCD⟩ := sm_paste hΩo hAc hBc hcov hgA hhB hgc hhc heq heq'
  refine ⟨fun z => if z ∈ A then f z else h z, hCD.contDiffAt (hΩo.mem_nhds haΩ), ?_⟩
  obtain ⟨r1, hr1, hr1Ω⟩ := Metric.isOpen_iff.1 hΩo a haΩ
  refine ⟨r1, hr1, fun z _ hz => ?_⟩
  have : z ∈ A := hz
  simp [this]


/-- M3 (chart level): the local flow of the extended chart field at a boundary point; for
`σ = ±1` with `σ · v(a)₀ > 0`, curves from hyperplane points stay in the half-space for times in
`uIcc 0 (σ ε)`. -/
theorem sm_flow {v : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3)}
    {a : EuclideanSpace ℝ (Fin 3)}
    (hv : ContDiffWithinAt ℝ 1 v {z | 0 ≤ z 0} a) (ha : a 0 = 0) {σ : ℝ}
    (hσ : σ = 1 ∨ σ = -1) (hva : 0 < σ * (v a) 0) {G : Set (EuclideanSpace ℝ (Fin 3))}
    (hG : G ∈ 𝓝[{z | 0 ≤ z 0}] a) :
    ∃ ε > (0 : ℝ), ∃ ρ > (0 : ℝ), ∃ α : EuclideanSpace ℝ (Fin 3) × ℝ → EuclideanSpace ℝ (Fin 3),
      ContDiffOn ℝ 1 α (Metric.ball a ρ ×ˢ Ioo (-ε) ε) ∧
      (∀ z ∈ Metric.ball a ρ, α (z, 0) = z) ∧
      (∀ z ∈ Metric.ball a ρ, z 0 = 0 → ∀ τ ∈ uIcc 0 (σ * ε),
        HasDerivAt (fun t => α (z, t)) (v (α (z, τ))) τ ∧ α (z, τ) ∈ G ∧ 0 ≤ (α (z, τ)) 0) ∧
      HasFDerivAt α ((ContinuousLinearMap.fst ℝ _ ℝ) +
        (ContinuousLinearMap.snd ℝ (EuclideanSpace ℝ (Fin 3)) ℝ).smulRight (v a)) (a, 0) := by
  obtain ⟨vt, hvt, r1, hr1, hvt_eq⟩ := sm_ext hv ha
  have hvta : vt a = v a := hvt_eq a (Metric.mem_ball_self hr1) (by simp [ha])
  have hcont : ContinuousAt (fun w => σ * (vt w) 0) a :=
    continuousAt_const.mul ((EuclideanSpace.proj (0 : Fin 3)).continuous.continuousAt.comp
      hvt.continuousAt)
  have hev : ∀ᶠ w in 𝓝 a, 0 < σ * (vt w) 0 :=
    hcont.eventually (lt_mem_nhds (by simpa [hvta] using hva))
  obtain ⟨r2, hr2, hr2'⟩ := Metric.eventually_nhds_iff_ball.1 hev
  obtain ⟨r3, hr3, hr3'⟩ := Metric.mem_nhdsWithin_iff.1 hG
  set r := min r1 (min r2 r3) with hr
  have hrpos : 0 < r := lt_min hr1 (lt_min hr2 hr3)
  obtain ⟨ε, hε, ρ, hρ, α, hflow, hαC, -⟩ :=
    AnosovPlugs.exists_localFlow_contDiffOn_of_contDiffAt hvt Metric.isOpen_ball
      (Metric.mem_ball_self hrpos)
  have hball : ∀ w ∈ Metric.ball a r, w ∈ Metric.ball a r1 ∧ w ∈ Metric.ball a r2 ∧
      w ∈ Metric.ball a r3 := fun w hw => by
    simp only [Metric.mem_ball] at hw ⊢
    exact ⟨lt_of_lt_of_le hw (min_le_left _ _),
      lt_of_lt_of_le hw ((min_le_right _ _).trans (min_le_left _ _)),
      lt_of_lt_of_le hw ((min_le_right _ _).trans (min_le_right _ _))⟩
  refine ⟨ε, hε, ρ, hρ, α, hαC, fun z hz => (hflow z hz).1, ?_, ?_⟩
  · intro z hz hz0 τ hτ
    have hsub : uIcc 0 (σ * ε) ⊆ Icc (-ε) ε := by
      rcases hσ with rfl | rfl
      · rw [one_mul, uIcc_of_le hε.le]; exact Icc_subset_Icc (by linarith) le_rfl
      · rw [neg_one_mul, uIcc_of_ge (by linarith)]; exact Icc_subset_Icc le_rfl (by linarith)
    -- the normal coordinate along the curve
    set f : ℝ → ℝ := fun t => (α (z, t)) 0 with hfdef
    have hfd : ∀ t ∈ Icc (-ε) ε, HasDerivAt f ((vt (α (z, t))) 0) t := by
      intro t ht
      have h := ((hflow z hz).2 t ht).1
      have := (EuclideanSpace.proj (0 : Fin 3)).hasFDerivAt.comp_hasDerivAt t h
      exact this
    have hpos : ∀ t ∈ Icc (-ε) ε, 0 < σ * (vt (α (z, t))) 0 := fun t ht =>
      (hr2' _ (hball _ ((hflow z hz).2 t ht).2).2.1)
    have hf0 : f 0 = 0 := by simp [hfdef, (hflow z hz).1, hz0]
    have hnn : 0 ≤ f τ := by
      rcases hσ with rfl | rfl
      · rw [one_mul, uIcc_of_le hε.le] at hτ
        have hmono : MonotoneOn f (Icc 0 ε) := by
          refine monotoneOn_of_hasDerivWithinAt_nonneg (f' := fun t => (vt (α (z, t))) 0)
            (convex_Icc 0 ε) ?_ ?_ ?_
          · intro t ht
            exact (hfd t ⟨by linarith [ht.1], ht.2⟩).continuousAt.continuousWithinAt
          · intro t ht
            have ht' := interior_subset ht
            exact (hfd t ⟨by linarith [ht'.1], ht'.2⟩).hasDerivWithinAt
          · intro t ht
            have ht' := interior_subset ht
            have := hpos t ⟨by linarith [ht'.1], ht'.2⟩
            linarith
        have := hmono ⟨le_rfl, hε.le⟩ hτ hτ.1
        linarith
      · rw [neg_one_mul, uIcc_of_ge (by linarith)] at hτ
        have hanti : AntitoneOn f (Icc (-ε) 0) := by
          refine antitoneOn_of_hasDerivWithinAt_nonpos (f' := fun t => (vt (α (z, t))) 0)
            (convex_Icc (-ε) 0) ?_ ?_ ?_
          · intro t ht
            exact (hfd t ⟨ht.1, by linarith [ht.2]⟩).continuousAt.continuousWithinAt
          · intro t ht
            have ht' := interior_subset ht
            exact (hfd t ⟨ht'.1, by linarith [ht'.2]⟩).hasDerivWithinAt
          · intro t ht
            have ht' := interior_subset ht
            have := hpos t ⟨ht'.1, by linarith [ht'.2]⟩
            linarith
        have := hanti hτ ⟨by linarith, le_rfl⟩ hτ.2
        linarith
    have hmem := hball _ ((hflow z hz).2 τ (hsub hτ)).2
    have hA : α (z, τ) ∈ ({z | 0 ≤ z 0} : Set (EuclideanSpace ℝ (Fin 3))) := hnn
    refine ⟨?_, hr3' ⟨hmem.2.2, hA⟩, hnn⟩
    rw [← hvt_eq _ hmem.1 hnn]
    exact ((hflow z hz).2 τ (hsub hτ)).1
  · -- derivative at (a, 0)
    have hopen : IsOpen (Metric.ball a ρ ×ˢ Ioo (-ε) ε) := Metric.isOpen_ball.prod isOpen_Ioo
    have hmem : ((a, 0) : EuclideanSpace ℝ (Fin 3) × ℝ) ∈ Metric.ball a ρ ×ˢ Ioo (-ε) ε :=
      ⟨Metric.mem_ball_self hρ, by simp [hε]⟩
    have hdiff : HasFDerivAt α (fderiv ℝ α (a, 0)) (a, 0) :=
      ((hαC.contDiffAt (hopen.mem_nhds hmem)).differentiableAt one_ne_zero).hasFDerivAt
    set D := fderiv ℝ α (a, 0) with hD
    -- the z-partial
    have h1 : HasFDerivAt (fun z => α (z, 0)) (D.comp (ContinuousLinearMap.inl ℝ _ ℝ)) a :=
      hdiff.comp a ((hasFDerivAt_id a).prodMk (hasFDerivAt_const 0 a))
    have h1' : HasFDerivAt (fun z => α (z, 0)) (ContinuousLinearMap.id ℝ _) a := by
      refine (hasFDerivAt_id a).congr_of_eventuallyEq ?_
      filter_upwards [Metric.isOpen_ball.mem_nhds (Metric.mem_ball_self hρ)] with z hz
      exact (hflow z hz).1
    have e1 := h1.unique h1'
    -- the t-partial
    have h2 : HasDerivAt (fun t => α (a, t)) (D (0, 1)) 0 := by
      have := hdiff.comp_hasDerivAt (0 : ℝ) ((hasDerivAt_const (0 : ℝ) a).prodMk (hasDerivAt_id 0))
      exact this
    have h2' : HasDerivAt (fun t => α (a, t)) (v a) 0 := by
      have := ((hflow a (Metric.mem_ball_self hρ)).2 0 ⟨by linarith, hε.le⟩).1
      rwa [(hflow a (Metric.mem_ball_self hρ)).1, hvta] at this
    have e2 := h2.unique h2'
    convert hdiff using 1
    ext1
    · rw [e1]; ext1 h; simp
    · ext1; simp [← e2]


end


section ManifoldHelpers
set_option linter.unusedSectionVars false

variable {M : Type} [TopologicalSpace M] [ChartedSpace (EuclideanHalfSpace 3) M]
  [IsManifold I3 ∞ M]

/-- In a chart, a target point is in the interior of the target iff its coordinate `0` is
positive. -/
theorem sm_mem_interior_target_iff (x₀ : M) {z : EuclideanSpace ℝ (Fin 3)}
    (hz : z ∈ (extChartAt I3 x₀).target) :
    z ∈ interior (extChartAt I3 x₀).target ↔ 0 < z 0 := by
  constructor
  · intro h
    have h1 := interior_mono (extChartAt_target_subset_range (I := I3) x₀) h
    rw [interior_range_modelWithCornersEuclideanHalfSpace] at h1
    exact h1
  · intro h
    set V : Set (EuclideanSpace ℝ (Fin 3)) :=
      I3.symm ⁻¹' (chartAt (EuclideanHalfSpace 3) x₀).target with hV
    have hVo : IsOpen V := (chartAt (EuclideanHalfSpace 3) x₀).open_target.preimage
      I3.continuous_symm
    have hsub : V ∩ {y : EuclideanSpace ℝ (Fin 3) | 0 < y 0} ⊆ (extChartAt I3 x₀).target := by
      intro y hy
      rw [extChartAt_target]
      refine ⟨hy.1, ?_⟩
      rw [range_modelWithCornersEuclideanHalfSpace]
      exact le_of_lt (show (0:ℝ) < y 0 from hy.2)
    have hzV : z ∈ V := by
      rw [extChartAt_target] at hz; exact hz.1
    exact interior_maximal hsub
      (hVo.inter (isOpen_lt continuous_const (EuclideanSpace.proj (0 : Fin 3)).continuous))
      ⟨hzV, h⟩

/-- Boundary points, read in the chart at an arbitrary base point. -/
theorem sm_boundary_iff (x₀ : M) {s : M} (hs : s ∈ (extChartAt I3 x₀).source) :
    s ∈ I3.boundary M ↔ (extChartAt I3 x₀ s) 0 = 0 := by
  have hs' : s ∈ (chartAt (EuclideanHalfSpace 3) x₀).source := by
    rwa [← extChartAt_source I3]
  have hmem : extChartAt I3 x₀ s ∈ (extChartAt I3 x₀).target :=
    (extChartAt I3 x₀).map_source hs
  have hge : 0 ≤ (extChartAt I3 x₀ s) 0 := by
    have := extChartAt_target_subset_range (I := I3) x₀ hmem
    rw [range_modelWithCornersEuclideanHalfSpace] at this
    exact this
  have key : I3.IsInteriorPoint s ↔ 0 < (extChartAt I3 x₀ s) 0 := by
    rw [I3.isInteriorPoint_iff_of_mem_atlas (n := ∞) (by simp)
      (chart_mem_atlas (EuclideanHalfSpace 3) x₀) hs']
    exact sm_mem_interior_target_iff x₀ hmem
  show I3.IsBoundaryPoint s ↔ _
  have hb : I3.IsBoundaryPoint s ↔ ¬ I3.IsInteriorPoint s := by
    rw [I3.isInteriorPoint_iff_not_isBoundaryPoint, not_not]
  rw [hb, key]
  constructor
  · intro h; exact le_antisymm (not_lt.1 h) hge
  · intro h; rw [h]; exact lt_irrefl 0

set_option backward.isDefEq.respectTransparency false in
/-- Chart changes at a boundary point keep the closed inward half-space of vectors. -/
theorem sm_tcc_nonneg {x y s : M} (hx : s ∈ (extChartAt I3 x).source)
    (hy : s ∈ (extChartAt I3 y).source) (hs : s ∈ I3.boundary M)
    {v : EuclideanSpace ℝ (Fin 3)} (hv : 0 ≤ v 0) :
    0 ≤ (tangentCoordChange I3 x y s v) 0 := by
  have hF := hasFDerivWithinAt_tangentCoordChange (I := I3) ⟨hx, hy⟩
  set b := extChartAt I3 x s with hb
  have hb0 : b 0 = 0 := (sm_boundary_iff x hx).1 hs
  have hFb : ((extChartAt I3 y ∘ (extChartAt I3 x).symm) b) 0 = 0 := by
    simp only [Function.comp_apply, hb, (extChartAt I3 x).left_inv hx]
    exact (sm_boundary_iff y hy).1 hs
  have hf := (EuclideanSpace.proj (0 : Fin 3)).hasFDerivAt.comp_hasFDerivWithinAt b hF
  have hmin : IsLocalMinOn (fun w => (EuclideanSpace.proj (0 : Fin 3))
      ((extChartAt I3 y ∘ (extChartAt I3 x).symm) w)) (range I3) b := by
    refine Filter.Eventually.of_forall (fun w => ?_)
    show (EuclideanSpace.proj (0 : Fin 3)) _ ≤ (EuclideanSpace.proj (0 : Fin 3)) _
    have hr : (extChartAt I3 y ∘ (extChartAt I3 x).symm) w ∈ range I3 := by
      simp only [Function.comp_apply, extChartAt_coe]
      exact mem_range_self _
    rw [range_modelWithCornersEuclideanHalfSpace] at hr
    change ((extChartAt I3 y ∘ (extChartAt I3 x).symm) b) 0 ≤
      ((extChartAt I3 y ∘ (extChartAt I3 x).symm) w) 0
    rw [hFb]; exact hr
  have hcone : v ∈ posTangentConeAt (range I3) b := by
    apply mem_posTangentConeAt_of_segment_subset
    apply I3.convex_range.segment_subset
    · rw [range_modelWithCornersEuclideanHalfSpace]; simp [hb0]
    · rw [range_modelWithCornersEuclideanHalfSpace]
      simp only [mem_ofPred_eq, PiLp.add_apply, hb0, zero_add]; exact hv
  have := hmin.hasFDerivWithinAt_nonneg hf hcone
  simpa using this

set_option backward.isDefEq.respectTransparency false in
/-- Chart changes at a boundary point keep the open inward half-space of vectors. -/
theorem sm_tcc_pos {x y s : M} (hx : s ∈ (extChartAt I3 x).source)
    (hy : s ∈ (extChartAt I3 y).source) (hs : s ∈ I3.boundary M)
    {v : EuclideanSpace ℝ (Fin 3)} (hv : 0 < v 0) :
    0 < (tangentCoordChange I3 x y s v) 0 := by
  set w := tangentCoordChange I3 x y s v with hw
  have h1 : 0 ≤ w 0 := sm_tcc_nonneg hx hy hs hv.le
  by_contra hcon
  have hw0 : w 0 = 0 := le_antisymm (not_lt.1 hcon) h1
  have hback : tangentCoordChange I3 y x s w = v := by
    rw [hw, tangentCoordChange_comp ⟨⟨hx, hy⟩, hx⟩, tangentCoordChange_self hx]
  have h2 : 0 ≤ (tangentCoordChange I3 y x s (-w)) 0 :=
    sm_tcc_nonneg hy hx hs (by simp [hw0])
  rw [map_neg, hback] at h2
  simp at h2
  linarith

theorem sm_tcc_neg {x y s : M} (hx : s ∈ (extChartAt I3 x).source)
    (hy : s ∈ (extChartAt I3 y).source) (hs : s ∈ I3.boundary M)
    {v : EuclideanSpace ℝ (Fin 3)} (hv : v 0 < 0) :
    (tangentCoordChange I3 x y s v) 0 < 0 := by
  have := sm_tcc_pos hx hy hs (v := -v) (by simp; linarith)
  rw [map_neg] at this
  simpa using this

end ManifoldHelpers

section Lift

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]

set_option backward.isDefEq.respectTransparency false in
/-- A chart curve with a within-derivative gives a manifold curve with a within-derivative. -/
theorem sm_lift {x₀ : M} {c : ℝ → E} {s : Set ℝ} {t : ℝ} {u : E}
    (hc : HasDerivWithinAt c u s t) (hmaps : MapsTo c s (extChartAt I x₀).target) (ht : t ∈ s) :
    HasMFDerivWithinAt 𝓘(ℝ, ℝ) I ((extChartAt I x₀).symm ∘ c) s t
      ((1 : ℝ →L[ℝ] ℝ).smulRight (tangentCoordChange I x₀ ((extChartAt I x₀).symm (c t))
        ((extChartAt I x₀).symm (c t)) u)) := by
  set xₜ : M := (extChartAt I x₀).symm (c t) with hxt
  have hct := hmaps ht
  have hft1 : xₜ ∈ (extChartAt I x₀).source := (extChartAt I x₀).map_target hct
  have hft2 := mem_extChartAt_source (I := I) xₜ
  refine ⟨((continuousOn_extChartAt_symm x₀) _ hct).comp hc.continuousWithinAt hmaps,
    HasDerivWithinAt.hasFDerivWithinAt ?_⟩
  simp only [mfld_simps]
  change HasDerivWithinAt ((extChartAt I xₜ ∘ (extChartAt I x₀).symm) ∘ c)
    (tangentCoordChange I x₀ xₜ xₜ u) s t
  have hF := hasFDerivWithinAt_tangentCoordChange (I := I) ⟨hft1, hft2⟩
  rw [hxt, (extChartAt I x₀).right_inv hct] at hF
  exact hF.comp_hasDerivWithinAt t hc
    (fun r hr => extChartAt_target_subset_range (I := I) x₀ (hmaps hr))

set_option backward.isDefEq.respectTransparency false in
/-- The integral-curve form of `sm_lift`. -/
theorem sm_lift_field {x₀ : M} {X : (x : M) → TangentSpace I x} {c : ℝ → E} {s : Set ℝ}
    (hc : ∀ t ∈ s, HasDerivWithinAt c (tangentCoordChange I ((extChartAt I x₀).symm (c t)) x₀
      ((extChartAt I x₀).symm (c t)) (X ((extChartAt I x₀).symm (c t)))) s t)
    (hmaps : MapsTo c s (extChartAt I x₀).target) :
    IsMIntegralCurveOn ((extChartAt I x₀).symm ∘ c) X s := by
  intro t ht
  have h := sm_lift (hc t ht) hmaps ht
  have hft1 : (extChartAt I x₀).symm (c t) ∈ (extChartAt I x₀).source :=
    (extChartAt I x₀).map_target (hmaps ht)
  have hft2 := mem_extChartAt_source (I := I) ((extChartAt I x₀).symm (c t))
  rw [tangentCoordChange_comp ⟨⟨hft2, hft1⟩, hft2⟩, tangentCoordChange_self hft2] at h
  exact h

end Lift

set_option backward.isDefEq.respectTransparency false in
/-- Push an integral curve forward by a `C¹` map that sends `X` to `Z`. -/
theorem sm_comp_curve
    {M : Type} [TopologicalSpace M] [ChartedSpace (EuclideanHalfSpace 3) M] [IsManifold I3 ∞ M]
    {N : Type} [TopologicalSpace N] [ChartedSpace (EuclideanHalfSpace 3) N] [IsManifold I3 ∞ N]
    (X : (x : M) → TangentSpace I3 x) (Z : (w : N) → TangentSpace I3 w) (i : M → N)
    (hi : ContMDiff I3 I3 1 i) (hZ : ∀ x, mfderiv I3 I3 i x (X x) = Z (i x))
    {γ : ℝ → M} {s : Set ℝ} (hγ : IsMIntegralCurveOn γ X s) :
    IsMIntegralCurveOn (i ∘ γ) Z s := by
  intro t ht
  have hd := ((hi (γ t)).mdifferentiableAt one_ne_zero).hasMFDerivAt
  refine (HasMFDerivAt.comp_hasMFDerivWithinAt (f := γ) t hd (hγ t ht)).congr_mfderiv ?_
  ext1
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.smulRight_apply,
    one_apply_eq_self, one_smul, Function.comp_apply]
  exact hZ (γ t)

set_option backward.isDefEq.respectTransparency false in
/-- The chart field of a `C¹` vector field is `C¹` within the model range. -/
theorem sm_chartField
    {M : Type} [TopologicalSpace M] [ChartedSpace (EuclideanHalfSpace 3) M] [IsManifold I3 ∞ M]
    (X : (x : M) → TangentSpace I3 x) (hX : IsC1VectorField X) (x₀ : M) :
    ContDiffWithinAt ℝ 1 (fun z => tangentCoordChange I3 ((extChartAt I3 x₀).symm z) x₀
        ((extChartAt I3 x₀).symm z) (X ((extChartAt I3 x₀).symm z)))
      {z | 0 ≤ z 0} (extChartAt I3 x₀ x₀) := by
  have hX' : ContMDiff I3 I3.tangent 1 (fun x => (⟨x, X x⟩ : TangentBundle I3 M)) := hX
  have h := hX' x₀
  rw [contMDiffAt_iff] at h
  obtain ⟨_, h⟩ := h
  rw [← range_modelWithCornersEuclideanHalfSpace]
  exact h.snd

set_option backward.isDefEq.respectTransparency false in
/-- M4: near a point of `T ⊆ outBoundary X` that is a union of components, every point of
the boundary hyperplane (in the chart) belongs to `T`. -/
theorem sm_tout
    {M : Type} [TopologicalSpace M] [ChartedSpace (EuclideanHalfSpace 3) M] [IsManifold I3 ∞ M]
    (X : (x : M) → TangentSpace I3 x) (hX : IsC1VectorField X) (T : Set M)
    (hT : IsUnionOfComponents T (outBoundary X)) (x : M) (hx : x ∈ T) :
    ∃ r > (0 : ℝ), ∀ z ∈ Metric.ball (extChartAt I3 x x) r, z 0 = 0 →
      z ∈ (extChartAt I3 x).target ∧ (extChartAt I3 x).symm z ∈ T := by
  set e := extChartAt I3 x with he
  set a := e x with ha
  set v : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3) := fun z =>
    tangentCoordChange I3 (e.symm z) x (e.symm z) (X (e.symm z)) with hv
  have hxout : x ∈ outBoundary X := hT.1 hx
  have hva : v a = X x := by
    show tangentCoordChange I3 (e.symm a) x (e.symm a) (X (e.symm a)) = X x
    have h1 : e.symm a = x := e.left_inv (mem_extChartAt_source (I := I3) x)
    rw [h1]
    exact tangentCoordChange_self (mem_extChartAt_source (I := I3) x)
  have hcont : ContinuousWithinAt v {z | 0 ≤ z 0} a := (sm_chartField X hX x).continuousWithinAt
  have hneg : ∀ᶠ z in 𝓝[{z | 0 ≤ z 0}] a, (v z) 0 < 0 := by
    have : ContinuousWithinAt (fun z => (v z) 0) {z | 0 ≤ z 0} a :=
      (EuclideanSpace.proj (0 : Fin 3)).continuous.continuousAt.comp_continuousWithinAt hcont
    exact this.eventually (gt_mem_nhds (by show (v a) 0 < 0; rw [hva]; exact hxout.2))
  have htgt : e.target ∈ 𝓝[{z | 0 ≤ z 0}] a := by
    rw [← range_modelWithCornersEuclideanHalfSpace]; exact extChartAt_target_mem_nhdsWithin x
  obtain ⟨r, hr, hsub⟩ := Metric.mem_nhdsWithin_iff.1 (Filter.inter_mem hneg htgt)
  refine ⟨r, hr, ?_⟩
  set D := Metric.ball a r ∩ {z : EuclideanSpace ℝ (Fin 3) | z 0 = 0} with hD
  have hDsub : ∀ z ∈ D, (v z) 0 < 0 ∧ z ∈ e.target := fun z hz =>
    hsub ⟨hz.1, show (0 : ℝ) ≤ z 0 from le_of_eq hz.2.symm⟩
  have hDout : ∀ z ∈ D, e.symm z ∈ outBoundary X := by
    intro z hz
    obtain ⟨hvz, hzt⟩ := hDsub z hz
    have hsrc : e.symm z ∈ e.source := e.map_target hzt
    have hbd : e.symm z ∈ I3.boundary M := by
      rw [sm_boundary_iff x hsrc, e.right_inv hzt]; exact hz.2
    refine ⟨hbd, ?_⟩
    have hself := mem_extChartAt_source (I := I3) (e.symm z)
    have := sm_tcc_neg hsrc hself hbd hvz
    have hvz' : v z = tangentCoordChange I3 (e.symm z) x (e.symm z) (X (e.symm z)) := rfl
    rw [hvz', tangentCoordChange_comp ⟨⟨hself, hsrc⟩, hself⟩, tangentCoordChange_self hself] at this
    exact this
  have haD : a ∈ D := ⟨Metric.mem_ball_self hr, (sm_boundary_iff x (mem_extChartAt_source (I := I3) x)).1
    hxout.1⟩
  have hDconv : Convex ℝ D := by
    refine (convex_ball a r).inter ?_
    have : {z : EuclideanSpace ℝ (Fin 3) | z 0 = 0} =
        (EuclideanSpace.proj (0 : Fin 3)) ⁻¹' {0} := by ext z; simp
    rw [this]
    exact (convex_singleton 0).linear_preimage (EuclideanSpace.proj (0 : Fin 3)).toLinearMap
  have hpre : IsPreconnected (e.symm '' D) :=
    hDconv.isPreconnected.image _ ((continuousOn_extChartAt_symm x).mono
      (fun z hz => (hDsub z hz).2))
  have hxD : x ∈ e.symm '' D := ⟨a, haD, e.left_inv (mem_extChartAt_source (I := I3) x)⟩
  have hcc : e.symm '' D ⊆ connectedComponentIn (outBoundary X) x :=
    hpre.subset_connectedComponentIn hxD (by rintro _ ⟨z, hz, rfl⟩; exact hDout z hz)
  intro z hz hz0
  exact ⟨(hDsub z ⟨hz, hz0⟩).2, hT.2 x hx (hcc ⟨z, ⟨hz, hz0⟩, rfl⟩)⟩


set_option backward.isDefEq.respectTransparency false in
/-- The flow-box piece on one side of the seam: a `C¹` chart map `K` near `(a, 0)` that reads
`i ∘ γ_z` in the chart of `N` at `i x₀`, where `γ_z` is the `X`-integral curve from the boundary
point with chart coordinates `z`, for times in `uIcc 0 (σ ε)`. -/
theorem sm_piece
    {M : Type} [TopologicalSpace M] [ChartedSpace (EuclideanHalfSpace 3) M] [IsManifold I3 ∞ M]
    {N : Type} [TopologicalSpace N] [ChartedSpace (EuclideanHalfSpace 3) N] [IsManifold I3 ∞ N]
    (X : (x : M) → TangentSpace I3 x) (hX : IsC1VectorField X)
    (i : M → N) (hi : ContMDiff I3 I3 1 i)
    (x₀ : M) (hx₀ : x₀ ∈ I3.boundary M) {σ : ℝ} (hσ : σ = 1 ∨ σ = -1)
    (hXx : 0 < σ * normalCoord (X x₀)) :
    ∃ K : EuclideanSpace ℝ (Fin 3) × ℝ → EuclideanSpace ℝ (Fin 3), ∃ ε > (0 : ℝ), ∃ ρ > (0 : ℝ),
      ContDiffAt ℝ 1 K (extChartAt I3 x₀ x₀, 0) ∧
      HasFDerivAt K ((mfderiv I3 I3 i x₀ : EuclideanSpace ℝ (Fin 3) →L[ℝ] EuclideanSpace ℝ (Fin 3)).comp
        ((ContinuousLinearMap.fst ℝ (EuclideanSpace ℝ (Fin 3)) ℝ) +
        (ContinuousLinearMap.snd ℝ (EuclideanSpace ℝ (Fin 3)) ℝ).smulRight (id (X x₀) : EuclideanSpace ℝ (Fin 3))))
        (extChartAt I3 x₀ x₀, 0) ∧
      ∀ z ∈ Metric.ball (extChartAt I3 x₀ x₀) ρ, z 0 = 0 →
        z ∈ (extChartAt I3 x₀).target ∧
        ∃ γ : ℝ → M, γ 0 = (extChartAt I3 x₀).symm z ∧
          IsMIntegralCurveOn γ X (uIcc 0 (σ * ε)) ∧
          ∀ τ ∈ uIcc 0 (σ * ε), i (γ τ) ∈ (extChartAt I3 (i x₀)).source ∧
            K (z, τ) = extChartAt I3 (i x₀) (i (γ τ)) := by
  set e := extChartAt I3 x₀ with he
  set a := e x₀ with ha
  set eN := extChartAt I3 (i x₀) with heN
  have hx₀src : x₀ ∈ e.source := mem_extChartAt_source (I := I3) x₀
  have ha0 : a 0 = 0 := (sm_boundary_iff x₀ hx₀src).1 hx₀
  set v : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3) := fun z =>
    tangentCoordChange I3 (e.symm z) x₀ (e.symm z) (X (e.symm z)) with hvdef
  have hv : ContDiffWithinAt ℝ 1 v {z | 0 ≤ z 0} a := sm_chartField X hX x₀
  have hva : v a = X x₀ := by
    show tangentCoordChange I3 (e.symm a) x₀ (e.symm a) (X (e.symm a)) = X x₀
    have h1 : e.symm a = x₀ := e.left_inv hx₀src
    rw [h1]
    exact tangentCoordChange_self hx₀src
  set Φ := writtenInExtChartAt I3 I3 x₀ i with hΦdef
  have hΦ : ContDiffWithinAt ℝ 1 Φ {z | 0 ≤ z 0} a := by
    rw [← range_modelWithCornersEuclideanHalfSpace]
    exact (contMDiffAt_iff.1 (hi x₀)).2
  obtain ⟨Φt, hΦt, r1, hr1, hΦt_eq⟩ := sm_ext hΦ ha0
  -- the target set for the flow
  set G : Set (EuclideanSpace ℝ (Fin 3)) :=
    Metric.ball a r1 ∩ e.target ∩ e.symm ⁻¹' (i ⁻¹' eN.source) with hGdef
  have hG : G ∈ 𝓝[{z | 0 ≤ z 0}] a := by
    rw [← range_modelWithCornersEuclideanHalfSpace]
    refine Filter.inter_mem (Filter.inter_mem
      (mem_nhdsWithin_of_mem_nhds (Metric.isOpen_ball.mem_nhds (Metric.mem_ball_self hr1)))
      (extChartAt_target_mem_nhdsWithin x₀)) ?_
    have hpre : i ⁻¹' eN.source ∈ 𝓝 x₀ :=
      (hi x₀).continuousAt.preimage_mem_nhds (extChartAt_source_mem_nhds (I := I3) (i x₀))
    have := extChartAt_preimage_mem_nhdsWithin (I := I3) (s := univ) (x := x₀)
      (by rwa [nhdsWithin_univ])
    simpa only [preimage_univ, univ_inter] using this
  obtain ⟨ε, hε, ρ, hρ, α, hαC, hα0, hαcurve, hαD⟩ :=
    sm_flow hv ha0 hσ (by rw [hva]; exact hXx) hG
  refine ⟨fun p => Φt (α p), ε, hε, ρ, hρ, ?_, ?_, ?_⟩
  · have hαa : α (a, 0) = a := hα0 a (Metric.mem_ball_self hρ)
    have hopen : IsOpen (Metric.ball a ρ ×ˢ Ioo (-ε) ε) := Metric.isOpen_ball.prod isOpen_Ioo
    have hαCa : ContDiffAt ℝ 1 α (a, 0) :=
      hαC.contDiffAt (hopen.mem_nhds ⟨Metric.mem_ball_self hρ, by simp [hε]⟩)
    have hΦt' : ContDiffAt ℝ 1 Φt (α (a, 0)) := by rw [hαa]; exact hΦt
    exact hΦt'.comp (a, 0) hαCa
  · have hαa : α (a, 0) = a := hα0 a (Metric.mem_ball_self hρ)
    have hΦw : HasFDerivWithinAt Φ (mfderiv I3 I3 i x₀) (range I3) a :=
      ((hi x₀).mdifferentiableAt one_ne_zero).hasMFDerivAt.2
    have hΦtd : HasFDerivAt Φt (fderiv ℝ Φt a) a :=
      (hΦt.differentiableAt one_ne_zero).hasFDerivAt
    have hΦw' : HasFDerivWithinAt Φ (fderiv ℝ Φt a) (range I3) a := by
      refine hΦtd.hasFDerivWithinAt.congr_of_eventuallyEq ?_ ?_
      · rw [range_modelWithCornersEuclideanHalfSpace]
        filter_upwards [inter_mem_nhdsWithin {z : EuclideanSpace ℝ (Fin 3) | 0 ≤ z 0}
          (Metric.isOpen_ball.mem_nhds (Metric.mem_ball_self hr1))] with z hz
        exact (hΦt_eq z hz.2 hz.1).symm
      · exact (hΦt_eq a (Metric.mem_ball_self hr1) (by simp [ha0])).symm
    have hamem : a ∈ range I3 := by
      rw [range_modelWithCornersEuclideanHalfSpace]; simp [ha0]
    have heqD : fderiv ℝ Φt a = mfderiv I3 I3 i x₀ :=
      (I3.uniqueDiffOn a hamem).eq hΦw' hΦw
    have hΦtd' : HasFDerivAt Φt (mfderiv I3 I3 i x₀) (α (a, 0)) := by
      rw [hαa, ← heqD]; exact hΦtd
    have := hΦtd'.comp (a, 0) hαD
    rw [hva] at this
    exact this
  · intro z hz hz0
    have hcurve := hαcurve z hz hz0
    have hzero : (0 : ℝ) ∈ uIcc 0 (σ * ε) := left_mem_uIcc
    have hzG : α (z, 0) ∈ G := (hcurve 0 hzero).2.1
    rw [hα0 z hz] at hzG
    refine ⟨hzG.1.2, fun t => e.symm (α (z, t)), by simp only [hα0 z hz], ?_, ?_⟩
    · have := sm_lift_field (I := I3) (x₀ := x₀) (X := X) (c := fun t => α (z, t))
        (s := uIcc 0 (σ * ε)) (fun t ht => (hcurve t ht).1.hasDerivWithinAt)
        (fun t ht => (hcurve t ht).2.1.1.2)
      exact this
    · intro τ hτ
      refine ⟨(hcurve τ hτ).2.1.2, ?_⟩
      show Φt (α (z, τ)) = eN (i (e.symm (α (z, τ))))
      rw [hΦt_eq _ (hcurve τ hτ).2.1.1.1 (hcurve τ hτ).2.2]
      rfl


section ChartRead

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
  {v : (x : M) → TangentSpace I x}

set_option backward.isDefEq.respectTransparency false in
/-- A manifold integral curve, read in the chart at an arbitrary base point `x₀`. -/
theorem sm_chart {γ : ℝ → M} {s : Set ℝ} {t : ℝ} {x₀ : M}
    (hγ : IsMIntegralCurveOn γ v s) (ht : t ∈ s)
    (hsrc : γ t ∈ (extChartAt I x₀).source) :
    HasDerivWithinAt ((extChartAt I x₀) ∘ γ)
      (tangentCoordChange I (γ t) x₀ (γ t) (v (γ t))) s t := by
  replace hsrc := extChartAt_source I x₀ ▸ hsrc
  rw [hasDerivWithinAt_iff_hasFDerivWithinAt, ← hasMFDerivWithinAt_iff_hasFDerivWithinAt]
  apply (HasMFDerivWithinAt.comp t (hasMFDerivWithinAt_extChartAt (I := I) hsrc) (hγ _ ht)
    (Set.subset_preimage_image _ _)).congr_mfderiv
  rw [ContinuousLinearMap.ext_iff]
  intro a
  rw [ContinuousLinearMap.comp_apply, ContinuousLinearMap.smulRight_apply, map_smul,
    ← one_apply_eq_self (F := TangentSpace 𝓘(ℝ, ℝ) t →L[ℝ] TangentSpace 𝓘(ℝ, ℝ) t) a,
    ← ContinuousLinearMap.smulRight_apply,
    mfderiv_chartAt_eq_tangentCoordChange hsrc]
  rfl

end ChartRead

set_option backward.isDefEq.respectTransparency false in
/-- The derivative of a chart map along `e` equals the chart field, when the chart map reads an
integral curve along the line `τ ↦ c0 + τ • e`. -/
theorem sm_ode
    {N : Type} [TopologicalSpace N] [ChartedSpace (EuclideanHalfSpace 3) N] [IsManifold I3 ∞ N]
    (Z : (w : N) → TangentSpace I3 w) (p : N)
    {Θ : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3)}
    {D : EuclideanSpace ℝ (Fin 3) →L[ℝ] EuclideanSpace ℝ (Fin 3)}
    {z c0 e : EuclideanSpace ℝ (Fin 3)} {τ0 : ℝ} {s : Set ℝ}
    (hD : HasFDerivAt Θ D z) (hz : c0 + τ0 • e = z) (hs : UniqueDiffWithinAt ℝ s τ0)
    (hτ0 : τ0 ∈ s) {β : ℝ → N} (hβ : IsMIntegralCurveOn β Z s)
    (hsrc : ∀ τ ∈ s, β τ ∈ (extChartAt I3 p).source)
    (hg : ∀ τ ∈ s, Θ (c0 + τ • e) = extChartAt I3 p (β τ)) :
    D e = tangentCoordChange I3 ((extChartAt I3 p).symm (Θ z)) p
      ((extChartAt I3 p).symm (Θ z)) (Z ((extChartAt I3 p).symm (Θ z))) := by
  have hline : HasDerivAt (fun τ : ℝ => c0 + τ • e) e τ0 := by
    simpa using ((hasDerivAt_id τ0).smul_const e).const_add c0
  have h1 : HasDerivAt (fun τ => Θ (c0 + τ • e)) (D e) τ0 := by
    have hD' : HasFDerivAt Θ D (c0 + τ0 • e) := by rw [hz]; exact hD
    exact hD'.comp_hasDerivAt τ0 hline
  have h2 := sm_chart (x₀ := p) hβ hτ0 (hsrc τ0 hτ0)
  have h2' : HasDerivWithinAt (fun τ => Θ (c0 + τ • e))
      (tangentCoordChange I3 (β τ0) p (β τ0) (Z (β τ0))) s τ0 :=
    h2.congr (fun τ hτ => hg τ hτ) (hg τ0 hτ0)
  have heq := hs.eq_deriv s h1.hasDerivWithinAt h2'
  have hΘz : Θ z = extChartAt I3 p (β τ0) := by rw [← hz]; exact hg τ0 hτ0
  rw [heq, hΘz, (extChartAt I3 p).left_inv (hsrc τ0 hτ0)]

theorem sm_P_e0 : sm_P (EuclideanSpace.single (0 : Fin 3) (1 : ℝ)) = 0 := by
  ext i; fin_cases i <;> simp [sm_P, sm_L_apply]

/-- Two maps that agree on the hyperplane near `z` and whose derivatives agree on `e₀` have
the same derivative at `z`. -/
theorem sm_fderiv_eq_of_hyp {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {f g : EuclideanSpace ℝ (Fin 3) → F} {Df Dg : EuclideanSpace ℝ (Fin 3) →L[ℝ] F}
    {z : EuclideanSpace ℝ (Fin 3)} (hf : HasFDerivAt f Df z) (hg : HasFDerivAt g Dg z)
    (hz : z 0 = 0) (hfg : ∀ᶠ w in 𝓝 z, w 0 = 0 → f w = g w)
    (he : Df (EuclideanSpace.single (0 : Fin 3) (1 : ℝ)) =
      Dg (EuclideanSpace.single (0 : Fin 3) (1 : ℝ))) : Df = Dg := by
  have htan : ∀ h : EuclideanSpace ℝ (Fin 3), h 0 = 0 → Df h = Dg h := by
    intro h hh
    have hline : HasDerivAt (fun t : ℝ => z + t • h) h 0 := by
      simpa using ((hasDerivAt_id (0 : ℝ)).smul_const h).const_add z
    have hz' : z + (0 : ℝ) • h = z := by simp
    have h1 : HasDerivAt (fun t : ℝ => f (z + t • h)) (Df h) 0 := by
      have : HasFDerivAt f Df (z + (0 : ℝ) • h) := by rw [hz']; exact hf
      exact this.comp_hasDerivAt 0 hline
    have h2 : HasDerivAt (fun t : ℝ => g (z + t • h)) (Dg h) 0 := by
      have : HasFDerivAt g Dg (z + (0 : ℝ) • h) := by rw [hz']; exact hg
      exact this.comp_hasDerivAt 0 hline
    have hev : (fun t : ℝ => g (z + t • h)) =ᶠ[𝓝 (0 : ℝ)] (fun t : ℝ => f (z + t • h)) := by
      have hc : Filter.Tendsto (fun t : ℝ => z + t • h) (𝓝 0) (𝓝 z) := by
        have := hline.continuousAt.tendsto
        simpa using this
      filter_upwards [hc.eventually hfg] with t ht
      exact (ht (by simp [hz, hh])).symm
    exact h1.unique (h2.congr_of_eventuallyEq hev.symm)
  ext1 h
  rw [sm_decomp h, map_add, map_add, map_smul, map_smul, he,
    htan _ (sm_P_apply0 h)]

/-- Injectivity of the derivative of the flow box at the base point. -/
theorem sm_inj (D : EuclideanSpace ℝ (Fin 3) →L[ℝ] EuclideanSpace ℝ (Fin 3))
    (hD : Function.Injective D) (v : EuclideanSpace ℝ (Fin 3)) (hv : v 0 ≠ 0) :
    Function.Injective (D.comp (sm_P + (EuclideanSpace.proj (0 : Fin 3)).smulRight v)) := by
  suffices hker : ∀ h, (D.comp (sm_P + (EuclideanSpace.proj (0 : Fin 3)).smulRight v)) h = 0 →
      h = 0 by
    intro x y hxy
    have := hker (x - y) (by rw [map_sub, hxy, sub_self])
    exact sub_eq_zero.1 this
  intro h hh
  have h1 : D (sm_P h + h 0 • v) = D 0 := by
    rw [map_zero]; simpa using hh
  have h2 := hD h1
  have h3 : h 0 * v 0 = 0 := by
    have := congrArg (fun w : EuclideanSpace ℝ (Fin 3) => w 0) h2
    simpa [sm_P_apply0] using this
  have h4 : h 0 = 0 := by
    rcases mul_eq_zero.1 h3 with h5 | h5
    · exact h5
    · exact absurd h5 hv
  rw [h4, zero_smul, add_zero] at h2
  rw [sm_decomp h, h2, h4, zero_smul, add_zero]


local notation "E3" => EuclideanSpace ℝ (Fin 3)

theorem sm_line (z : EuclideanSpace ℝ (Fin 3)) (τ : ℝ) :
    sm_P (sm_P z + τ • EuclideanSpace.single (0 : Fin 3) (1 : ℝ)) = sm_P z ∧
    (sm_P z + τ • EuclideanSpace.single (0 : Fin 3) (1 : ℝ)) 0 = τ := by
  constructor
  · rw [map_add, map_smul, sm_P_P, sm_P_e0, smul_zero, add_zero]
  · simp [sm_P_apply0]

set_option backward.isDefEq.respectTransparency false in
theorem solution
    {U : Type} [TopologicalSpace U] [ChartedSpace (EuclideanHalfSpace 3) U]
    [IsManifold I3 ∞ U] [T2Space U] [CompactSpace U]
    {V : Type} [TopologicalSpace V] [ChartedSpace (EuclideanHalfSpace 3) V]
    [IsManifold I3 ∞ V] [T2Space V] [CompactSpace V]
    {W : Type} [TopologicalSpace W] [ChartedSpace (EuclideanHalfSpace 3) W]
    [IsManifold I3 ∞ W] [T2Space W] [CompactSpace W]
    (X : (x : U) → TangentSpace I3 x) (Y : (y : V) → TangentSpace I3 y)
    (hX : IsPlug X) (hY : IsPlug Y)
    (Tout : Set U) (Tin : Set V) (hTout : IsUnionOfComponents Tout (outBoundary X))
    (hTin : IsUnionOfComponents Tin (inBoundary Y)) (φ : U → V)
    (hφ : IsBoundaryDiffeo φ Tout Tin)
    (Z : (w : W) → TangentSpace I3 w) (iU : U → W) (iV : V → W)
    (hglue : IsPlugGluing X Y Tout φ Z iU iV) :
    ∀ x ∈ Tout, I3.IsInteriorPoint (iU x) →
      ∃ ε > (0 : ℝ), ∃ O : Set W, IsOpen O ∧ iU x ∈ O ∧ ∀ h : ℝ, |h| ≤ ε → ∃ f : W → W,
        ContMDiffOn I3 I3 1 f O ∧
        ∀ y ∈ O, ∃ η : ℝ → W, η 0 = y ∧ IsMIntegralCurveOn η Z (uIcc 0 h) ∧ η h = f y := by
  classical
  intro x hx hint
  obtain ⟨hcU, hcV, -, -, hdU, -, -, hseam, hZU, hZV⟩ := hglue
  have hxout : x ∈ outBoundary X := hTout.1 hx
  have hy0 : φ x ∈ Tin := hφ.1.mapsTo hx
  have hy0in : φ x ∈ inBoundary Y := hTin.1 hy0
  have hp : iV (φ x) = iU x := ((hseam x (φ x)).2 ⟨hx, rfl⟩).symm
  have hXneg : normalCoord (X x) < 0 := hxout.2
  obtain ⟨KU, εU, hεU, ρU, hρU, hKUc, hKUd, hKU⟩ :=
    sm_piece X hX.1 iU hcU x hxout.1 (σ := -1) (Or.inr rfl) (by linarith)
  obtain ⟨KV, εV, hεV, ρV, hρV, hKVc, -, hKV⟩ :=
    sm_piece Y hY.1 iV hcV (φ x) hy0in.1 (σ := 1) (Or.inl rfl) (by linarith [hy0in.2])
  rw [hp] at hKV
  rw [neg_one_mul, uIcc_of_ge (by linarith)] at hKU
  rw [one_mul, uIcc_of_le hεV.le] at hKV
  set eU := extChartAt I3 x with heU
  set a := eU x with ha
  set eV := extChartAt I3 (φ x) with heV
  set b := eV (φ x) with hb
  set p := iU x with hpdef
  set eW := extChartAt I3 p with heW
  set e0 : EuclideanSpace ℝ (Fin 3) := EuclideanSpace.single (0 : Fin 3) (1 : ℝ) with he0
  have hxsrc : x ∈ eU.source := mem_extChartAt_source (I := I3) x
  have ha0 : a 0 = 0 := (sm_boundary_iff x hxsrc).1 hxout.1
  have hPa : sm_P a = a := sm_P_of a ha0
  have hatgt : a ∈ eU.target := eU.map_source hxsrc
  -- M4
  obtain ⟨r0, hr0, hr0T⟩ := sm_tout X hX.1 Tout hTout x hx
  -- the boundary map in charts
  set ψ : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3) :=
    writtenInExtChartAt I3 I3 x φ with hψdef
  have hψa : ψ (sm_P a) = b := by
    rw [hPa]
    show eV (φ (eU.symm a)) = b
    rw [ha, eU.left_inv hxsrc]
  have hψ : ContDiffAt ℝ 1 (fun z => ψ (sm_P z)) a := by
    have h1 := ((contMDiffWithinAt_iff.1 (hφ.2.1 x hx)).2)
    have h2 : ContDiffWithinAt ℝ 1 ψ (Metric.ball a r0 ∩ {z | z 0 = 0}) a := by
      refine h1.mono ?_
      intro z hz
      obtain ⟨hzt, hzT⟩ := hr0T z hz.1 hz.2
      exact ⟨hzT, extChartAt_target_subset_range (I := I3) x hzt⟩
    have h3 : ContDiffWithinAt ℝ 1 (fun z => ψ (sm_P z)) (sm_P ⁻¹' Metric.ball a r0) a := by
      have h2' : ContDiffWithinAt ℝ 1 ψ (Metric.ball a r0 ∩ {z | z 0 = 0}) (sm_P a) := by
        rw [hPa]; exact h2
      exact h2'.comp a sm_P.contDiff.contDiffWithinAt
        (fun z hz => ⟨hz, sm_P_apply0 z⟩)
    refine h3.contDiffAt ?_
    refine sm_P.continuous.continuousAt.preimage_mem_nhds ?_
    rw [hPa]; exact Metric.ball_mem_nhds a hr0
  -- the two pieces of the flow box
  set ΘU : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3) :=
    fun z => KU (sm_P z, z 0) with hΘUdef
  set ΘV : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3) :=
    fun z => KV (ψ (sm_P z), z 0) with hΘVdef
  have hproj : ContDiff ℝ 1 (fun z : EuclideanSpace ℝ (Fin 3) => z 0) := by
    have := (EuclideanSpace.proj (0 : Fin 3) : EuclideanSpace ℝ (Fin 3) →L[ℝ] ℝ).contDiff (n := 1)
    exact this
  have hinner : ContDiffAt ℝ 1 (fun z : EuclideanSpace ℝ (Fin 3) => (sm_P z, z 0)) a :=
    sm_P.contDiff.contDiffAt.prodMk hproj.contDiffAt
  have hΘUa : ContDiffAt ℝ 1 ΘU a := by
    have : ContDiffAt ℝ 1 KU (sm_P a, a 0) := by rw [hPa, ha0]; exact hKUc
    exact this.comp a hinner
  have hΘVa : ContDiffAt ℝ 1 ΘV a := by
    have : ContDiffAt ℝ 1 KV (ψ (sm_P a), a 0) := by rw [hψa, ha0]; exact hKVc
    exact this.comp a (hψ.prodMk hproj.contDiffAt)
  -- continuity of `φ` within `Tout` at `x`, read through the chart
  obtain ⟨Oφ, hOφo, hxOφ, hOφ⟩ : ∃ Oφ : Set U, IsOpen Oφ ∧ x ∈ Oφ ∧ Oφ ∩ Tout ⊆ φ ⁻¹' eV.source := by
    have hc := (hφ.2.1 x hx).continuousWithinAt
    have := hc.preimage_mem_nhdsWithin (extChartAt_source_mem_nhds (I := I3) (φ x))
    rcases mem_nhdsWithin.1 this with ⟨O', hO', hxO', hsub⟩
    exact ⟨O', hO', hxO', hsub⟩
  have hsymmc : ContinuousAt (fun z => eU.symm (sm_P z)) a := by
    have h1 : ContinuousAt eU.symm (sm_P a) := by
      rw [hPa]; exact continuousAt_extChartAt_symm'' hatgt
    exact h1.comp sm_P.continuous.continuousAt
  -- all conditions near `a`
  have hev : ∀ᶠ z in 𝓝 a, ContDiffAt ℝ 1 ΘU z ∧ ContDiffAt ℝ 1 ΘV z ∧
      sm_P z ∈ Metric.ball a ρU ∧ sm_P z ∈ Metric.ball a r0 ∧
      ψ (sm_P z) ∈ Metric.ball b ρV ∧ (-εU < z 0 ∧ z 0 < εV) ∧ eU.symm (sm_P z) ∈ Oφ := by
    refine (hΘUa.eventually (by simp)).and ((hΘVa.eventually (by simp)).and ?_)
    refine Filter.Eventually.and ?_ (Filter.Eventually.and ?_ (Filter.Eventually.and ?_
      (Filter.Eventually.and ?_ ?_)))
    · refine sm_P.continuous.continuousAt.preimage_mem_nhds ?_
      rw [hPa]; exact Metric.ball_mem_nhds a hρU
    · refine sm_P.continuous.continuousAt.preimage_mem_nhds ?_
      rw [hPa]; exact Metric.ball_mem_nhds a hr0
    · refine hψ.continuousAt.preimage_mem_nhds ?_
      show Metric.ball b ρV ∈ 𝓝 (ψ (sm_P a))
      rw [hψa]; exact Metric.ball_mem_nhds b hρV
    · have hI : Ioo (-εU) εV ∈ 𝓝 ((fun z : EuclideanSpace ℝ (Fin 3) => z 0) a) := by
        simp only [ha0]; exact Ioo_mem_nhds (by linarith) hεV
      exact hproj.continuous.continuousAt.preimage_mem_nhds hI
    · refine hsymmc.preimage_mem_nhds ?_
      show Oφ ∈ 𝓝 (eU.symm (sm_P a))
      rw [hPa, ha, eU.left_inv hxsrc]; exact hOφo.mem_nhds hxOφ
  obtain ⟨δ0, hδ0, hδ0'⟩ := Metric.eventually_nhds_iff_ball.1 hev
  have hpt : ∀ z ∈ Metric.ball a δ0, sm_P z ∈ eU.target ∧ eU.symm (sm_P z) ∈ Tout ∧
      φ (eU.symm (sm_P z)) ∈ eV.source ∧ (ψ (sm_P z)) 0 = 0 := by
    intro z hz
    obtain ⟨-, -, -, h4, -, -, h7⟩ := hδ0' z hz
    obtain ⟨ht, hT⟩ := hr0T (sm_P z) h4 (sm_P_apply0 z)
    have hsrc : φ (eU.symm (sm_P z)) ∈ eV.source := hOφ ⟨h7, hT⟩
    refine ⟨ht, hT, hsrc, ?_⟩
    have hbd : φ (eU.symm (sm_P z)) ∈ I3.boundary V := (hTin.1 (hφ.1.mapsTo hT)).1
    exact (sm_boundary_iff (φ x) hsrc).1 hbd
  have hU : ∀ z ∈ Metric.ball a δ0, ∃ γ : ℝ → U, γ 0 = eU.symm (sm_P z) ∧
      IsMIntegralCurveOn γ X (Icc (-εU) 0) ∧ ∀ τ ∈ Icc (-εU) 0, iU (γ τ) ∈ eW.source ∧
        KU (sm_P z, τ) = eW (iU (γ τ)) :=
    fun z hz => (hKU (sm_P z) (hδ0' z hz).2.2.1 (sm_P_apply0 z)).2
  have hV : ∀ z ∈ Metric.ball a δ0, ∃ γ : ℝ → V, γ 0 = eV.symm (ψ (sm_P z)) ∧
      IsMIntegralCurveOn γ Y (Icc 0 εV) ∧ ∀ τ ∈ Icc 0 εV, iV (γ τ) ∈ eW.source ∧
        KV (ψ (sm_P z), τ) = eW (iV (γ τ)) :=
    fun z hz => (hKV (ψ (sm_P z)) (hδ0' z hz).2.2.2.2.1 (hpt z hz).2.2.2).2
  have hseamval : ∀ z ∈ Metric.ball a δ0, z 0 = 0 → ΘU z = ΘV z := by
    intro z hz hz0
    obtain ⟨γ, hγ0, -, hγK⟩ := hU z hz
    obtain ⟨γ', hγ'0, -, hγ'K⟩ := hV z hz
    have h0U : (0:ℝ) ∈ Icc (-εU) 0 := ⟨by linarith, le_rfl⟩
    have h0V : (0:ℝ) ∈ Icc 0 εV := ⟨le_rfl, hεV.le⟩
    show KU (sm_P z, z 0) = KV (ψ (sm_P z), z 0)
    rw [hz0, (hγK 0 h0U).2, (hγ'K 0 h0V).2, hγ0, hγ'0]
    have hψz : eV.symm (ψ (sm_P z)) = φ (eU.symm (sm_P z)) := eV.left_inv (hpt z hz).2.2.1
    rw [hψz]
    congr 1
    exact (hseam _ _).2 ⟨(hpt z hz).2.1, rfl⟩
  set vW : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3) := fun y =>
    tangentCoordChange I3 (eW.symm y) p (eW.symm y) (Z (eW.symm y)) with hvWdef
  have hodeU : ∀ z ∈ Metric.ball a δ0, z 0 ≤ 0 → fderiv ℝ ΘU z e0 = vW (ΘU z) := by
    intro z hz hz0
    obtain ⟨γ, -, hγ, hγK⟩ := hU z hz
    have hτ : z 0 ∈ Icc (-εU) 0 := ⟨(hδ0' z hz).2.2.2.2.2.1.1.le, hz0⟩
    exact sm_ode Z p (((hδ0' z hz).1.differentiableAt one_ne_zero).hasFDerivAt)
      (sm_decomp z).symm ((uniqueDiffOn_Icc (by linarith)) _ hτ) hτ
      (sm_comp_curve X Z iU hcU hZU hγ) (fun τ hτ => (hγK τ hτ).1)
      (fun τ hτ => by
        show KU (sm_P (sm_P z + τ • e0), (sm_P z + τ • e0) 0) = _
        rw [(sm_line z τ).1, (sm_line z τ).2]; exact (hγK τ hτ).2)
  have hodeV : ∀ z ∈ Metric.ball a δ0, 0 ≤ z 0 → fderiv ℝ ΘV z e0 = vW (ΘV z) := by
    intro z hz hz0
    obtain ⟨γ, -, hγ, hγK⟩ := hV z hz
    have hτ : z 0 ∈ Icc 0 εV := ⟨hz0, (hδ0' z hz).2.2.2.2.2.1.2.le⟩
    exact sm_ode Z p (((hδ0' z hz).2.1.differentiableAt one_ne_zero).hasFDerivAt)
      (sm_decomp z).symm ((uniqueDiffOn_Icc hεV) _ hτ) hτ
      (sm_comp_curve Y Z iV hcV hZV hγ) (fun τ hτ => (hγK τ hτ).1)
      (fun τ hτ => by
        show KV (ψ (sm_P (sm_P z + τ • e0)), (sm_P z + τ • e0) 0) = _
        rw [(sm_line z τ).1, (sm_line z τ).2]; exact (hγK τ hτ).2)
  -- pasting
  set A : Set (EuclideanSpace ℝ (Fin 3)) := {z | z 0 ≤ 0} with hAdef
  set B : Set (EuclideanSpace ℝ (Fin 3)) := {z | 0 ≤ z 0} with hBdef
  have hAc : IsClosed A := isClosed_le hproj.continuous continuous_const
  have hBc : IsClosed B := isClosed_le continuous_const hproj.continuous
  have hcov : Metric.ball a δ0 ⊆ A ∪ B := fun z _ => le_total (z 0) 0
  obtain ⟨hΘD, hΘC⟩ := sm_paste (A := A) (B := B) (Ω := Metric.ball a δ0) Metric.isOpen_ball
    hAc hBc hcov (g := ΘU) (h := ΘV) (g' := fderiv ℝ ΘU) (h' := fderiv ℝ ΘV)
    (fun z hz => ((hδ0' z hz.2).1.differentiableAt one_ne_zero).hasFDerivAt.hasFDerivWithinAt)
    (fun z hz => ((hδ0' z hz.2).2.1.differentiableAt one_ne_zero).hasFDerivAt.hasFDerivWithinAt)
    (fun z hz => ((hδ0' z hz.2).1.continuousAt_fderiv one_ne_zero).continuousWithinAt)
    (fun z hz => ((hδ0' z hz.2).2.1.continuousAt_fderiv one_ne_zero).continuousWithinAt)
    (fun z hz => hseamval z hz.2 (le_antisymm hz.1.1 hz.1.2))
    (fun z hz => by
      have hz0 : z 0 = 0 := le_antisymm hz.1.1 hz.1.2
      refine sm_fderiv_eq_of_hyp (((hδ0' z hz.2).1.differentiableAt one_ne_zero).hasFDerivAt)
        (((hδ0' z hz.2).2.1.differentiableAt one_ne_zero).hasFDerivAt) hz0 ?_ ?_
      · filter_upwards [Metric.isOpen_ball.mem_nhds hz.2] with w hw hw0
        exact hseamval w hw hw0
      · rw [hodeU z hz.2 hz.1.1, hodeV z hz.2 hz.1.2, hseamval z hz.2 hz0])
  set Θ : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3) :=
    fun z => if z ∈ A then ΘU z else ΘV z with hΘdef
  have hΘode : ∀ z ∈ Metric.ball a δ0,
      (if z ∈ A then fderiv ℝ ΘU z else fderiv ℝ ΘV z) e0 = vW (Θ z) := by
    intro z hz
    by_cases hzA : z ∈ A
    · rw [if_pos hzA]
      show _ = vW (if z ∈ A then ΘU z else ΘV z)
      rw [if_pos hzA]; exact hodeU z hz hzA
    · have h0 : 0 ≤ z 0 := le_of_lt (not_le.1 hzA)
      rw [if_neg hzA]
      show _ = vW (if z ∈ A then ΘU z else ΘV z)
      rw [if_neg hzA]; exact hodeV z hz h0
  -- the derivative at `a`
  have haΩ : a ∈ Metric.ball a δ0 := Metric.mem_ball_self hδ0
  have haA : a ∈ A := le_of_eq ha0
  have hinjD : Function.Injective (fderiv ℝ ΘU a) := by
    have hKUd' := hKUd
    rw [← hPa, ← ha0] at hKUd'
    have hpr : HasFDerivAt (fun z : EuclideanSpace ℝ (Fin 3) => z 0)
        (EuclideanSpace.proj (0 : Fin 3) : EuclideanSpace ℝ (Fin 3) →L[ℝ] ℝ) a := by
      have := (EuclideanSpace.proj (0 : Fin 3) : EuclideanSpace ℝ (Fin 3) →L[ℝ] ℝ).hasFDerivAt (x := a)
      exact this
    have hin : HasFDerivAt (fun z : EuclideanSpace ℝ (Fin 3) => (sm_P z, z 0))
        (sm_P.prod (EuclideanSpace.proj (0 : Fin 3))) a :=
      sm_P.hasFDerivAt.prodMk hpr
    have hc : HasFDerivAt ΘU _ a := hKUd'.comp a hin
    rw [hc.fderiv]
    have heqL : ((mfderiv I3 I3 iU x : EuclideanSpace ℝ (Fin 3) →L[ℝ] EuclideanSpace ℝ (Fin 3)).comp
        ((ContinuousLinearMap.fst ℝ (EuclideanSpace ℝ (Fin 3)) ℝ) +
          (ContinuousLinearMap.snd ℝ (EuclideanSpace ℝ (Fin 3)) ℝ).smulRight
            (id (X x) : EuclideanSpace ℝ (Fin 3)))).comp
        (sm_P.prod (EuclideanSpace.proj (0 : Fin 3))) =
        (mfderiv I3 I3 iU x : EuclideanSpace ℝ (Fin 3) →L[ℝ] EuclideanSpace ℝ (Fin 3)).comp
          (sm_P + (EuclideanSpace.proj (0 : Fin 3)).smulRight
            (id (X x) : EuclideanSpace ℝ (Fin 3))) := by
      ext1 h
      simp only [ContinuousLinearMap.comp_apply, add_apply,
        ContinuousLinearMap.prod_apply]
      rfl
    rw [heqL]
    exact sm_inj _ (hdU x) _ (ne_of_lt hXneg)
  -- inverse function theorem
  have hΘa : ContDiffAt ℝ 1 Θ a := hΘC.contDiffAt (Metric.isOpen_ball.mem_nhds haΩ)
  have hΘDa : HasFDerivAt Θ (fderiv ℝ ΘU a) a := by
    have := hΘD a haΩ
    rw [if_pos haA] at this
    exact this
  let De : E3 ≃L[ℝ] E3 :=
    (LinearEquiv.ofInjectiveEndo (fderiv ℝ ΘU a : E3 →ₗ[ℝ] E3) hinjD).toContinuousLinearEquiv
  have hDe : (De : E3 →L[ℝ] E3) = fderiv ℝ ΘU a := by
    ext v; simp [De, LinearEquiv.coe_ofInjectiveEndo]
  have hΘDa' : HasFDerivAt Θ (De : E3 →L[ℝ] E3) a := by rw [hDe]; exact hΘDa
  set Θh := hΘa.toOpenPartialHomeomorph Θ hΘDa' one_ne_zero with hΘh
  have hΘhcoe : (Θh : E3 → E3) = Θ := rfl
  have haS : a ∈ Θh.source := hΘa.mem_toOpenPartialHomeomorph_source hΘDa' one_ne_zero
  have hΘaq : Θ a = eW p := by
    obtain ⟨γ, hγ0, -, hγK⟩ := hU a haΩ
    show (if a ∈ A then ΘU a else ΘV a) = eW p
    rw [if_pos haA]
    show KU (sm_P a, a 0) = eW p
    rw [ha0, (hγK 0 ⟨by linarith, le_rfl⟩).2, hγ0, hPa, ha, eU.left_inv hxsrc]
  have hqint : eW p ∈ interior eW.target := (I3.isInteriorPoint_iff).1 hint
  have hfdΘ : ∀ z ∈ Metric.ball a δ0,
      fderiv ℝ Θ z = (if z ∈ A then fderiv ℝ ΘU z else fderiv ℝ ΘV z) :=
    fun z hz => (hΘD z hz).fderiv
  have hinv : ∀ᶠ z in 𝓝 a, ∃ e : E3 ≃L[ℝ] E3, (e : E3 →L[ℝ] E3) = fderiv ℝ Θ z := by
    have hcont := hΘa.continuousAt_fderiv one_ne_zero
    have hmem : range ((↑) : (E3 ≃L[ℝ] E3) → E3 →L[ℝ] E3) ∈ 𝓝 (fderiv ℝ Θ a) := by
      refine ContinuousLinearEquiv.isOpen.mem_nhds ⟨De, ?_⟩
      rw [hDe, hfdΘ a haΩ, if_pos haA]
    exact hcont.preimage_mem_nhds hmem
  have hev2 : ∀ᶠ z in 𝓝 a, z ∈ Θh.source ∧
      (∃ e : E3 ≃L[ℝ] E3, (e : E3 →L[ℝ] E3) = fderiv ℝ Θ z) ∧
      Θ z ∈ interior eW.target ∧ z ∈ Metric.ball a δ0 := by
    refine Filter.Eventually.and (Θh.open_source.mem_nhds haS) (hinv.and (Filter.Eventually.and ?_
      (Metric.isOpen_ball.mem_nhds haΩ)))
    refine hΘa.continuousAt.preimage_mem_nhds ?_
    rw [hΘaq]; exact isOpen_interior.mem_nhds hqint
  obtain ⟨δ1, hδ1, hδ1'⟩ := Metric.eventually_nhds_iff_ball.1 hev2
  set δ := δ1 / 2 with hδdef
  have hδ : 0 < δ := by positivity
  set Oc := Θh.target ∩ Θh.symm ⁻¹' Metric.ball a δ with hOcdef
  have hOco : IsOpen Oc := Θh.isOpen_inter_preimage_symm Metric.isOpen_ball
  set O := eW.source ∩ eW ⁻¹' Oc with hOdef
  have hOo : IsOpen O := isOpen_extChartAt_preimage' p hOco
  have hpO : p ∈ O := by
    refine ⟨mem_extChartAt_source (I := I3) p, ?_, ?_⟩
    · show eW p ∈ Θh.target
      rw [← hΘaq]; exact Θh.map_source haS
    · show Θh.symm (eW p) ∈ Metric.ball a δ
      rw [← hΘaq]
      have : Θh.symm (Θh a) = a := Θh.left_inv haS
      rw [hΘhcoe] at this
      rw [this]; exact Metric.mem_ball_self hδ
  have hshift : ∀ w ∈ Metric.ball a δ, ∀ r : ℝ, |r| ≤ δ → w + r • e0 ∈ Metric.ball a δ1 := by
    intro w hw r hr
    rw [Metric.mem_ball, dist_eq_norm] at hw ⊢
    have : w + r • e0 - a = (w - a) + r • e0 := by abel
    rw [this]
    calc ‖(w - a) + r • e0‖ ≤ ‖w - a‖ + ‖r • e0‖ := norm_add_le _ _
      _ = ‖w - a‖ + |r| := by rw [norm_smul, he0, PiLp.norm_single]; simp
      _ < δ + δ := by linarith
      _ = δ1 := by rw [hδdef]; ring
  refine ⟨δ, hδ, O, hOo, hpO, fun h hh => ?_⟩
  set G : E3 → E3 := fun u => Θ (Θh.symm u + h • e0) with hGdef
  have hGc : ContDiffOn ℝ 1 G Oc := by
    intro u hu
    have hw : Θh.symm u ∈ Metric.ball a δ := hu.2
    have hw1 : Θh.symm u ∈ Metric.ball a δ1 := Metric.ball_subset_ball (by linarith) hw
    obtain ⟨-, ⟨e, he⟩, -, hwΩ⟩ := hδ1' _ hw1
    have hsymm : ContDiffAt ℝ 1 Θh.symm u := by
      refine Θh.contDiffAt_symm hu.1 (f₀' := e) ?_ ?_
      · rw [he]
        exact ((hΘC.contDiffAt (Metric.isOpen_ball.mem_nhds hwΩ)).differentiableAt
          one_ne_zero).hasFDerivAt
      · exact hΘC.contDiffAt (Metric.isOpen_ball.mem_nhds hwΩ)
    have hsh := hδ1' _ (hshift _ hw h hh)
    have hΘc : ContDiffAt ℝ 1 Θ (Θh.symm u + h • e0) :=
      hΘC.contDiffAt (Metric.isOpen_ball.mem_nhds hsh.2.2.2)
    exact (hΘc.comp u (hsymm.add contDiffAt_const)).contDiffWithinAt
  refine ⟨eW.symm ∘ (G ∘ eW), ?_, ?_⟩
  · have h1 : ContMDiffOn I3 𝓘(ℝ, E3) 1 eW O := by
      refine (contMDiffOn_extChartAt (x := p)).mono ?_
      intro y hy; rw [← extChartAt_source I3]; exact hy.1
    have h2 : ContMDiffOn 𝓘(ℝ, E3) 𝓘(ℝ, E3) 1 G Oc := hGc.contMDiffOn
    have h3 : ContMDiffOn 𝓘(ℝ, E3) I3 1 eW.symm eW.target := contMDiffOn_extChartAt_symm p
    refine h3.comp (h2.comp h1 (fun y hy => hy.2)) ?_
    intro y hy
    exact interior_subset (s := eW.target) (hδ1' _ (hshift _ hy.2.2 h hh)).2.2.1
  · intro y hy
    set w := Θh.symm (eW y) with hwdef
    have hw : w ∈ Metric.ball a δ := hy.2.2
    refine ⟨fun r => eW.symm (Θ (w + r • e0)), ?_, ?_, rfl⟩
    · show eW.symm (Θ (w + (0:ℝ) • e0)) = y
      rw [zero_smul, add_zero]
      have : Θh (Θh.symm (eW y)) = eW y := Θh.right_inv hy.2.1
      rw [hΘhcoe] at this
      rw [hwdef, this, eW.left_inv hy.1]
    · have hr : ∀ r ∈ uIcc 0 h, |r| ≤ δ := by
        intro r hr
        rcases le_total 0 h with h0 | h0
        · rw [uIcc_of_le h0] at hr; rw [abs_le] at hh ⊢; constructor <;> linarith [hr.1, hr.2]
        · rw [uIcc_of_ge h0] at hr; rw [abs_le] at hh ⊢; constructor <;> linarith [hr.1, hr.2]
      apply sm_lift_field (I := I3) (x₀ := p) (X := Z) (c := fun r => Θ (w + r • e0))
        (s := uIcc 0 h)
      · intro r hrs
        have hm := hδ1' _ (hshift _ hw r (hr r hrs))
        have hline : HasDerivAt (fun r : ℝ => w + r • e0) e0 r := by
          simpa using ((hasDerivAt_id r).smul_const e0).const_add w
        have hd := (hΘD _ hm.2.2.2).comp_hasDerivAt r hline
        rw [hΘode _ hm.2.2.2] at hd
        exact hd.hasDerivWithinAt
      · intro r hrs
        exact interior_subset (s := eW.target) (hδ1' _ (hshift _ hw r (hr r hrs))).2.2.1
