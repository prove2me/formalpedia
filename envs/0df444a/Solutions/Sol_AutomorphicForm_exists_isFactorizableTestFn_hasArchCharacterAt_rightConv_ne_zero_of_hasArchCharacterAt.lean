-- Prove2me | solution 1 for AutomorphicForm.exists_isFactorizableTestFn_hasArchCharacterAt_rightConv_ne_zero_of_hasArchCharacterAt
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.961684+00:00
-- url     : https://prove2.me/submissions/4ad10b58-bc0c-57e7-bba7-61d6c04c7068

import Definitions.Def_AutomorphicForm_RightConvolution
import Definitions.Def_AutomorphicForm_FactorizableTestFn
import Definitions.Def_AutomorphicForm_SmoothAutomorphicFnAt
import Definitions.Def_AutomorphicForm_ArchType
import Theorems.Thm_AutomorphicForm_continuous_and_hasCompactSupport_of_isFactorizableTestFn
import Definitions.Def_AutomorphicForm_ArchWeightCharTransport
import Theorems.Thm_NumberField_AdelicHaar_isMulRightInvariant_adelicGLHaar
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_exists_isFactorizableTestFn_hasArchCharacterAt_rightConv_ne_zero_of_hasArchCharacterAt

open NumberField NumberField.AdelicLevel
open NumberField.InfinitePlace NumberField.InfinitePlace.Completion IsDedekindDomain
p2m_open "NumberField.InfiniteAdeleRing AutomorphicForm Metric Topology MeasureTheory"

open scoped Classical

noncomputable section

namespace Ws1
namespace H2K
namespace Scaffold

variable (F : Type) [Field F] [NumberField F]

abbrev E : Type := Fin 2 → Fin 2 → mixedEmbedding.mixedSpace F

def ofE (m : E F) : Matrix (Fin 2) (Fin 2) (mixedEmbedding.mixedSpace F) := m

omit [NumberField F] in
theorem continuous_ringEquiv_mixedSpace : Continuous (ringEquiv_mixedSpace F) := by
  refine continuous_prodMk.2 ⟨continuous_pi fun v => ?_, continuous_pi fun v => ?_⟩
  · exact (isometry_extensionEmbeddingOfIsReal v.2).continuous.comp (continuous_apply _)
  · exact (isometry_extensionEmbedding v.1).continuous.comp (continuous_apply _)

omit [NumberField F] in
theorem continuous_ringEquiv_mixedSpace_symm : Continuous (ringEquiv_mixedSpace F).symm := by
  apply continuous_pi
  intro v
  by_cases hv : IsReal v
  · have key : (fun y : mixedEmbedding.mixedSpace F => (ringEquiv_mixedSpace F).symm y v)
        = fun y => (isometryEquivRealOfIsReal hv).symm (y.1 ⟨v, hv⟩) := by
      funext y
      apply (isometryEquivRealOfIsReal hv).injective
      rw [IsometryEquiv.apply_symm_apply]
      have h := congrArg (fun z : mixedEmbedding.mixedSpace F => z.1 ⟨v, hv⟩)
        ((ringEquiv_mixedSpace F).apply_symm_apply y)
      exact h
    rw [key]
    exact (isometryEquivRealOfIsReal hv).symm.continuous.comp
      ((continuous_apply _).comp continuous_fst)
  · have hc : IsComplex v := not_isReal_iff_isComplex.1 hv
    have key : (fun y : mixedEmbedding.mixedSpace F => (ringEquiv_mixedSpace F).symm y v)
        = fun y => (isometryEquivComplexOfIsComplex hc).symm (y.2 ⟨v, hc⟩) := by
      funext y
      apply (isometryEquivComplexOfIsComplex hc).injective
      rw [IsometryEquiv.apply_symm_apply]
      have h := congrArg (fun z : mixedEmbedding.mixedSpace F => z.2 ⟨v, hc⟩)
        ((ringEquiv_mixedSpace F).apply_symm_apply y)
      exact h
    rw [key]
    exact (isometryEquivComplexOfIsComplex hc).symm.continuous.comp
      ((continuous_apply _).comp continuous_snd)

def mixedHomeo : InfiniteAdeleRing F ≃ₜ mixedEmbedding.mixedSpace F where
  toEquiv := (ringEquiv_mixedSpace F).toEquiv
  continuous_toFun := continuous_ringEquiv_mixedSpace F
  continuous_invFun := continuous_ringEquiv_mixedSpace_symm F

def matHomeo : (Fin 2 → Fin 2 → InfiniteAdeleRing F) ≃ₜ E F :=
  Homeomorph.piCongrRight fun _ => Homeomorph.piCongrRight fun _ => mixedHomeo F

def pairHomeo :
    (Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing F) × (Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing F))ᵐᵒᵖ)
      ≃ₜ (E F × E F) :=
  Homeomorph.prodCongr (matHomeo F) (MulOpposite.opHomeomorph.symm.trans (matHomeo F))

def J (g : GL (Fin 2) (InfiniteAdeleRing F)) : E F × E F :=
  pairHomeo F (Units.embedProduct _ g)

omit [NumberField F] in
theorem J_apply (g : GL (Fin 2) (InfiniteAdeleRing F)) :
    J F g = (archEntries F g, archEntries F g⁻¹) := rfl

omit [NumberField F] in
theorem isClosedEmbedding_J : IsClosedEmbedding (J F) :=
  (pairHomeo F).isClosedEmbedding.comp Units.isClosedEmbedding_embedProduct

def cE : E F := archEntries F 1

omit [NumberField F] in
theorem ofE_archEntries (g : GL (Fin 2) (InfiniteAdeleRing F)) :
    ofE F (archEntries F g)
      = (ringEquiv_mixedSpace F).toRingHom.mapMatrix (g : Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing F)) := by
  funext i j
  rfl

omit [NumberField F] in
theorem continuous_detE : Continuous fun m : E F => (ofE F m).det :=
  Continuous.matrix_det continuous_id

theorem isOpen_detUnit : IsOpen {m : E F | IsUnit (ofE F m).det} :=
  Units.isOpen.preimage (continuous_detE F)

omit [NumberField F] in
theorem det_cE : (ofE F (cE F)).det = 1 := by
  rw [cE, ofE_archEntries, ← RingHom.map_det, Units.val_one, Matrix.det_one, map_one]

theorem exists_ball_subset_detUnit :
    ∃ ε > 0, ball (cE F) ε ⊆ {m : E F | IsUnit (ofE F m).det} :=
  Metric.isOpen_iff.1 (isOpen_detUnit F) (cE F) (by simp [det_cE])

def ε : ℝ := Classical.choose (exists_ball_subset_detUnit F)

theorem ε_pos : 0 < ε F := (Classical.choose_spec (exists_ball_subset_detUnit F)).1

theorem ball_ε_subset : ball (cE F) (ε F) ⊆ {m : E F | IsUnit (ofE F m).det} :=
  (Classical.choose_spec (exists_ball_subset_detUnit F)).2

def Ψ (m : E F) : E F := fun i j => (Ring.inverse (ofE F m).det • (ofE F m).adjugate) i j

theorem continuousOn_Ψ : ContinuousOn (Ψ F) (closedBall (cE F) (ε F / 2)) := by
  intro m hm
  have hunit : IsUnit (ofE F m).det :=
    ball_ε_subset F (closedBall_subset_ball (by linarith [ε_pos F]) hm)
  obtain ⟨u, hu⟩ := hunit
  apply ContinuousAt.continuousWithinAt
  have h1 : ContinuousAt (fun m : E F => Ring.inverse (ofE F m).det) m := by
    have hi : ContinuousAt Ring.inverse (ofE F m).det := hu ▸ NormedRing.inverse_continuousAt u
    exact hi.comp (continuous_detE F).continuousAt
  have h2 : Continuous fun m : E F => (ofE F m).adjugate := Continuous.matrix_adjugate continuous_id
  have h3 : ContinuousAt (fun m : E F =>
      (Ring.inverse (ofE F m).det • (ofE F m).adjugate :
        Matrix (Fin 2) (Fin 2) (mixedEmbedding.mixedSpace F))) m :=
    h1.smul h2.continuousAt
  exact h3

theorem exists_R : ∃ R > 0, Ψ F '' closedBall (cE F) (ε F / 2) ⊆ closedBall (cE F) R := by
  have hc : IsCompact (Ψ F '' closedBall (cE F) (ε F / 2)) :=
    (isCompact_closedBall _ _).image_of_continuousOn (continuousOn_Ψ F)
  obtain ⟨R, hR⟩ := hc.isBounded.subset_closedBall (cE F)
  exact ⟨max R 1, by positivity, hR.trans (closedBall_subset_closedBall (le_max_left _ _))⟩

def R : ℝ := Classical.choose (exists_R F)

theorem R_pos : 0 < R F := (Classical.choose_spec (exists_R F)).1

theorem Ψ_subset : Ψ F '' closedBall (cE F) (ε F / 2) ⊆ closedBall (cE F) (R F) :=
  (Classical.choose_spec (exists_R F)).2

def bump₂ : ContDiffBump (cE F) where
  rIn := R F
  rOut := R F + 1
  rIn_pos := R_pos F
  rIn_lt_rOut := by linarith

theorem archEntries_inv_mem (g : GL (Fin 2) (InfiniteAdeleRing F))
    (hg : archEntries F g ∈ closedBall (cE F) (ε F / 2)) :
    archEntries F g⁻¹ ∈ closedBall (cE F) (R F) := by
  apply Ψ_subset F
  refine ⟨archEntries F g, hg, ?_⟩

  set A := (ringEquiv_mixedSpace F).toRingHom.mapMatrix
    (g : Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing F)) with hA
  have hAinv : (ringEquiv_mixedSpace F).toRingHom.mapMatrix
      ((g⁻¹ : GL (Fin 2) (InfiniteAdeleRing F)) : Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing F)) = A⁻¹ := by
    symm
    apply Matrix.inv_eq_left_inv
    rw [hA, ← map_mul, Units.inv_mul, map_one]
  funext i j
  show (Ring.inverse (ofE F (archEntries F g)).det • (ofE F (archEntries F g)).adjugate) i j
    = archEntries F g⁻¹ i j
  have h2 : archEntries F g⁻¹ i j = (ofE F (archEntries F g⁻¹)) i j := rfl
  rw [h2, ofE_archEntries, ofE_archEntries, hAinv, Matrix.inv_def]

omit [NumberField F] in
theorem Ψ_archEntries (g : GL (Fin 2) (InfiniteAdeleRing F)) :
    Ψ F (archEntries F g) = archEntries F g⁻¹ := by
  set A := (ringEquiv_mixedSpace F).toRingHom.mapMatrix
    (g : Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing F)) with hA
  have hAinv : (ringEquiv_mixedSpace F).toRingHom.mapMatrix
      ((g⁻¹ : GL (Fin 2) (InfiniteAdeleRing F)) : Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing F)) = A⁻¹ := by
    symm
    apply Matrix.inv_eq_left_inv
    rw [hA, ← map_mul, Units.inv_mul, map_one]
  funext i j
  show (Ring.inverse (ofE F (archEntries F g)).det • (ofE F (archEntries F g)).adjugate) i j
    = archEntries F g⁻¹ i j
  have h2 : archEntries F g⁻¹ i j = (ofE F (archEntries F g⁻¹)) i j := rfl
  rw [h2, ofE_archEntries, ofE_archEntries, hAinv, Matrix.inv_def]

theorem continuousAt_Ψ : ContinuousAt (Ψ F) (cE F) :=
  (continuousOn_Ψ F).continuousAt (closedBall_mem_nhds _ (half_pos (ε_pos F)))

theorem exists_radius {T : Set (GL (Fin 2) (InfiniteAdeleRing F))}
    (hT : T ∈ 𝓝 (1 : GL (Fin 2) (InfiniteAdeleRing F))) :
    ∃ ρ : ℝ, 0 < ρ ∧ ρ ≤ ε F / 2 ∧ ∀ g, dist (archEntries F g) (cE F) < ρ → g ∈ T := by
  have hJ : J F = (fun m : E F => (m, Ψ F m)) ∘ archEntries F := by
    funext g
    rw [Function.comp_apply, J_apply, Ψ_archEntries]
  have hJ1 : J F 1 = (cE F, Ψ F (cE F)) := by
    show J F 1 = (archEntries F 1, Ψ F (archEntries F 1))
    rw [J_apply, inv_one, Ψ_archEntries F 1, inv_one]
  have hcont : ContinuousAt (fun m : E F => (m, Ψ F m)) (cE F) :=
    continuousAt_id.prodMk (continuousAt_Ψ F)
  have h1 : Filter.Tendsto (fun m : E F => (m, Ψ F m)) (𝓝 (cE F)) (𝓝 (J F 1)) := by
    rw [hJ1]
    exact hcont
  have hle : Filter.comap (archEntries F) (𝓝 (cE F)) ≤ 𝓝 (1 : GL (Fin 2) (InfiniteAdeleRing F)) :=
    calc Filter.comap (archEntries F) (𝓝 (cE F))
        ≤ Filter.comap (archEntries F)
            (Filter.comap (fun m : E F => (m, Ψ F m)) (𝓝 (J F 1))) :=
          Filter.comap_mono (Filter.tendsto_iff_comap.1 h1)
      _ = Filter.comap (J F) (𝓝 (J F 1)) := by rw [Filter.comap_comap, hJ]
      _ = 𝓝 1 := ((isClosedEmbedding_J F).isInducing.nhds_eq_comap 1).symm
  obtain ⟨S, hS, hST⟩ := Filter.mem_comap.1 (hle hT)
  obtain ⟨δ, hδ, hδS⟩ := Metric.mem_nhds_iff.1 hS
  refine ⟨min δ (ε F / 2), lt_min hδ (half_pos (ε_pos F)), min_le_right _ _, fun g hg => ?_⟩
  exact hST (show g ∈ archEntries F ⁻¹' S from
    hδS (Metric.mem_ball.2 (lt_of_lt_of_le hg (min_le_left _ _))))

theorem continuous_adelicArchGLIncl : Continuous (adelicArchGLIncl F) := by
  refine Units.continuous_iff.2 ⟨?_, ?_⟩
  · refine continuous_matrix fun i j => ?_
    show Continuous fun k : GL (Fin 2) (InfiniteAdeleRing F) =>
      (((k : Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing F)) i j,
        (1 : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 F) F)) i j) : AdeleRing (𝓞 F) F)
    exact (Units.continuous_val.matrix_elem i j).prodMk continuous_const
  · refine continuous_matrix fun i j => ?_
    show Continuous fun k : GL (Fin 2) (InfiniteAdeleRing F) =>
      ((((k⁻¹ : GL (Fin 2) (InfiniteAdeleRing F)) : Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing F)) i j,
        (1 : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 F) F)) i j) : AdeleRing (𝓞 F) F)
    exact (Units.continuous_coe_inv.matrix_elem i j).prodMk continuous_const

theorem exists_radius_of_continuous (φ : AdelicGL2 (𝓞 F) F → ℂ) (hφ : Continuous φ)
    (g₀ : AdelicGL2 (𝓞 F) F) (hg₀ : φ g₀ ≠ 0) :
    ∃ ρ : ℝ, 0 < ρ ∧ ρ ≤ ε F / 2 ∧ ∀ m : GL (Fin 2) (InfiniteAdeleRing F),
      dist (archEntries F m) (cE F) < ρ →
        ‖φ (g₀ * adelicArchGLIncl F m) - φ g₀‖ ≤ ‖φ g₀‖ / 2 := by
  have hψ : Continuous fun m : GL (Fin 2) (InfiniteAdeleRing F) =>
      φ (g₀ * adelicArchGLIncl F m) - φ g₀ :=
    (hφ.comp (continuous_const.mul (continuous_adelicArchGLIncl F))).sub continuous_const
  have h0 : φ (g₀ * adelicArchGLIncl F 1) - φ g₀ = 0 := by
    rw [map_one, mul_one, sub_self]
  have hT : {m : GL (Fin 2) (InfiniteAdeleRing F) |
      ‖φ (g₀ * adelicArchGLIncl F m) - φ g₀‖ ≤ ‖φ g₀‖ / 2} ∈
        𝓝 (1 : GL (Fin 2) (InfiniteAdeleRing F)) := by
    have hpre := (hψ.continuousAt (x := (1 : GL (Fin 2) (InfiniteAdeleRing F)))).preimage_mem_nhds
      (closedBall_mem_nhds (φ (g₀ * adelicArchGLIncl F 1) - φ g₀) (half_pos (norm_pos_iff.2 hg₀)))
    rw [h0] at hpre
    exact Filter.mem_of_superset hpre fun m hm =>
      mem_closedBall_zero_iff.1 (Set.mem_preimage.1 hm)
  obtain ⟨ρ, hρ, hρε, h⟩ := exists_radius F hT
  exact ⟨ρ, hρ, hρε, fun m hm => h m hm⟩

structure ArchProfile (ρ : ℝ) where

  b : E F → ℝ
  smooth : ContDiff ℝ (⊤ : ℕ∞) b
  nonneg : ∀ m, 0 ≤ b m
  apply_cE : b (cE F) = 1
  dist_lt_of_ne_zero : ∀ m, b m ≠ 0 → dist m (cE F) < ρ

variable {F} in
theorem ArchProfile.eq_zero_of_le_dist {ρ : ℝ} (P : ArchProfile F ρ) {m : E F} (h : ρ ≤ dist m (cE F)) :
    P.b m = 0 := by
  by_contra hne
  exact absurd (P.dist_lt_of_ne_zero m hne) (not_lt.2 h)

def bumpAt (ρ : ℝ) (hρ : 0 < ρ) : ContDiffBump (cE F) where
  rIn := ρ / 2
  rOut := ρ
  rIn_pos := half_pos hρ
  rIn_lt_rOut := half_lt_self hρ

def ArchProfile.ofBump (ρ : ℝ) (hρ : 0 < ρ) : ArchProfile F ρ where
  b := (bumpAt F ρ hρ).toFun
  smooth := (bumpAt F ρ hρ).contDiff
  nonneg := fun _ => (bumpAt F ρ hρ).nonneg
  apply_cE := (bumpAt F ρ hρ).one_of_mem_closedBall (mem_closedBall_self (bumpAt F ρ hρ).rIn_pos.le)
  dist_lt_of_ne_zero := fun m hm => by
    by_contra h
    rw [not_lt] at h
    exact hm ((bumpAt F ρ hρ).zero_of_le_dist h)

variable {ρ : ℝ}

def Φ₂ (P : ArchProfile F ρ) (p : E F × E F) : ℂ :=
  ((P.b p.1 : ℝ) : ℂ) * (((bump₂ F).toFun p.2 : ℝ) : ℂ)

theorem hasCompactSupport_Φ₂ (P : ArchProfile F ρ) : HasCompactSupport (Φ₂ F P) := by
  refine HasCompactSupport.intro'
    ((isCompact_closedBall (cE F) ρ).prod
      (isCompact_closedBall (cE F) (bump₂ F).rOut))
    (isClosed_closedBall.prod isClosed_closedBall) fun p hp => ?_
  rw [Set.mem_prod, not_and_or] at hp
  rcases hp with h | h
  · have h' : P.b p.1 = 0 :=
      P.eq_zero_of_le_dist (le_of_lt (by rwa [mem_closedBall, not_le] at h))
    simp [Φ₂, h']
  · have h' : (bump₂ F).toFun p.2 = 0 :=
      (bump₂ F).zero_of_le_dist (le_of_lt (by rwa [mem_closedBall, not_le] at h))
    simp [Φ₂, h']

def fa (P : ArchProfile F ρ) : GL (Fin 2) (InfiniteAdeleRing F) → ℂ := Φ₂ F P ∘ J F

theorem fa_apply (P : ArchProfile F ρ) (g : GL (Fin 2) (InfiniteAdeleRing F)) :
    fa F P g = ((P.b (archEntries F g) : ℝ) : ℂ) *
      (((bump₂ F).toFun (archEntries F g⁻¹) : ℝ) : ℂ) := rfl

theorem fa_eq (P : ArchProfile F ρ) (hρε : ρ ≤ ε F / 2) (g : GL (Fin 2) (InfiniteAdeleRing F)) :
    fa F P g = ((P.b (archEntries F g) : ℝ) : ℂ) := by
  rw [fa_apply]
  by_cases h : archEntries F g ∈ closedBall (cE F) (ε F / 2)
  · rw [(bump₂ F).one_of_mem_closedBall (archEntries_inv_mem F g h), Complex.ofReal_one, mul_one]
  · have h0 : P.b (archEntries F g) = 0 := by
      apply P.eq_zero_of_le_dist
      rw [mem_closedBall, not_le] at h
      exact le_of_lt (lt_of_le_of_lt hρε h)
    rw [h0, Complex.ofReal_zero, zero_mul]

theorem isArchTestFactor_fa (P : ArchProfile F ρ) (hρε : ρ ≤ ε F / 2) :
    IsArchTestFactor F (fa F P) := by
  refine ⟨⟨fun m => ((P.b m : ℝ) : ℂ), ?_, fun g => fa_eq F P hρε g⟩, ?_⟩
  · have hc : (fun m : E F => ((P.b m : ℝ) : ℂ))
        = Complex.ofRealCLM ∘ P.b := by
      funext m
      simp
    rw [hc]
    exact Complex.ofRealCLM.contDiff.comp P.smooth
  · exact (hasCompactSupport_Φ₂ F P).comp_isClosedEmbedding (isClosedEmbedding_J F)

def Kf (N : Ideal (𝓞 F)) : Set (GL (Fin 2) (FiniteAdeleRing (𝓞 F) F)) :=
  (AdelicLevel.finiteLevelOne (𝓞 F) F N : Set (GL (Fin 2) (FiniteAdeleRing (𝓞 F) F)))

def ff (N : Ideal (𝓞 F)) : GL (Fin 2) (FiniteAdeleRing (𝓞 F) F) → ℂ :=
  (Kf F N).indicator fun _ => 1

theorem isOpen_Kf {N : Ideal (𝓞 F)} (hN : N ≠ ⊥) : IsOpen (Kf F N) :=
  AdelicLevel.isOpen_finiteLevelOne (𝓞 F) F hN

theorem isClosed_Kf (N : Ideal (𝓞 F)) : IsClosed (Kf F N) :=
  AdelicLevel.isClosed_finiteLevelOne (𝓞 F) F N

theorem isCompact_Kf (N : Ideal (𝓞 F)) : IsCompact (Kf F N) :=
  AdelicLevel.isCompact_finiteLevelOne (𝓞 F) F N

theorem isFinTestFactor_ff {N : Ideal (𝓞 F)} (hN : N ≠ ⊥) : IsFinTestFactor F (ff F N) := by
  refine ⟨?_, HasCompactSupport.intro' (isCompact_Kf F N) (isClosed_Kf F N)
    fun x hx => Set.indicator_of_notMem hx _⟩
  intro s
  have hpre : ff F N ⁻¹' s
      = (if (1 : ℂ) ∈ s then Kf F N else ∅) ∪ (if (0 : ℂ) ∈ s then (Kf F N)ᶜ else ∅) := by
    ext x
    by_cases hx : x ∈ Kf F N <;> by_cases h1 : (1 : ℂ) ∈ s <;> by_cases h0 : (0 : ℂ) ∈ s <;>
      simp [ff, Set.indicator, hx, h1, h0]
  rw [hpre]
  refine IsOpen.union ?_ ?_
  · split_ifs
    · exact isOpen_Kf F hN
    · exact isOpen_empty
  · split_ifs
    · exact (isClosed_Kf F N).isOpen_compl
    · exact isOpen_empty

theorem ff_mul_of_mem (N : Ideal (𝓞 F)) {k : GL (Fin 2) (FiniteAdeleRing (𝓞 F) F)}
    (hk : k ∈ AdelicLevel.finiteLevelOne (𝓞 F) F N) (x : GL (Fin 2) (FiniteAdeleRing (𝓞 F) F)) :
    ff F N (k * x) = ff F N x := by
  by_cases hx : x ∈ Kf F N
  · have hx' : x ∈ AdelicLevel.finiteLevelOne (𝓞 F) F N := hx
    have hkx : k * x ∈ Kf F N := mul_mem hk hx'
    simp only [ff, Set.indicator_of_mem hx, Set.indicator_of_mem hkx]
  · have hkx : k * x ∉ Kf F N := fun h =>
      hx ((Subgroup.mul_mem_cancel_left (AdelicLevel.finiteLevelOne (𝓞 F) F N) hk).1
        (show k * x ∈ AdelicLevel.finiteLevelOne (𝓞 F) F N from h))
    simp only [ff, Set.indicator_of_notMem hx, Set.indicator_of_notMem hkx]

def testFn (P : ArchProfile F ρ) (N : Ideal (𝓞 F)) : AdelicGL2 (𝓞 F) F → ℂ := fun g =>
  fa F P (AdelicLevel.glArch (𝓞 F) F g) * ff F N (AdelicLevel.glFin (𝓞 F) F g)

def testFnR (P : ArchProfile F ρ) (N : Ideal (𝓞 F)) : AdelicGL2 (𝓞 F) F → ℝ := fun g =>
  P.b (archEntries F (AdelicLevel.glArch (𝓞 F) F g)) *
    (Kf F N).indicator (fun _ => (1 : ℝ)) (AdelicLevel.glFin (𝓞 F) F g)

theorem isFactorizableTestFn_testFn (P : ArchProfile F ρ) (hρε : ρ ≤ ε F / 2)
    {N : Ideal (𝓞 F)} (hN : N ≠ ⊥) : IsFactorizableTestFn F (testFn F P N) :=
  ⟨fa F P, ff F N, isArchTestFactor_fa F P hρε, isFinTestFactor_ff F hN, fun _ => rfl⟩

theorem testFn_mul_of_mem (P : ArchProfile F ρ) (N : Ideal (𝓞 F)) {k : AdelicGL2 (𝓞 F) F}
    (hk : k ∈ AdelicLevel.levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F) (x : AdelicGL2 (𝓞 F) F) :
    testFn F P N (k * x) = testFn F P N x := by
  obtain ⟨hk₁, hk₂⟩ := Subgroup.mem_inf.1 hk
  have h1 : AdelicLevel.glArch (𝓞 F) F k = 1 := (mem_finiteAdelicGL2Subgroup_iff F k).1 hk₂
  have h2 : AdelicLevel.glFin (𝓞 F) F k ∈ AdelicLevel.finiteLevelOne (𝓞 F) F N :=
    AdelicLevel.mem_levelOne_iff.1 hk₁
  simp only [testFn, map_mul, h1, one_mul, ff_mul_of_mem F N h2]

theorem testFn_decomp (N : Ideal (𝓞 F)) (x : AdelicGL2 (𝓞 F) F)
    (hx : AdelicLevel.glFin (𝓞 F) F x ∈ Kf F N) :
    (adelicArchGLIncl F (AdelicLevel.glArch (𝓞 F) F x))⁻¹ * x ∈
      AdelicLevel.levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F := by
  refine Subgroup.mem_inf.2 ⟨?_, ?_⟩
  · rw [AdelicLevel.mem_levelOne_iff, map_mul, map_inv, glFin_adelicArchGLIncl, inv_one, one_mul]
    exact hx
  · rw [mem_finiteAdelicGL2Subgroup_iff, map_mul, map_inv, glArch_adelicArchGLIncl, inv_mul_cancel]

theorem glFin_mem_of_testFn_ne_zero (P : ArchProfile F ρ) (N : Ideal (𝓞 F))
    (x : AdelicGL2 (𝓞 F) F) (hx : testFn F P N x ≠ 0) : AdelicLevel.glFin (𝓞 F) F x ∈ Kf F N := by
  by_contra h
  exact hx (by simp only [testFn, ff, Set.indicator_of_notMem h, mul_zero])

theorem testFn_support (P : ArchProfile F ρ) (N : Ideal (𝓞 F)) (x : AdelicGL2 (𝓞 F) F)
    (hx : testFn F P N x ≠ 0) :
    ∃ a k : AdelicGL2 (𝓞 F) F, AdelicLevel.glFin (𝓞 F) F a = 1 ∧
      k ∈ AdelicLevel.levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F ∧ x = a * k :=
  ⟨adelicArchGLIncl F (AdelicLevel.glArch (𝓞 F) F x),
    (adelicArchGLIncl F (AdelicLevel.glArch (𝓞 F) F x))⁻¹ * x, glFin_adelicArchGLIncl F _,
    testFn_decomp F N x (glFin_mem_of_testFn_ne_zero F P N x hx), (mul_inv_cancel_left _ _).symm⟩

theorem testFn_eq_ofReal (P : ArchProfile F ρ) (hρε : ρ ≤ ε F / 2) (N : Ideal (𝓞 F))
    (g : AdelicGL2 (𝓞 F) F) : testFn F P N g = ((testFnR F P N g : ℝ) : ℂ) := by
  simp only [testFn, testFnR, fa_eq F P hρε, ff, Complex.ofReal_mul]
  congr 1
  by_cases h : AdelicLevel.glFin (𝓞 F) F g ∈ Kf F N
  · rw [Set.indicator_of_mem h, Set.indicator_of_mem h, Complex.ofReal_one]
  · rw [Set.indicator_of_notMem h, Set.indicator_of_notMem h, Complex.ofReal_zero]

theorem testFnR_nonneg (P : ArchProfile F ρ) (N : Ideal (𝓞 F)) (g : AdelicGL2 (𝓞 F) F) :
    0 ≤ testFnR F P N g :=
  mul_nonneg (P.nonneg _) (Set.indicator_nonneg (fun _ _ => zero_le_one) _)

theorem testFnR_one (P : ArchProfile F ρ) (N : Ideal (𝓞 F)) : testFnR F P N 1 = 1 := by
  have h1 : P.b (archEntries F 1) = 1 := P.apply_cE
  have h2 : (Kf F N).indicator (fun _ => (1 : ℝ)) 1 = 1 :=
    Set.indicator_of_mem
      (show (1 : GL (Fin 2) (FiniteAdeleRing (𝓞 F) F)) ∈ Kf F N from
        (AdelicLevel.finiteLevelOne (𝓞 F) F N).one_mem) _
  simp only [testFnR, map_one, h1, h2, mul_one]

theorem of_testFnR_ne_zero (P : ArchProfile F ρ) (N : Ideal (𝓞 F)) (x : AdelicGL2 (𝓞 F) F)
    (hx : testFnR F P N x ≠ 0) :
    dist (archEntries F (AdelicLevel.glArch (𝓞 F) F x)) (cE F) < ρ ∧
      AdelicLevel.glFin (𝓞 F) F x ∈ Kf F N := by
  constructor
  · by_contra h
    rw [not_lt] at h
    have h0 : P.b (archEntries F (AdelicLevel.glArch (𝓞 F) F x)) = 0 :=
      P.eq_zero_of_le_dist h
    exact hx (by simp only [testFnR, h0, zero_mul])
  · by_contra h
    exact hx (by simp only [testFnR, Set.indicator_of_notMem h, mul_zero])

theorem rightConv_ne_zero_of_bound (φ : AdelicGL2 (𝓞 F) F → ℂ) (hφ : Continuous φ)
    (g₀ : AdelicGL2 (𝓞 F) F) (hg₀ : φ g₀ ≠ 0) (f : AdelicGL2 (𝓞 F) F → ℂ) (hfc : Continuous f)
    (hfs : HasCompactSupport f) (fR : AdelicGL2 (𝓞 F) F → ℝ) (hfR : ∀ x, f x = ((fR x : ℝ) : ℂ))
    (hR0 : ∀ x, 0 ≤ fR x) (hR1 : fR 1 ≠ 0)
    (hbound : ∀ x, fR x ≠ 0 → ‖φ (g₀ * x) - φ g₀‖ ≤ ‖φ g₀‖ / 2) :
    rightConv F φ f g₀ ≠ 0 := by
  letI : MeasurableSpace (AdelicGL2 (𝓞 F) F) := AdelicHaar.glBorel (Fin 2) (𝓞 F) F
  haveI : BorelSpace (AdelicGL2 (𝓞 F) F) := AdelicHaar.borelSpace_glBorel (Fin 2) (𝓞 F) F
  haveI := AdelicHaar.isHaarMeasure_adelicGLHaar (Fin 2) (𝓞 F) F
  have hRre : fR = fun x => (f x).re := by
    funext x
    rw [hfR x, Complex.ofReal_re]
  have hRc : Continuous fR := by
    rw [hRre]
    exact Complex.continuous_re.comp hfc
  have hRs : HasCompactSupport fR := by
    rw [hRre]
    exact hfs.comp_left Complex.zero_re
  have hRi : Integrable fR (AdelicHaar.adelicGLHaar (Fin 2) (𝓞 F) F) :=
    hRc.integrable_of_hasCompactSupport hRs
  have hIpos : 0 < ∫ x, fR x ∂(AdelicHaar.adelicGLHaar (Fin 2) (𝓞 F) F) :=
    (integral_pos_iff_support_of_nonneg (fun x => hR0 x) hRi).2
      (hRc.isOpen_support.measure_pos _ ⟨1, hR1⟩)
  have hmul : Continuous fun x : AdelicGL2 (𝓞 F) F => g₀ * x := continuous_const.mul continuous_id
  have hi₁ : Integrable (fun x => φ (g₀ * x) * f x) (AdelicHaar.adelicGLHaar (Fin 2) (𝓞 F) F) :=
    ((hφ.comp hmul).mul hfc).integrable_of_hasCompactSupport hfs.mul_left
  have hi₂ : Integrable (fun x => φ g₀ * f x) (AdelicHaar.adelicGLHaar (Fin 2) (𝓞 F) F) :=
    (hfc.integrable_of_hasCompactSupport hfs).const_mul _
  have h3 : ∫ x, f x ∂(AdelicHaar.adelicGLHaar (Fin 2) (𝓞 F) F)
      = ((∫ x, fR x ∂(AdelicHaar.adelicGLHaar (Fin 2) (𝓞 F) F) : ℝ) : ℂ) := by
    simp only [hfR]
    exact integral_complex_ofReal
  intro h0
  have h2 : ∫ x, φ (g₀ * x) * f x ∂(AdelicHaar.adelicGLHaar (Fin 2) (𝓞 F) F) = 0 := h0
  have hint : ∫ x, (φ (g₀ * x) - φ g₀) * f x ∂(AdelicHaar.adelicGLHaar (Fin 2) (𝓞 F) F)
      = -(φ g₀ * ((∫ x, fR x ∂(AdelicHaar.adelicGLHaar (Fin 2) (𝓞 F) F) : ℝ) : ℂ)) := by
    have h1 : (fun x => (φ (g₀ * x) - φ g₀) * f x) = fun x => φ (g₀ * x) * f x - φ g₀ * f x := by
      funext x
      ring
    rw [h1, integral_sub hi₁ hi₂, h2, integral_const_mul, h3, zero_sub]
  have hle : ‖∫ x, (φ (g₀ * x) - φ g₀) * f x ∂(AdelicHaar.adelicGLHaar (Fin 2) (𝓞 F) F)‖
      ≤ ∫ x, ‖φ g₀‖ / 2 * fR x ∂(AdelicHaar.adelicGLHaar (Fin 2) (𝓞 F) F) := by
    refine norm_integral_le_of_norm_le (hRi.const_mul _) (Filter.Eventually.of_forall fun x => ?_)
    rw [norm_mul, hfR x, Complex.norm_real, Real.norm_of_nonneg (hR0 x)]
    by_cases hx : fR x = 0
    · simp [hx]
    · exact mul_le_mul_of_nonneg_right (hbound x hx) (hR0 x)
  rw [hint, norm_neg, norm_mul, Complex.norm_real, Real.norm_of_nonneg hIpos.le,
    integral_const_mul] at hle
  have hc : 0 < ‖φ g₀‖ := norm_pos_iff.2 hg₀
  nlinarith [mul_pos hc hIpos]

def ArchProfile.mk' {ρ : ℝ} (b : E F → ℝ) (hb : ContDiff ℝ (⊤ : ℕ∞) b) (hb0 : ∀ m, 0 ≤ b m)
    (hb1 : b (cE F) = 1) (hbρ : ∀ m, b m ≠ 0 → m ∈ Metric.ball (cE F) ρ) : ArchProfile F ρ :=
  ⟨b, hb, hb0, hb1, fun m hm => Metric.mem_ball.1 (hbρ m hm)⟩

theorem testFn_spec {N : Ideal (𝓞 F)} (hN : N ≠ ⊥)
    (φ : AdelicGL2 (𝓞 F) F → ℂ) (hcont : Continuous φ) (g₀ : AdelicGL2 (𝓞 F) F) (hg₀ : φ g₀ ≠ 0)
    (hlev : ∀ g : AdelicGL2 (𝓞 F) F, ∀ k ∈ AdelicLevel.levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F,
      φ (g * k) = φ g)
    {ρ : ℝ} (hρε : ρ ≤ ε F / 2)
    (hV : ∀ m : GL (Fin 2) (InfiniteAdeleRing F), dist (archEntries F m) (cE F) < ρ →
      ‖φ (g₀ * adelicArchGLIncl F m) - φ g₀‖ ≤ ‖φ g₀‖ / 2)
    (P : ArchProfile F ρ) :
    IsFactorizableTestFn F (testFn F P N) ∧
      (∀ k ∈ AdelicLevel.levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F, ∀ x,
        testFn F P N (k * x) = testFn F P N x) ∧
      (∀ x, testFn F P N x ≠ 0 → ∃ a k : AdelicGL2 (𝓞 F) F,
        AdelicLevel.glFin (𝓞 F) F a = 1 ∧ k ∈ AdelicLevel.levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F ∧
          x = a * k) ∧
      rightConv F φ (testFn F P N) g₀ ≠ 0 := by
  have htier := isFactorizableTestFn_testFn F P hρε hN
  refine ⟨htier, fun _ hk x => testFn_mul_of_mem F P N hk x, fun x hx => testFn_support F P N x hx, ?_⟩
  obtain ⟨hfc, hfs⟩ :=
    AutomorphicForm.continuous_and_hasCompactSupport_of_isFactorizableTestFn F _ htier
  refine rightConv_ne_zero_of_bound F φ hcont g₀ hg₀ _ hfc hfs (testFnR F P N)
    (testFn_eq_ofReal F P hρε N) (testFnR_nonneg F P N)
    (by rw [testFnR_one]; exact one_ne_zero) fun x hx => ?_
  obtain ⟨hdist, hfin⟩ := of_testFnR_ne_zero F P N x hx
  have hx' : g₀ * x = (g₀ * adelicArchGLIncl F (AdelicLevel.glArch (𝓞 F) F x)) *
      ((adelicArchGLIncl F (AdelicLevel.glArch (𝓞 F) F x))⁻¹ * x) := by
    rw [mul_assoc, mul_inv_cancel_left]
  rw [hx', hlev _ _ (testFn_decomp F N x hfin)]
  exact hV _ hdist

end Ws1.H2K.Scaffold

end

open Ws1.H2K.Scaffold in

theorem Ws1.H2K.sanity_3ea48e3c
    (K : Type) [Field K] [NumberField K]
    (N : Ideal (𝓞 K)) (hN : N ≠ ⊥)
    (φ : AdelicGL2 (𝓞 K) K → ℂ) (hcont : Continuous φ) (hne : ∃ g, φ g ≠ 0)
    (hlev : ∀ g : AdelicGL2 (𝓞 K) K, ∀ k ∈ levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K,
      φ (g * k) = φ g) :
    ∃ f : AdelicGL2 (𝓞 K) K → ℂ,
      IsFactorizableTestFn K f ∧
      (∀ k ∈ levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K, ∀ x, f (k * x) = f x) ∧
      (∀ x, f x ≠ 0 → ∃ a k : AdelicGL2 (𝓞 K) K,
        glFin (𝓞 K) K a = 1 ∧ k ∈ levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K ∧ x = a * k) ∧
      ∃ g, rightConv K φ f g ≠ 0 := by
  obtain ⟨g₀, hg₀⟩ := hne
  obtain ⟨ρ, hρ, hρε, hV⟩ := exists_radius_of_continuous K φ hcont g₀ hg₀
  obtain ⟨h1, h2, h3, h4⟩ := testFn_spec K hN φ hcont g₀ hg₀ hlev hρε hV (ArchProfile.ofBump K ρ hρ)
  exact ⟨_, h1, h2, h3, g₀, h4⟩

set_option autoImplicit false

p2m_open "NumberField NumberField.InfinitePlace.NumberField NumberField.AdelicLevel NumberField.InfinitePlace NumberField.InfinitePlace.NumberField.InfinitePlace NumberField.InfinitePlace.Completion"
p2m_open "NumberField.InfiniteAdeleRing AutomorphicForm Metric Topology MeasureTheory"
open scoped Classical BigOperators

noncomputable section

namespace Ws1
namespace H2K

variable (F : Type) [Field F] [NumberField F]

abbrev E : Type := Fin 2 → Fin 2 → mixedEmbedding.mixedSpace F

def cE : E F := archEntries F 1

theorem cE_fst (i j : Fin 2) (v : {w : InfinitePlace F // w.IsReal}) :
    (cE F i j).1 v = (1 : Matrix (Fin 2) (Fin 2) ℝ) i j := by
  simp only [cE, archEntries_apply, Units.val_one, ringEquiv_mixedSpace_apply]
  by_cases h : i = j
  · subst h
    rw [Matrix.one_apply_eq, Matrix.one_apply_eq]
    exact map_one _
  · rw [Matrix.one_apply_ne h, Matrix.one_apply_ne h]
    exact map_zero _

theorem cE_snd (i j : Fin 2) (v : {w : InfinitePlace F // w.IsComplex}) :
    (cE F i j).2 v = (1 : Matrix (Fin 2) (Fin 2) ℂ) i j := by
  simp only [cE, archEntries_apply, Units.val_one, ringEquiv_mixedSpace_apply]
  by_cases h : i = j
  · subst h
    rw [Matrix.one_apply_eq, Matrix.one_apply_eq]
    exact map_one _
  · rw [Matrix.one_apply_ne h, Matrix.one_apply_ne h]
    exact map_zero _

def sqSize (x : mixedEmbedding.mixedSpace F) : ℝ := (∑ v, (x.1 v) ^ 2) + ∑ v, ‖x.2 v‖ ^ 2

theorem sqSize_nonneg (x : mixedEmbedding.mixedSpace F) : 0 ≤ sqSize F x :=
  add_nonneg (Finset.sum_nonneg fun _ _ => sq_nonneg _) (Finset.sum_nonneg fun _ _ => sq_nonneg _)

theorem contDiff_sqSize : ContDiff ℝ (⊤ : ℕ∞) (sqSize F) := by
  refine ContDiff.add (ContDiff.sum fun v _ => ?_) (ContDiff.sum fun v _ => ?_)
  · exact ((contDiff_apply ℝ ℝ v).comp contDiff_fst).pow 2
  · exact ((contDiff_apply ℝ ℂ v).comp contDiff_snd).norm_sq ℝ

theorem sq_fst_le_sqSize (x : mixedEmbedding.mixedSpace F) (v : {w : InfinitePlace F // w.IsReal}) :
    (x.1 v) ^ 2 ≤ sqSize F x :=
  (Finset.single_le_sum (f := fun v => (x.1 v) ^ 2) (fun _ _ => sq_nonneg _) (Finset.mem_univ v)).trans
    (le_add_of_nonneg_right (Finset.sum_nonneg fun _ _ => sq_nonneg _))

theorem sq_snd_le_sqSize (x : mixedEmbedding.mixedSpace F) (v : {w : InfinitePlace F // w.IsComplex}) :
    ‖x.2 v‖ ^ 2 ≤ sqSize F x :=
  (Finset.single_le_sum (f := fun v => ‖x.2 v‖ ^ 2) (fun _ _ => sq_nonneg _) (Finset.mem_univ v)).trans
    (le_add_of_nonneg_left (Finset.sum_nonneg fun _ _ => sq_nonneg _))

theorem norm_le_sqrt_sqSize (x : mixedEmbedding.mixedSpace F) : ‖x‖ ≤ Real.sqrt (sqSize F x) := by
  rw [Prod.norm_def]
  refine max_le ?_ ?_
  · refine (pi_norm_le_iff_of_nonneg (Real.sqrt_nonneg _)).2 fun v => ?_
    rw [Real.norm_eq_abs, ← Real.sqrt_sq_eq_abs]
    exact Real.sqrt_le_sqrt (sq_fst_le_sqSize F x v)
  · refine (pi_norm_le_iff_of_nonneg (Real.sqrt_nonneg _)).2 fun v => ?_
    rw [← Real.sqrt_sq (norm_nonneg (x.2 v))]
    exact Real.sqrt_le_sqrt (sq_snd_le_sqSize F x v)

def q (m : E F) : ℝ := ∑ i, ∑ j, sqSize F (m i j - cE F i j)

theorem q_nonneg (m : E F) : 0 ≤ q F m :=
  Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => sqSize_nonneg F _

theorem contDiff_q : ContDiff ℝ (⊤ : ℕ∞) (q F) := by
  refine ContDiff.sum fun i _ => ContDiff.sum fun j _ => (contDiff_sqSize F).comp ?_
  exact ((contDiff_apply ℝ _ j).comp (contDiff_apply ℝ _ i)).sub contDiff_const

theorem q_cE : q F (cE F) = 0 := by
  simp [q, sqSize]

theorem sqSize_le_q (m : E F) (i j : Fin 2) : sqSize F (m i j - cE F i j) ≤ q F m :=
  (Finset.single_le_sum (f := fun j => sqSize F (m i j - cE F i j)) (fun _ _ => sqSize_nonneg F _)
    (Finset.mem_univ j)).trans
    (Finset.single_le_sum (f := fun i => ∑ j, sqSize F (m i j - cE F i j))
      (fun _ _ => Finset.sum_nonneg fun _ _ => sqSize_nonneg F _) (Finset.mem_univ i))

theorem dist_le_sqrt_q (m : E F) : dist m (cE F) ≤ Real.sqrt (q F m) := by
  rw [dist_eq_norm]
  refine (pi_norm_le_iff_of_nonneg (Real.sqrt_nonneg _)).2 fun i => ?_
  refine (pi_norm_le_iff_of_nonneg (Real.sqrt_nonneg _)).2 fun j => ?_
  exact (norm_le_sqrt_sqSize F _).trans (Real.sqrt_le_sqrt (sqSize_le_q F m i j))

def core (r : ℝ) (hr : 0 < r) : ContDiffBump (0 : ℝ) where
  rIn := r ^ 2 / 2
  rOut := r ^ 2
  rIn_pos := by positivity
  rIn_lt_rOut := by nlinarith [sq_pos_of_pos hr]

def bump (r : ℝ) (hr : 0 < r) (m : E F) : ℝ := core r hr (q F m)

theorem contDiff_bump (r : ℝ) (hr : 0 < r) : ContDiff ℝ (⊤ : ℕ∞) (bump F r hr) :=
  (core r hr).contDiff.comp (contDiff_q F)

theorem bump_nonneg (r : ℝ) (hr : 0 < r) (m : E F) : 0 ≤ bump F r hr m := (core r hr).nonneg

theorem bump_cE (r : ℝ) (hr : 0 < r) : bump F r hr (cE F) = 1 := by
  unfold bump
  rw [q_cE]
  exact (core r hr).one_of_mem_closedBall (by simp [core]; positivity)

theorem mem_ball_of_bump_ne_zero (r : ℝ) (hr : 0 < r) {m : E F} (h : bump F r hr m ≠ 0) :
    m ∈ ball (cE F) r := by
  have hq : q F m < r ^ 2 := by
    have hsupp : q F m ∈ Function.support (core r hr) := h
    rw [(core r hr).support_eq] at hsupp
    simpa [core, abs_of_nonneg (q_nonneg F m)] using hsupp
  rw [mem_ball]
  calc dist m (cE F) ≤ Real.sqrt (q F m) := dist_le_sqrt_q F m
    _ < Real.sqrt (r ^ 2) := Real.sqrt_lt_sqrt (q_nonneg F m) hq
    _ = r := Real.sqrt_sq hr.le

section Conjugation

variable {F}
variable {w : InfinitePlace F} (hw : w.IsReal)

omit [NumberField F] in
theorem infiniteAdele_sum_apply (s : Finset (Fin 2)) (f : Fin 2 → InfiniteAdeleRing F) (v : InfinitePlace F) :
    (∑ c ∈ s, f c) v = ∑ c ∈ s, f c v := by
  induction s using Finset.induction_on with
  | empty => rfl
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha, ← ih]
    rfl

def frob (M : Matrix (Fin 2) (Fin 2) ℝ) : ℝ := ∑ i, ∑ j, M i j ^ 2

theorem frob_eq_trace (M : Matrix (Fin 2) (Fin 2) ℝ) : frob M = (M.transpose * M).trace := by
  simp only [frob, Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.transpose_apply, Fin.sum_univ_two, pow_two]
  ring

theorem frob_transpose_mul_mul (κ M : Matrix (Fin 2) (Fin 2) ℝ) (hκ : κ * κ.transpose = 1) :
    frob (κ.transpose * M * κ) = frob M := by
  have hκ' : κ.transpose * κ = 1 := mul_eq_one_comm.mp hκ
  rw [frob_eq_trace, frob_eq_trace]
  have h1 : (κ.transpose * M * κ).transpose * (κ.transpose * M * κ) =
      κ.transpose * (M.transpose * M * κ) := by
    rw [Matrix.transpose_mul, Matrix.transpose_mul, Matrix.transpose_transpose]
    simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc κ κ.transpose, hκ, Matrix.one_mul]
  rw [h1, Matrix.trace_mul_comm, Matrix.mul_assoc, hκ, Matrix.mul_one]

def rotMatrixOf (k : rowIsometrySubgroup₀ w.Completion) : Matrix (Fin 2) (Fin 2) ℝ :=
  (ringEquivRealOfIsReal hw).toRingHom.mapMatrix ((k : GL (Fin 2) w.Completion) : Matrix (Fin 2) (Fin 2) w.Completion)

theorem rotMatrixOf_apply (k : rowIsometrySubgroup₀ w.Completion) (i j : Fin 2) :
    rotMatrixOf hw k i j = ringEquivRealOfIsReal hw (((k : GL (Fin 2) w.Completion) : Matrix _ _ _) i j) := rfl

theorem rotMatrixOf_mul_transpose (k : rowIsometrySubgroup₀ w.Completion) :
    rotMatrixOf hw k * (rotMatrixOf hw k).transpose = 1 := by
  have hmem := map_mem_rowIsometrySubgroup₀_of_normPreserving (ringEquivRealOfIsReal hw)
    (norm_ringEquivRealOfIsReal hw) (k : GL (Fin 2) w.Completion) k.2
  obtain ⟨-, -, hiso⟩ := (mem_rowIsometrySubgroup₀_iff ℝ).mp hmem
  have hent : ∀ i j, ((glEquivOfRingEquiv (ringEquivRealOfIsReal hw) (k : GL (Fin 2) w.Completion) :
      GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) i j = rotMatrixOf hw k i j := fun i j => rfl
  simp only [hent] at hiso
  set κ := rotMatrixOf hw k with hκ
  have h10 := hiso 1 0
  have h01 := hiso 0 1
  have h11 := hiso 1 1
  simp only [one_mul, zero_mul, add_zero, zero_add, Real.norm_eq_abs, sq_abs, one_pow,
    zero_pow two_ne_zero] at h10 h01 h11

  have r1 : κ 0 0 ^ 2 + κ 0 1 ^ 2 = 1 := h10
  have r2 : κ 1 0 ^ 2 + κ 1 1 ^ 2 = 1 := h01
  have r3 : κ 0 0 * κ 1 0 + κ 0 1 * κ 1 1 = 0 := by nlinarith [h11, r1, r2]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Matrix.transpose_apply, Fin.sum_univ_two] <;> nlinarith [r1, r2, r3]

theorem rotMatrixOf_inv (k : rowIsometrySubgroup₀ w.Completion) :
    rotMatrixOf hw k⁻¹ = (rotMatrixOf hw k).transpose := by
  have hmul : rotMatrixOf hw k⁻¹ * rotMatrixOf hw k = 1 := by
    unfold rotMatrixOf
    rw [← RingHom.map_mul (f := (ringEquivRealOfIsReal hw).toRingHom.mapMatrix)]
    · have : (((k⁻¹ : rowIsometrySubgroup₀ w.Completion) : GL (Fin 2) w.Completion) : Matrix (Fin 2) (Fin 2) w.Completion) *
          ((k : GL (Fin 2) w.Completion) : Matrix (Fin 2) (Fin 2) w.Completion) = 1 := by
        rw [Subgroup.coe_inv, ← Units.val_mul, inv_mul_cancel, Units.val_one]
      rw [this, map_one]
  have htr : (rotMatrixOf hw k).transpose * rotMatrixOf hw k = 1 :=
    mul_eq_one_comm.mp (rotMatrixOf_mul_transpose hw k)

  calc rotMatrixOf hw k⁻¹ = rotMatrixOf hw k⁻¹ * (rotMatrixOf hw k * (rotMatrixOf hw k).transpose) := by
        rw [rotMatrixOf_mul_transpose, Matrix.mul_one]
    _ = (rotMatrixOf hw k⁻¹ * rotMatrixOf hw k) * (rotMatrixOf hw k).transpose := by rw [Matrix.mul_assoc]
    _ = (rotMatrixOf hw k).transpose := by rw [hmul, Matrix.one_mul]

def archRotOf (k : rowIsometrySubgroup₀ w.Completion) : GL (Fin 2) (InfiniteAdeleRing F) :=
  archGLIncl F w (k : GL (Fin 2) w.Completion)

theorem archRotOf_coe_apply_self (k : rowIsometrySubgroup₀ w.Completion) (i j : Fin 2) :
    ((archRotOf k : GL (Fin 2) (InfiniteAdeleRing F)) : Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing F)) i j w =
      ((k : GL (Fin 2) w.Completion) : Matrix (Fin 2) (Fin 2) w.Completion) i j :=
  archMatrixUpdate_apply_self F w _ i j

theorem archRotOf_coe_apply_of_ne (k : rowIsometrySubgroup₀ w.Completion) (i j : Fin 2)
    {v : InfinitePlace F} (hv : v ≠ w) :
    ((archRotOf k : GL (Fin 2) (InfiniteAdeleRing F)) : Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing F)) i j v =
      (1 : Matrix (Fin 2) (Fin 2) v.Completion) i j :=
  archMatrixUpdate_apply_of_ne F w _ i j hv

theorem archRotOf_inv (k : rowIsometrySubgroup₀ w.Completion) : (archRotOf k)⁻¹ = archRotOf k⁻¹ := by
  unfold archRotOf
  rw [Subgroup.coe_inv, map_inv]

theorem archEntries_fst_mul (x y : GL (Fin 2) (InfiniteAdeleRing F)) (i j : Fin 2) :
    (archEntries F (x * y) i j).1 ⟨w, hw⟩ =
      ∑ c, (archEntries F x i c).1 ⟨w, hw⟩ * (archEntries F y c j).1 ⟨w, hw⟩ := by
  simp only [archEntries_apply, ringEquiv_mixedSpace_apply, Units.val_mul, Matrix.mul_apply]
  rw [infiniteAdele_sum_apply, map_sum]
  refine Finset.sum_congr rfl fun c _ => ?_
  exact map_mul _ _ _

theorem archEntries_fst_mul_of_ne (x y : GL (Fin 2) (InfiniteAdeleRing F)) (i j : Fin 2)
    (v : {w' : InfinitePlace F // w'.IsReal}) :
    (archEntries F (x * y) i j).1 v = ∑ c, (archEntries F x i c).1 v * (archEntries F y c j).1 v := by
  simp only [archEntries_apply, ringEquiv_mixedSpace_apply, Units.val_mul, Matrix.mul_apply]
  rw [infiniteAdele_sum_apply, map_sum]
  refine Finset.sum_congr rfl fun c _ => ?_
  exact map_mul _ _ _

theorem archEntries_snd_mul (x y : GL (Fin 2) (InfiniteAdeleRing F)) (i j : Fin 2)
    (v : {w' : InfinitePlace F // w'.IsComplex}) :
    (archEntries F (x * y) i j).2 v = ∑ c, (archEntries F x i c).2 v * (archEntries F y c j).2 v := by
  simp only [archEntries_apply, ringEquiv_mixedSpace_apply, Units.val_mul, Matrix.mul_apply]
  rw [infiniteAdele_sum_apply, map_sum]
  refine Finset.sum_congr rfl fun c _ => ?_
  exact map_mul _ _ _

theorem archEntries_archRotOf_fst_self (k : rowIsometrySubgroup₀ w.Completion) (i j : Fin 2) :
    (archEntries F (archRotOf k) i j).1 ⟨w, hw⟩ = rotMatrixOf hw k i j := by
  simp only [archEntries_apply, ringEquiv_mixedSpace_apply, archRotOf_coe_apply_self, rotMatrixOf_apply]
  rfl

theorem archEntries_archRotOf_fst_of_ne (k : rowIsometrySubgroup₀ w.Completion) (i j : Fin 2)
    (v : {w' : InfinitePlace F // w'.IsReal}) (hv : (v : InfinitePlace F) ≠ w) :
    (archEntries F (archRotOf k) i j).1 v = (1 : Matrix (Fin 2) (Fin 2) ℝ) i j := by
  simp only [archEntries_apply, ringEquiv_mixedSpace_apply]
  rw [archRotOf_coe_apply_of_ne k i j hv]
  by_cases h : i = j
  · subst h; rw [Matrix.one_apply_eq, Matrix.one_apply_eq]; exact map_one _
  · rw [Matrix.one_apply_ne h, Matrix.one_apply_ne h]; exact map_zero _

include hw in

theorem archEntries_archRotOf_snd (k : rowIsometrySubgroup₀ w.Completion) (i j : Fin 2)
    (v : {w' : InfinitePlace F // w'.IsComplex}) :
    (archEntries F (archRotOf k) i j).2 v = (1 : Matrix (Fin 2) (Fin 2) ℂ) i j := by
  have hv : (v : InfinitePlace F) ≠ w := fun h => by
    have h1 : (v : InfinitePlace F).IsComplex := v.2
    rw [h] at h1
    exact (not_isReal_iff_isComplex.mpr h1) hw
  simp only [archEntries_apply, ringEquiv_mixedSpace_apply]
  rw [archRotOf_coe_apply_of_ne k i j hv]
  by_cases h : i = j
  · subst h; rw [Matrix.one_apply_eq, Matrix.one_apply_eq]; exact map_one _
  · rw [Matrix.one_apply_ne h, Matrix.one_apply_ne h]; exact map_zero _

def wBlock (m : E F) : Matrix (Fin 2) (Fin 2) ℝ := fun i j => (m i j).1 ⟨w, hw⟩

theorem archEntries_conj_fst_self (k : rowIsometrySubgroup₀ w.Completion) (g : GL (Fin 2) (InfiniteAdeleRing F))
    (i j : Fin 2) :
    (archEntries F ((archRotOf k)⁻¹ * g * archRotOf k) i j).1 ⟨w, hw⟩ =
      ((rotMatrixOf hw k).transpose * wBlock hw (archEntries F g) * rotMatrixOf hw k) i j := by
  rw [archEntries_fst_mul hw, Matrix.mul_apply]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [archEntries_fst_mul hw, archEntries_archRotOf_fst_self, Matrix.mul_apply]
  congr 1
  refine Finset.sum_congr rfl fun d _ => ?_
  rw [archRotOf_inv, archEntries_archRotOf_fst_self, rotMatrixOf_inv, Matrix.transpose_apply]
  rfl

theorem archEntries_conj_fst_of_ne (k : rowIsometrySubgroup₀ w.Completion) (g : GL (Fin 2) (InfiniteAdeleRing F))
    (i j : Fin 2) (v : {w' : InfinitePlace F // w'.IsReal}) (hv : (v : InfinitePlace F) ≠ w) :
    (archEntries F ((archRotOf k)⁻¹ * g * archRotOf k) i j).1 v = (archEntries F g i j).1 v := by
  rw [archEntries_fst_mul_of_ne]
  simp_rw [archEntries_fst_mul_of_ne ((archRotOf k)⁻¹) g, archRotOf_inv, archEntries_archRotOf_fst_of_ne _ _ _ _ hv]
  fin_cases i <;> fin_cases j <;> simp [Matrix.one_apply, Fin.sum_univ_two]

include hw in
theorem archEntries_conj_snd (k : rowIsometrySubgroup₀ w.Completion) (g : GL (Fin 2) (InfiniteAdeleRing F))
    (i j : Fin 2) (v : {w' : InfinitePlace F // w'.IsComplex}) :
    (archEntries F ((archRotOf k)⁻¹ * g * archRotOf k) i j).2 v = (archEntries F g i j).2 v := by
  rw [archEntries_snd_mul]
  simp_rw [archEntries_snd_mul ((archRotOf k)⁻¹) g, archRotOf_inv, archEntries_archRotOf_snd hw]
  fin_cases i <;> fin_cases j <;> simp [Matrix.one_apply, Fin.sum_univ_two]

def restPart (x : mixedEmbedding.mixedSpace F) : ℝ :=
  (∑ v ∈ Finset.univ.erase ⟨w, hw⟩, (x.1 v) ^ 2) + ∑ v, ‖x.2 v‖ ^ 2

theorem sqSize_split (x : mixedEmbedding.mixedSpace F) :
    sqSize F x = (x.1 ⟨w, hw⟩) ^ 2 + restPart hw x := by
  unfold sqSize restPart
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ (⟨w, hw⟩ : {w' : InfinitePlace F // w'.IsReal})), add_assoc]

theorem q_split (m : E F) : q F m = frob (wBlock hw m - 1) + ∑ i, ∑ j, restPart hw (m i j - cE F i j) := by
  have h1 : ∀ i j, sqSize F (m i j - cE F i j) = (wBlock hw m - 1) i j ^ 2 + restPart hw (m i j - cE F i j) := by
    intro i j
    rw [sqSize_split hw]
    congr 2
    rw [Matrix.sub_apply, Prod.fst_sub, Pi.sub_apply, cE_fst]
    rfl
  unfold q frob
  simp_rw [h1, Finset.sum_add_distrib]

include hw in

theorem q_archEntries_conj (k : rowIsometrySubgroup₀ w.Completion) (g : GL (Fin 2) (InfiniteAdeleRing F)) :
    q F (archEntries F ((archRotOf k)⁻¹ * g * archRotOf k)) = q F (archEntries F g) := by
  rw [q_split hw, q_split hw]
  have hrest : ∀ i j, restPart hw (archEntries F ((archRotOf k)⁻¹ * g * archRotOf k) i j - cE F i j) =
      restPart hw (archEntries F g i j - cE F i j) := by
    intro i j
    unfold restPart
    congr 1
    · refine Finset.sum_congr rfl fun v hv => ?_
      have hv' : (v : InfinitePlace F) ≠ w := fun h => Finset.ne_of_mem_erase hv (Subtype.ext h)
      rw [Prod.fst_sub, Pi.sub_apply, Prod.fst_sub, Pi.sub_apply, archEntries_conj_fst_of_ne k g i j v hv']
    · refine Finset.sum_congr rfl fun v _ => ?_
      rw [Prod.snd_sub, Pi.sub_apply, Prod.snd_sub, Pi.sub_apply, archEntries_conj_snd hw]
  have hb : wBlock hw (archEntries F ((archRotOf k)⁻¹ * g * archRotOf k)) - 1 =
      (rotMatrixOf hw k).transpose * (wBlock hw (archEntries F g) - 1) * rotMatrixOf hw k := by
    have hκ' : (rotMatrixOf hw k).transpose * rotMatrixOf hw k = 1 :=
      mul_eq_one_comm.mp (rotMatrixOf_mul_transpose hw k)
    rw [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, hκ']
    congr 1
    ext i j
    exact archEntries_conj_fst_self hw k g i j
  rw [hb, frob_transpose_mul_mul _ _ (rotMatrixOf_mul_transpose hw k)]
  simp_rw [hrest]

include hw in

theorem bump_archEntries_conj (r : ℝ) (hr : 0 < r) (k : rowIsometrySubgroup₀ w.Completion)
    (g : GL (Fin 2) (InfiniteAdeleRing F)) :
    bump F r hr (archEntries F ((archRotOf k)⁻¹ * g * archRotOf k)) = bump F r hr (archEntries F g) := by
  unfold bump
  rw [q_archEntries_conj hw]

end Conjugation

section TypeKeep

variable {F}
variable {w : InfinitePlace F} (hw : w.IsReal)

theorem glArch_adelicArchGLInclAt (k : GL (Fin 2) w.Completion) :
    glArch (𝓞 F) F (adelicArchGLInclAt F w k) = archGLIncl F w k :=
  glArch_adelicArchGLIncl F _

theorem glFin_adelicArchGLInclAt (k : GL (Fin 2) w.Completion) :
    glFin (𝓞 F) F (adelicArchGLInclAt F w k) = 1 :=
  glFin_adelicArchGLIncl F _

theorem hasArchCharacterAt₀_rightConv_of_conj_invariant (χ : rowIsometrySubgroup₀ w.Completion →* ℂˣ)
    {φ f : AdelicGL2 (𝓞 F) F → ℂ} (hφ : HasArchCharacterAt₀ F w χ φ)
    (hf : ∀ k : rowIsometrySubgroup₀ w.Completion, ∀ x : AdelicGL2 (𝓞 F) F,
      f ((adelicArchGLInclAt F w (k : GL (Fin 2) w.Completion))⁻¹ * x *
        adelicArchGLInclAt F w (k : GL (Fin 2) w.Completion)) = f x) :
    HasArchCharacterAt₀ F w χ (rightConv F φ f) := by
  intro k g
  letI : MeasurableSpace (AdelicGL2 (𝓞 F) F) := AdelicHaar.glBorel (Fin 2) (𝓞 F) F
  haveI : BorelSpace (AdelicGL2 (𝓞 F) F) := AdelicHaar.borelSpace_glBorel (Fin 2) (𝓞 F) F
  haveI := AdelicHaar.isHaarMeasure_adelicGLHaar (Fin 2) (𝓞 F) F
  haveI := NumberField.AdelicHaar.isMulRightInvariant_adelicGLHaar F
  set u : AdelicGL2 (𝓞 F) F := adelicArchGLInclAt F w (k : GL (Fin 2) w.Completion) with hu
  rw [rightConv_apply, rightConv_apply, ← integral_const_mul]

  have h1 : (∫ x, φ (g * u * x) * f x ∂AdelicHaar.adelicGLHaar (Fin 2) (𝓞 F) F) =
      ∫ x, φ (g * u * (u⁻¹ * x)) * f (u⁻¹ * x) ∂AdelicHaar.adelicGLHaar (Fin 2) (𝓞 F) F :=
    (integral_mul_left_eq_self (fun x => φ (g * u * x) * f x) u⁻¹).symm
  have h2 : (∫ x, φ (g * u * (u⁻¹ * x)) * f (u⁻¹ * x) ∂AdelicHaar.adelicGLHaar (Fin 2) (𝓞 F) F) =
      ∫ x, φ (g * u * (u⁻¹ * (x * u))) * f (u⁻¹ * (x * u)) ∂AdelicHaar.adelicGLHaar (Fin 2) (𝓞 F) F :=
    (integral_mul_right_eq_self (fun x => φ (g * u * (u⁻¹ * x)) * f (u⁻¹ * x)) u).symm
  rw [h1, h2]
  refine integral_congr_ae (ae_of_all _ fun x => ?_)
  simp only
  have hx : g * u * (u⁻¹ * (x * u)) = g * x * u := by group
  rw [hx, ← mul_assoc u⁻¹ x u, hf k x, hφ k (g * x)]
  ring

end TypeKeep

end Ws1.H2K

end

set_option autoImplicit false

p2m_open "NumberField NumberField.InfinitePlace.NumberField NumberField.AdelicLevel AutomorphicForm NumberField.InfinitePlace NumberField.InfinitePlace.NumberField.InfinitePlace NumberField.InfinitePlace.Completion"

open Ws1.H2K.Scaffold in
theorem solution
    (K : Type) [Field K] [NumberField K]
    (N : Ideal (𝓞 K)) (hN : N ≠ ⊥) (w : InfinitePlace K) (hw : w.IsReal) (k : ℤ)
    (φ : AdelicGL2 (𝓞 K) K → ℂ) (hcont : Continuous φ) (hne : ∃ g, φ g ≠ 0)
    (hlev : ∀ g : AdelicGL2 (𝓞 K) K, ∀ u ∈ levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K,
      φ (g * u) = φ g)
    (hk : HasArchCharacterAt₀ K w
      ((archWeightCharℝ k).comp (rowIsometrySubgroup₀Map (ringEquivRealOfIsReal hw)
        (norm_ringEquivRealOfIsReal hw))) φ) :
    ∃ f : AdelicGL2 (𝓞 K) K → ℂ,
      IsFactorizableTestFn K f ∧
      (∀ u ∈ levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K, ∀ x, f (u * x) = f x) ∧
      (∀ x, f x ≠ 0 → ∃ a u : AdelicGL2 (𝓞 K) K,
        glFin (𝓞 K) K a = 1 ∧ u ∈ levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K ∧ x = a * u) ∧
      HasArchCharacterAt₀ K w
        ((archWeightCharℝ k).comp (rowIsometrySubgroup₀Map (ringEquivRealOfIsReal hw)
          (norm_ringEquivRealOfIsReal hw))) (rightConv K φ f) ∧
      ∃ g, rightConv K φ f g ≠ 0 := by
  obtain ⟨g₀, hg₀⟩ := hne
  obtain ⟨ρ, hρ, hρε, hV⟩ := exists_radius_of_continuous K φ hcont g₀ hg₀
  let P : ArchProfile K ρ :=
    ArchProfile.mk' K (Ws1.H2K.bump K ρ hρ) (Ws1.H2K.contDiff_bump K ρ hρ) (Ws1.H2K.bump_nonneg K ρ hρ)
      (Ws1.H2K.bump_cE K ρ hρ) (fun m hm => Ws1.H2K.mem_ball_of_bump_ne_zero K ρ hρ hm)
  obtain ⟨h1, h2, h3, h5⟩ := testFn_spec K hN φ hcont g₀ hg₀ hlev hρε hV P
  refine ⟨testFn K P N, h1, h2, h3, ?_, g₀, h5⟩
  refine Ws1.H2K.hasArchCharacterAt₀_rightConv_of_conj_invariant _ hk fun kk x => ?_

  have hfin : AdelicLevel.glFin (𝓞 K) K (adelicArchGLInclAt K w (kk : GL (Fin 2) w.Completion)) = 1 :=
    glFin_adelicArchGLIncl K _
  have harch : AdelicLevel.glArch (𝓞 K) K (adelicArchGLInclAt K w (kk : GL (Fin 2) w.Completion)) =
      archGLIncl K w (kk : GL (Fin 2) w.Completion) :=
    glArch_adelicArchGLIncl K _
  show fa K P (AdelicLevel.glArch (𝓞 K) K _) * ff K N (AdelicLevel.glFin (𝓞 K) K _) =
    fa K P (AdelicLevel.glArch (𝓞 K) K x) * ff K N (AdelicLevel.glFin (𝓞 K) K x)
  simp only [map_mul, map_inv, hfin, harch, inv_one, one_mul, mul_one]
  rw [fa_eq K P hρε, fa_eq K P hρε]
  have hb : P.b (archEntries K ((archGLIncl K w (kk : GL (Fin 2) w.Completion))⁻¹ *
        AdelicLevel.glArch (𝓞 K) K x * archGLIncl K w (kk : GL (Fin 2) w.Completion))) =
      P.b (archEntries K (AdelicLevel.glArch (𝓞 K) K x)) :=
    Ws1.H2K.bump_archEntries_conj hw ρ hρ kk (AdelicLevel.glArch (𝓞 K) K x)
  rw [hb]

end S_AutomorphicForm_exists_isFactorizableTestFn_hasArchCharacterAt_rightConv_ne_zero_of_hasArchCharacterAt
end P2MW
export P2MW.S_AutomorphicForm_exists_isFactorizableTestFn_hasArchCharacterAt_rightConv_ne_zero_of_hasArchCharacterAt (solution)
