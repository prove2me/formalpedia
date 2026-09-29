-- Prove2me | solution 1 for AutomorphicForm.integral_twistedConj_prod_mul_eq_mul_integral_integral_of_sigmaCentralizer
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:05.340288+00:00
-- url     : https://prove2.me/submissions/66ce927b-2811-5ad3-9b97-db25819d486f

import Mathlib
import Definitions.Def_AutomorphicForm_SigmaCentralizer
import Theorems.Thm_AutomorphicForm_integral_mul_eq_integral_mul_of_forall_integral_subgroup_mul_eq_one
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_integral_twistedConj_prod_mul_eq_mul_integral_integral_of_sigmaCentralizer

set_option autoImplicit false

open MeasureTheory
open scoped NNReal

namespace S30TwistedFubini

open AutomorphicForm

section ProductTori

open MeasureTheory

namespace GroupOrbital

section Closed

variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [T2Space G]

theorem isClosed_sigmaCentralizer {θ : G →* G} (hθ : Continuous θ) (δ : G) :
    IsClosed (AutomorphicForm.sigmaCentralizer θ δ : Set G) := by
  have h : (AutomorphicForm.sigmaCentralizer θ δ : Set G) = (fun t => t * δ * (θ t)⁻¹) ⁻¹' {δ} := by
    ext t
    simp only [SetLike.mem_coe, AutomorphicForm.mem_sigmaCentralizer_iff, Set.mem_preimage, Set.mem_singleton_iff]
  rw [h]
  exact IsClosed.preimage ((continuous_id.mul continuous_const).mul hθ.inv) isClosed_singleton

end Closed

section Algebra

variable {G₁ G₂ : Type} [Group G₁] [Group G₂]

theorem mem_sigmaCentralizer_prodMap_iff (θ₁ : G₁ →* G₁) (θ₂ : G₂ →* G₂) (δ₁ : G₁) (δ₂ : G₂) (t : G₁ × G₂) :
    t ∈ AutomorphicForm.sigmaCentralizer (θ₁.prodMap θ₂) (δ₁, δ₂) ↔
      t.1 ∈ AutomorphicForm.sigmaCentralizer θ₁ δ₁ ∧ t.2 ∈ AutomorphicForm.sigmaCentralizer θ₂ δ₂ := by
  obtain ⟨t₁, t₂⟩ := t
  simp only [AutomorphicForm.mem_sigmaCentralizer_iff, MonoidHom.coe_prodMap, Prod.map_apply, Prod.inv_mk,
    Prod.mk_mul_mk, Prod.mk.injEq]

theorem sigmaCentralizer_prodMap_comm (θ₁ : G₁ →* G₁) (θ₂ : G₂ →* G₂) (δ₁ : G₁) (δ₂ : G₂)
    (h₁ : ∀ s ∈ AutomorphicForm.sigmaCentralizer θ₁ δ₁, ∀ t ∈ AutomorphicForm.sigmaCentralizer θ₁ δ₁,
      s * t = t * s)
    (h₂ : ∀ s ∈ AutomorphicForm.sigmaCentralizer θ₂ δ₂, ∀ t ∈ AutomorphicForm.sigmaCentralizer θ₂ δ₂,
      s * t = t * s) :
    ∀ s ∈ AutomorphicForm.sigmaCentralizer (θ₁.prodMap θ₂) (δ₁, δ₂),
      ∀ t ∈ AutomorphicForm.sigmaCentralizer (θ₁.prodMap θ₂) (δ₁, δ₂), s * t = t * s := by
  intro s hs t ht
  rw [mem_sigmaCentralizer_prodMap_iff] at hs ht
  exact Prod.ext (h₁ _ hs.1 _ ht.1) (h₂ _ hs.2 _ ht.2)

def prodTorusMulEquiv (θ₁ : G₁ →* G₁) (θ₂ : G₂ →* G₂) (δ₁ : G₁) (δ₂ : G₂) :
    AutomorphicForm.sigmaCentralizer θ₁ δ₁ × AutomorphicForm.sigmaCentralizer θ₂ δ₂ ≃*
      AutomorphicForm.sigmaCentralizer (θ₁.prodMap θ₂) (δ₁, δ₂) :=
  { toFun := fun t => ⟨((t.1 : G₁), (t.2 : G₂)), (mem_sigmaCentralizer_prodMap_iff θ₁ θ₂ δ₁ δ₂ _).mpr ⟨t.1.2, t.2.2⟩⟩
    invFun := fun t =>
      (⟨(t : G₁ × G₂).1, ((mem_sigmaCentralizer_prodMap_iff θ₁ θ₂ δ₁ δ₂ _).mp t.2).1⟩,
       ⟨(t : G₁ × G₂).2, ((mem_sigmaCentralizer_prodMap_iff θ₁ θ₂ δ₁ δ₂ _).mp t.2).2⟩)
    left_inv := fun _ => rfl
    right_inv := fun _ => rfl
    map_mul' := fun _ _ => rfl }

end Algebra

section Topology

variable {G₁ G₂ : Type} [Group G₁] [TopologicalSpace G₁] [Group G₂] [TopologicalSpace G₂]

def prodTorusEquiv (θ₁ : G₁ →* G₁) (θ₂ : G₂ →* G₂) (δ₁ : G₁) (δ₂ : G₂) :
    AutomorphicForm.sigmaCentralizer θ₁ δ₁ × AutomorphicForm.sigmaCentralizer θ₂ δ₂ ≃ₜ*
      AutomorphicForm.sigmaCentralizer (θ₁.prodMap θ₂) (δ₁, δ₂) :=
  { toMulEquiv := prodTorusMulEquiv θ₁ θ₂ δ₁ δ₂
    continuous_toFun :=
      ((continuous_subtype_val.comp continuous_fst).prodMk (continuous_subtype_val.comp continuous_snd)).subtype_mk _
    continuous_invFun :=
      ((continuous_fst.comp continuous_subtype_val).subtype_mk _).prodMk
        ((continuous_snd.comp continuous_subtype_val).subtype_mk _) }

theorem prodTorusEquiv_apply_coe (θ₁ : G₁ →* G₁) (θ₂ : G₂ →* G₂) (δ₁ : G₁) (δ₂ : G₂)
    (t : AutomorphicForm.sigmaCentralizer θ₁ δ₁ × AutomorphicForm.sigmaCentralizer θ₂ δ₂) :
    ((prodTorusEquiv θ₁ θ₂ δ₁ δ₂ t : AutomorphicForm.sigmaCentralizer (θ₁.prodMap θ₂) (δ₁, δ₂)) : G₁ × G₂) =
      ((t.1 : G₁), (t.2 : G₂)) :=
  rfl

noncomputable def prodTorusMeasure (θ₁ : G₁ →* G₁) (θ₂ : G₂ →* G₂) (δ₁ : G₁) (δ₂ : G₂)
    (τ₁ : @Measure (AutomorphicForm.sigmaCentralizer θ₁ δ₁) (borel _))
    (τ₂ : @Measure (AutomorphicForm.sigmaCentralizer θ₂ δ₂) (borel _)) :
    @Measure (AutomorphicForm.sigmaCentralizer (θ₁.prodMap θ₂) (δ₁, δ₂)) (borel _) :=
  @Measure.map _ _ (@Prod.instMeasurableSpace _ _ (borel _) (borel _)) (borel _) (prodTorusEquiv θ₁ θ₂ δ₁ δ₂)
    (@Measure.prod _ _ (borel _) (borel _) τ₁ τ₂)

variable [SecondCountableTopology G₁] [SecondCountableTopology G₂]

omit [SecondCountableTopology G₁] in

theorem integral_prodTorusMeasure (θ₁ : G₁ →* G₁) (θ₂ : G₂ →* G₂) (δ₁ : G₁) (δ₂ : G₂)
    (τ₁ : @Measure (AutomorphicForm.sigmaCentralizer θ₁ δ₁) (borel _))
    (τ₂ : @Measure (AutomorphicForm.sigmaCentralizer θ₂ δ₂) (borel _))
    (g : AutomorphicForm.sigmaCentralizer (θ₁.prodMap θ₂) (δ₁, δ₂) → ℝ) :
    ∫ t, g t ∂(prodTorusMeasure θ₁ θ₂ δ₁ δ₂ τ₁ τ₂) =
      ∫ s, g (prodTorusEquiv θ₁ θ₂ δ₁ δ₂ s) ∂(@Measure.prod _ _ (borel _) (borel _) τ₁ τ₂) := by
  letI : MeasurableSpace (AutomorphicForm.sigmaCentralizer θ₁ δ₁) := borel _
  haveI : BorelSpace (AutomorphicForm.sigmaCentralizer θ₁ δ₁) := ⟨rfl⟩
  letI : MeasurableSpace (AutomorphicForm.sigmaCentralizer θ₂ δ₂) := borel _
  haveI : BorelSpace (AutomorphicForm.sigmaCentralizer θ₂ δ₂) := ⟨rfl⟩
  letI : MeasurableSpace (AutomorphicForm.sigmaCentralizer (θ₁.prodMap θ₂) (δ₁, δ₂)) := borel _
  haveI : BorelSpace (AutomorphicForm.sigmaCentralizer (θ₁.prodMap θ₂) (δ₁, δ₂)) := ⟨rfl⟩
  haveI : SecondCountableTopology (AutomorphicForm.sigmaCentralizer θ₂ δ₂) :=
    TopologicalSpace.secondCountableTopology_induced _ _ Subtype.val
  haveI : BorelSpace (AutomorphicForm.sigmaCentralizer θ₁ δ₁ × AutomorphicForm.sigmaCentralizer θ₂ δ₂) :=
    Prod.borelSpace
  unfold prodTorusMeasure
  rw [show (⇑(prodTorusEquiv θ₁ θ₂ δ₁ δ₂)) = ⇑((prodTorusEquiv θ₁ θ₂ δ₁ δ₂).toHomeomorph.toMeasurableEquiv) from rfl]
  exact MeasureTheory.integral_map_equiv _ g

omit [SecondCountableTopology G₁] in

theorem integral_prodTorusMeasure_mul (θ₁ : G₁ →* G₁) (θ₂ : G₂ →* G₂) (δ₁ : G₁) (δ₂ : G₂)
    (τ₁ : @Measure (AutomorphicForm.sigmaCentralizer θ₁ δ₁) (borel _))
    (τ₂ : @Measure (AutomorphicForm.sigmaCentralizer θ₂ δ₂) (borel _))
    [@SFinite _ (borel _) τ₁] [@SFinite _ (borel _) τ₂] (W₁ : G₁ → ℝ) (W₂ : G₂ → ℝ) (x : G₁ × G₂) :
    ∫ t : AutomorphicForm.sigmaCentralizer (θ₁.prodMap θ₂) (δ₁, δ₂),
        W₁ ((t : G₁ × G₂).1 * x.1) * W₂ ((t : G₁ × G₂).2 * x.2) ∂(prodTorusMeasure θ₁ θ₂ δ₁ δ₂ τ₁ τ₂) =
      (∫ t : AutomorphicForm.sigmaCentralizer θ₁ δ₁, W₁ (t * x.1) ∂τ₁) *
        ∫ t : AutomorphicForm.sigmaCentralizer θ₂ δ₂, W₂ (t * x.2) ∂τ₂ := by
  letI : MeasurableSpace (AutomorphicForm.sigmaCentralizer θ₁ δ₁) := borel _
  letI : MeasurableSpace (AutomorphicForm.sigmaCentralizer θ₂ δ₂) := borel _
  rw [integral_prodTorusMeasure]
  exact MeasureTheory.integral_prod_mul
    (fun s : AutomorphicForm.sigmaCentralizer θ₁ δ₁ => W₁ (s * x.1))
    (fun s : AutomorphicForm.sigmaCentralizer θ₂ δ₂ => W₂ (s * x.2))

end Topology

end GroupOrbital

end ProductTori

namespace GroupOrbital

section TorusHaar

variable {G₁ G₂ : Type} [Group G₁] [TopologicalSpace G₁] [IsTopologicalGroup G₁] [SecondCountableTopology G₁]
  [Group G₂] [TopologicalSpace G₂] [IsTopologicalGroup G₂] [SecondCountableTopology G₂]

omit [SecondCountableTopology G₁] in

theorem isHaarMeasure_prodTorusMeasure (θ₁ : G₁ →* G₁) (θ₂ : G₂ →* G₂) (δ₁ : G₁) (δ₂ : G₂)
    (τ₁ : @Measure (AutomorphicForm.sigmaCentralizer θ₁ δ₁) (borel _))
    (τ₂ : @Measure (AutomorphicForm.sigmaCentralizer θ₂ δ₂) (borel _))
    (h₁ : @Measure.IsHaarMeasure _ _ _ (borel _) τ₁) (h₂ : @Measure.IsHaarMeasure _ _ _ (borel _) τ₂)
    (s₁ : @SFinite _ (borel _) τ₁) (s₂ : @SFinite _ (borel _) τ₂) :
    @Measure.IsHaarMeasure _ _ _ (borel _) (prodTorusMeasure θ₁ θ₂ δ₁ δ₂ τ₁ τ₂) := by
  letI : MeasurableSpace (AutomorphicForm.sigmaCentralizer θ₁ δ₁) := borel _
  letI : MeasurableSpace (AutomorphicForm.sigmaCentralizer θ₂ δ₂) := borel _
  letI : MeasurableSpace (AutomorphicForm.sigmaCentralizer (θ₁.prodMap θ₂) (δ₁, δ₂)) := borel _
  haveI : BorelSpace (AutomorphicForm.sigmaCentralizer θ₁ δ₁) := ⟨rfl⟩
  haveI : BorelSpace (AutomorphicForm.sigmaCentralizer θ₂ δ₂) := ⟨rfl⟩
  haveI : BorelSpace (AutomorphicForm.sigmaCentralizer (θ₁.prodMap θ₂) (δ₁, δ₂)) := ⟨rfl⟩
  haveI : SecondCountableTopology (AutomorphicForm.sigmaCentralizer θ₂ δ₂) :=
    TopologicalSpace.secondCountableTopology_induced _ _ Subtype.val
  haveI : BorelSpace (AutomorphicForm.sigmaCentralizer θ₁ δ₁ × AutomorphicForm.sigmaCentralizer θ₂ δ₂) :=
    Prod.borelSpace
  haveI := h₁
  haveI := h₂
  haveI := s₁
  haveI := s₂
  exact ContinuousMulEquiv.isHaarMeasure_map (τ₁.prod τ₂) (prodTorusEquiv θ₁ θ₂ δ₁ δ₂)

end TorusHaar

end GroupOrbital

namespace GroupOrbital

section HaarFubini

variable {G₁ G₂ : Type} [Group G₁] [TopologicalSpace G₁] [IsTopologicalGroup G₁] [LocallyCompactSpace G₁]
  [SecondCountableTopology G₁] [T2Space G₁] [Group G₂] [TopologicalSpace G₂] [IsTopologicalGroup G₂]
  [LocallyCompactSpace G₂] [SecondCountableTopology G₂] [T2Space G₂]

omit [T2Space G₁] [T2Space G₂] in

theorem exists_integral_eq_mul_integral_integral (μ : @Measure (G₁ × G₂) (borel _))
    (hμ : @Measure.IsHaarMeasure (G₁ × G₂) _ _ (borel _) μ)
    (μ₁ : @Measure G₁ (borel _)) (h₁ : @Measure.IsHaarMeasure G₁ _ _ (borel _) μ₁)
    (μ₂ : @Measure G₂ (borel _)) (h₂ : @Measure.IsHaarMeasure G₂ _ _ (borel _) μ₂) :
    ∃ c : ℝ≥0, 0 < c ∧ ∀ h : G₁ × G₂ → ℂ, Continuous h → HasCompactSupport h →
      ∫ x, h x ∂μ = ((c : ℝ) : ℂ) * ∫ x₁, ∫ x₂, h (x₁, x₂) ∂μ₂ ∂μ₁ := by
  letI m₁ : MeasurableSpace G₁ := borel G₁
  letI m₂ : MeasurableSpace G₂ := borel G₂
  haveI : BorelSpace G₁ := ⟨rfl⟩
  haveI : BorelSpace G₂ := ⟨rfl⟩
  haveI := h₁
  haveI := h₂
  have hprod : (Prod.instMeasurableSpace : MeasurableSpace (G₁ × G₂)) = borel (G₁ × G₂) :=
    BorelSpace.measurable_eq
  revert μ
  rw [← hprod]
  intro μ hμ
  haveI := hμ
  refine ⟨μ.haarScalarFactor (μ₁.prod μ₂), Measure.haarScalarFactor_pos_of_isHaarMeasure _ _, fun h hc hs => ?_⟩
  have hμeq : μ = μ.haarScalarFactor (μ₁.prod μ₂) • μ₁.prod μ₂ :=
    Measure.isMulLeftInvariant_eq_smul μ (μ₁.prod μ₂)
  conv_lhs => rw [hμeq]
  rw [integral_smul_nnreal_measure, integral_prod _ (hc.integrable_of_hasCompactSupport hs)]
  show ((μ.haarScalarFactor (μ₁.prod μ₂) : ℝ)) • (∫ x₁, ∫ x₂, h (x₁, x₂) ∂μ₂ ∂μ₁ : ℂ) =
    ((μ.haarScalarFactor (μ₁.prod μ₂) : ℝ) : ℂ) * ∫ x₁, ∫ x₂, h (x₁, x₂) ∂μ₂ ∂μ₁
  rw [Complex.real_smul]

omit [T2Space G₁] [T2Space G₂] in

theorem integral_integral_swap_of_hasCompactSupport (μ₁ : @Measure G₁ (borel _))
    (h₁ : @Measure.IsHaarMeasure G₁ _ _ (borel _) μ₁) (μ₂ : @Measure G₂ (borel _))
    (h₂ : @Measure.IsHaarMeasure G₂ _ _ (borel _) μ₂) (h : G₁ × G₂ → ℂ) (hc : Continuous h)
    (hs : HasCompactSupport h) :
    ∫ x₁, ∫ x₂, h (x₁, x₂) ∂μ₂ ∂μ₁ = ∫ x₂, ∫ x₁, h (x₁, x₂) ∂μ₁ ∂μ₂ := by
  letI m₁ : MeasurableSpace G₁ := borel G₁
  letI m₂ : MeasurableSpace G₂ := borel G₂
  haveI : BorelSpace G₁ := ⟨rfl⟩
  haveI : BorelSpace G₂ := ⟨rfl⟩
  haveI := h₁
  haveI := h₂
  exact integral_integral_swap (hc.integrable_of_hasCompactSupport hs)

end HaarFubini

end GroupOrbital

namespace GroupOrbital

section NewFacts

open AutomorphicForm

variable {G₁ G₂ : Type} [Group G₁] [TopologicalSpace G₁] [IsTopologicalGroup G₁] [LocallyCompactSpace G₁]
  [SecondCountableTopology G₁] [T2Space G₁] [Group G₂] [TopologicalSpace G₂] [IsTopologicalGroup G₂]
  [LocallyCompactSpace G₂] [SecondCountableTopology G₂] [T2Space G₂]

omit [Group G₁] [Group G₂] [LocallyCompactSpace G₁] [LocallyCompactSpace G₂] [IsTopologicalGroup G₁]
  [IsTopologicalGroup G₂] [SecondCountableTopology G₁] [SecondCountableTopology G₂] in

theorem hasCompactSupport_prodWeights {W₁ : G₁ → ℝ} {W₂ : G₂ → ℝ} (hW₁s : HasCompactSupport W₁)
    (hW₂s : HasCompactSupport W₂) : HasCompactSupport fun x : G₁ × G₂ => W₁ x.1 * W₂ x.2 := by
  refine HasCompactSupport.intro (hW₁s.isCompact.prod hW₂s.isCompact) fun x hx => ?_
  simp only [Set.mem_prod, not_and_or] at hx
  rcases hx with h | h
  · simp [image_eq_zero_of_notMem_tsupport h]
  · simp [image_eq_zero_of_notMem_tsupport h]

omit [LocallyCompactSpace G₁] [T2Space G₁] [LocallyCompactSpace G₂] [T2Space G₂] [SecondCountableTopology G₁] in

theorem isInvInvariant_prodTorusMeasure (θ₁ : G₁ →* G₁) (θ₂ : G₂ →* G₂) (δ₁ : G₁) (δ₂ : G₂)
    (τ₁ : @Measure (sigmaCentralizer θ₁ δ₁) (borel _)) (τ₂ : @Measure (sigmaCentralizer θ₂ δ₂) (borel _))
    (s₁ : @SFinite _ (borel _) τ₁) (s₂ : @SFinite _ (borel _) τ₂)
    (i₁ : @Measure.IsInvInvariant _ (borel _) _ τ₁) (i₂ : @Measure.IsInvInvariant _ (borel _) _ τ₂) :
    @Measure.IsInvInvariant _ (borel _) _ (prodTorusMeasure θ₁ θ₂ δ₁ δ₂ τ₁ τ₂) := by
  letI : MeasurableSpace (sigmaCentralizer θ₁ δ₁) := borel _
  letI : MeasurableSpace (sigmaCentralizer θ₂ δ₂) := borel _
  letI : MeasurableSpace (sigmaCentralizer (θ₁.prodMap θ₂) (δ₁, δ₂)) := borel _
  haveI : BorelSpace (sigmaCentralizer θ₁ δ₁) := ⟨rfl⟩
  haveI : BorelSpace (sigmaCentralizer θ₂ δ₂) := ⟨rfl⟩
  haveI : BorelSpace (sigmaCentralizer (θ₁.prodMap θ₂) (δ₁, δ₂)) := ⟨rfl⟩
  haveI : SecondCountableTopology (sigmaCentralizer θ₂ δ₂) :=
    TopologicalSpace.secondCountableTopology_induced _ _ Subtype.val
  haveI : BorelSpace (sigmaCentralizer θ₁ δ₁ × sigmaCentralizer θ₂ δ₂) := Prod.borelSpace
  haveI := s₁; haveI := s₂; haveI := i₁; haveI := i₂
  have hem : Measurable (prodTorusEquiv θ₁ θ₂ δ₁ δ₂) := (prodTorusEquiv θ₁ θ₂ δ₁ δ₂).continuous.measurable
  refine ⟨?_⟩
  show Measure.map Inv.inv (Measure.map (prodTorusEquiv θ₁ θ₂ δ₁ δ₂) (τ₁.prod τ₂)) =
    Measure.map (prodTorusEquiv θ₁ θ₂ δ₁ δ₂) (τ₁.prod τ₂)
  rw [Measure.map_map measurable_inv hem]
  have hcomm : (Inv.inv ∘ prodTorusEquiv θ₁ θ₂ δ₁ δ₂) =
      prodTorusEquiv θ₁ θ₂ δ₁ δ₂ ∘ (fun p => (p.1⁻¹, p.2⁻¹)) := by
    funext p
    simp only [Function.comp_apply]
    rw [← Prod.inv_mk, ← map_inv]
  have hpm : Measurable (fun p : sigmaCentralizer θ₁ δ₁ × sigmaCentralizer θ₂ δ₂ => (p.1⁻¹, p.2⁻¹)) :=
    measurable_inv.prodMap measurable_inv
  rw [hcomm, ← Measure.map_map hem hpm]
  congr 1
  have : (fun p : sigmaCentralizer θ₁ δ₁ × sigmaCentralizer θ₂ δ₂ => (p.1⁻¹, p.2⁻¹)) =
      Prod.map (Inv.inv : sigmaCentralizer θ₁ δ₁ → _) (Inv.inv : sigmaCentralizer θ₂ δ₂ → _) := rfl
  rw [this, ← Measure.map_prod_map _ _ measurable_inv measurable_inv, Measure.map_inv_eq_self,
    Measure.map_inv_eq_self]

end NewFacts

end GroupOrbital

end S30TwistedFubini

open S30TwistedFubini in

theorem solution
    {G₁ G₂ : Type} [Group G₁] [TopologicalSpace G₁] [IsTopologicalGroup G₁] [LocallyCompactSpace G₁]
    [SecondCountableTopology G₁] [T2Space G₁]
    [Group G₂] [TopologicalSpace G₂] [IsTopologicalGroup G₂] [LocallyCompactSpace G₂]
    [SecondCountableTopology G₂] [T2Space G₂]
    (θ₁ : G₁ →* G₁) (hθ₁ : Continuous θ₁) (θ₂ : G₂ →* G₂) (hθ₂ : Continuous θ₂) (δ₁ : G₁) (δ₂ : G₂)
    (μ : @Measure (G₁ × G₂) (borel (G₁ × G₂))) (hμ : @Measure.IsHaarMeasure (G₁ × G₂) _ _ (borel _) μ)
    (μ₁ : @Measure G₁ (borel G₁)) (hμ₁ : @Measure.IsHaarMeasure G₁ _ _ (borel G₁) μ₁)
    (μ₂ : @Measure G₂ (borel G₂)) (hμ₂ : @Measure.IsHaarMeasure G₂ _ _ (borel G₂) μ₂)
    (τ₁ : @Measure (AutomorphicForm.sigmaCentralizer θ₁ δ₁) (borel _))
    (hτ₁ : @Measure.IsHaarMeasure _ _ _ (borel _) τ₁) (hτ₁i : @Measure.IsInvInvariant _ (borel _) _ τ₁)
    (τ₂ : @Measure (AutomorphicForm.sigmaCentralizer θ₂ δ₂) (borel _))
    (hτ₂ : @Measure.IsHaarMeasure _ _ _ (borel _) τ₂) (hτ₂i : @Measure.IsInvInvariant _ (borel _) _ τ₂)
    (e : AutomorphicForm.sigmaCentralizer θ₁ δ₁ × AutomorphicForm.sigmaCentralizer θ₂ δ₂ →
      AutomorphicForm.sigmaCentralizer (θ₁.prodMap θ₂) (δ₁, δ₂))
    (he : ∀ p, ((e p : AutomorphicForm.sigmaCentralizer (θ₁.prodMap θ₂) (δ₁, δ₂)) : G₁ × G₂) =
      ((p.1 : G₁), (p.2 : G₂))) :
    ∃ c : ℝ≥0, 0 < c ∧
      ∀ (f : G₁ × G₂ → ℂ), Continuous f → (∃ C : ℝ, ∀ x, ‖f x‖ ≤ C) →
      ∀ (W₁ : G₁ → ℝ) (W₂ : G₂ → ℝ), Continuous W₁ → (∀ x, 0 ≤ W₁ x) → HasCompactSupport W₁ →
        Continuous W₂ → (∀ x, 0 ≤ W₂ x) → HasCompactSupport W₂ →
        (∀ (x₁ : G₁) (x₂ : G₂), f (x₁⁻¹ * δ₁ * θ₁ x₁, x₂⁻¹ * δ₂ * θ₂ x₂) ≠ 0 →
          @integral _ ℝ _ _ (borel _) τ₁ (fun t => W₁ ((t : G₁) * x₁)) = 1 ∧
          @integral _ ℝ _ _ (borel _) τ₂ (fun t => W₂ ((t : G₂) * x₂)) = 1) →
        letI τ : @Measure (AutomorphicForm.sigmaCentralizer (θ₁.prodMap θ₂) (δ₁, δ₂)) (borel _) :=
          @Measure.map _ _ (@Prod.instMeasurableSpace _ _ (borel _) (borel _)) (borel _) e
            (@Measure.prod _ _ (borel _) (borel _) τ₁ τ₂)
        (∀ x : G₁ × G₂, f (x⁻¹ * (δ₁, δ₂) * (θ₁.prodMap θ₂) x) ≠ 0 →
            @integral _ ℝ _ _ (borel _) τ
              (fun t => W₁ (((t : G₁ × G₂) * x).1) * W₂ (((t : G₁ × G₂) * x).2)) = 1) ∧
        (∀ w : G₁ × G₂ → ℝ, (∀ x, 0 ≤ w x) → Measurable[borel (G₁ × G₂)] w → HasCompactSupport w →
          (∀ x : G₁ × G₂, f (x⁻¹ * (δ₁, δ₂) * (θ₁.prodMap θ₂) x) ≠ 0 →
            @integral _ ℝ _ _ (borel _) τ (fun t => w ((t : G₁ × G₂) * x)) = 1) →
          @integral _ ℂ _ _ (borel (G₁ × G₂)) μ (fun x => f (x⁻¹ * (δ₁, δ₂) * (θ₁.prodMap θ₂) x) * (w x : ℂ)) =
            ((c : ℝ) : ℂ) * @integral _ ℂ _ _ (borel G₁) μ₁ (fun x₁ => @integral _ ℂ _ _ (borel G₂) μ₂ (fun x₂ =>
              f (x₁⁻¹ * δ₁ * θ₁ x₁, x₂⁻¹ * δ₂ * θ₂ x₂) * ((W₁ x₁ * W₂ x₂ : ℝ) : ℂ)))) := by
  classical

  letI mG : MeasurableSpace (G₁ × G₂) := borel _
  haveI : BorelSpace (G₁ × G₂) := ⟨rfl⟩
  letI m₁ : MeasurableSpace G₁ := borel _
  haveI : BorelSpace G₁ := ⟨rfl⟩
  letI m₂ : MeasurableSpace G₂ := borel _
  haveI : BorelSpace G₂ := ⟨rfl⟩
  letI mT : MeasurableSpace (AutomorphicForm.sigmaCentralizer (θ₁.prodMap θ₂) (δ₁, δ₂)) := borel _
  haveI : BorelSpace (AutomorphicForm.sigmaCentralizer (θ₁.prodMap θ₂) (δ₁, δ₂)) := ⟨rfl⟩
  letI mT₁ : MeasurableSpace (AutomorphicForm.sigmaCentralizer θ₁ δ₁) := borel _
  haveI : BorelSpace (AutomorphicForm.sigmaCentralizer θ₁ δ₁) := ⟨rfl⟩
  letI mT₂ : MeasurableSpace (AutomorphicForm.sigmaCentralizer θ₂ δ₂) := borel _
  haveI : BorelSpace (AutomorphicForm.sigmaCentralizer θ₂ δ₂) := ⟨rfl⟩
  haveI := hμ; haveI := hμ₁; haveI := hμ₂; haveI := hτ₁; haveI := hτ₂; haveI := hτ₁i; haveI := hτ₂i

  obtain ⟨c, hc0, hc⟩ := GroupOrbital.exists_integral_eq_mul_integral_integral μ hμ μ₁ hμ₁ μ₂ hμ₂
  refine ⟨c, hc0, ?_⟩
  intro f hf hfb W₁ W₂ hW₁c hW₁0 hW₁s hW₂c hW₂0 hW₂s hn

  have he' : e = ⇑(GroupOrbital.prodTorusEquiv θ₁ θ₂ δ₁ δ₂) := by
    funext p
    apply Subtype.ext
    rw [he p]
    rfl
  have hτeq : @Measure.map _ _ (@Prod.instMeasurableSpace _ _ (borel _) (borel _)) (borel _) e
      (@Measure.prod _ _ (borel _) (borel _) τ₁ τ₂) = GroupOrbital.prodTorusMeasure θ₁ θ₂ δ₁ δ₂ τ₁ τ₂ := by
    rw [he']; rfl
  rw [hτeq]

  haveI : LocallyCompactSpace (AutomorphicForm.sigmaCentralizer θ₁ δ₁) :=
    (GroupOrbital.isClosed_sigmaCentralizer hθ₁ δ₁).locallyCompactSpace
  haveI : LocallyCompactSpace (AutomorphicForm.sigmaCentralizer θ₂ δ₂) :=
    (GroupOrbital.isClosed_sigmaCentralizer hθ₂ δ₂).locallyCompactSpace
  haveI : SecondCountableTopology (AutomorphicForm.sigmaCentralizer θ₁ δ₁) :=
    TopologicalSpace.secondCountableTopology_induced _ _ Subtype.val
  haveI : SecondCountableTopology (AutomorphicForm.sigmaCentralizer θ₂ δ₂) :=
    TopologicalSpace.secondCountableTopology_induced _ _ Subtype.val
  haveI s₁ : SFinite τ₁ := inferInstance
  haveI s₂ : SFinite τ₂ := inferInstance
  haveI : (GroupOrbital.prodTorusMeasure θ₁ θ₂ δ₁ δ₂ τ₁ τ₂).IsHaarMeasure :=
    GroupOrbital.isHaarMeasure_prodTorusMeasure θ₁ θ₂ δ₁ δ₂ τ₁ τ₂ hτ₁ hτ₂ s₁ s₂
  haveI : (GroupOrbital.prodTorusMeasure θ₁ θ₂ δ₁ δ₂ τ₁ τ₂).IsInvInvariant :=
    GroupOrbital.isInvInvariant_prodTorusMeasure θ₁ θ₂ δ₁ δ₂ τ₁ τ₂ s₁ s₂ hτ₁i hτ₂i
  have hθ : Continuous (θ₁.prodMap θ₂) := by
    rw [MonoidHom.coe_prodMap]
    exact hθ₁.prodMap hθ₂
  have hclosed := GroupOrbital.isClosed_sigmaCentralizer hθ (δ₁, δ₂)
  haveI : LocallyCompactSpace (AutomorphicForm.sigmaCentralizer (θ₁.prodMap θ₂) (δ₁, δ₂)) :=
    hclosed.locallyCompactSpace
  haveI : SecondCountableTopology (AutomorphicForm.sigmaCentralizer (θ₁.prodMap θ₂) (δ₁, δ₂)) :=
    TopologicalSpace.secondCountableTopology_induced _ _ Subtype.val

  have hsec : ∀ x : G₁ × G₂, f (x⁻¹ * (δ₁, δ₂) * (θ₁.prodMap θ₂) x) ≠ 0 →
      ∫ t, W₁ (((t : G₁ × G₂) * x).1) * W₂ (((t : G₁ × G₂) * x).2)
        ∂(GroupOrbital.prodTorusMeasure θ₁ θ₂ δ₁ δ₂ τ₁ τ₂) = 1 := by
    intro x hx
    have hx' : f (x.1⁻¹ * δ₁ * θ₁ x.1, x.2⁻¹ * δ₂ * θ₂ x.2) ≠ 0 := by
      obtain ⟨x₁, x₂⟩ := x
      simpa only [MonoidHom.coe_prodMap, Prod.map_apply, Prod.inv_mk, Prod.mk_mul_mk] using hx
    obtain ⟨h1, h2⟩ := hn x.1 x.2 hx'
    have key := GroupOrbital.integral_prodTorusMeasure_mul θ₁ θ₂ δ₁ δ₂ τ₁ τ₂ W₁ W₂ x
    simp only [Prod.fst_mul, Prod.snd_mul] at key ⊢
    rw [key, h1, h2, one_mul]
  refine ⟨hsec, ?_⟩

  intro w hw0 hwm hws hw1
  set F : G₁ × G₂ → ℂ := fun x => f (x⁻¹ * (δ₁, δ₂) * (θ₁.prodMap θ₂) x) with hF
  have hFc : Continuous F := hf.comp ((continuous_id.inv.mul continuous_const).mul hθ)
  have hFT : ∀ (t : AutomorphicForm.sigmaCentralizer (θ₁.prodMap θ₂) (δ₁, δ₂)) (x : G₁ × G₂),
      F ((t : G₁ × G₂) * x) = F x := by
    intro t x
    have key : ((t : G₁ × G₂))⁻¹ * (δ₁, δ₂) * (θ₁.prodMap θ₂) t = (δ₁, δ₂) :=
      AutomorphicForm.mem_sigmaCentralizer_iff_inv.1 t.2
    simp only [hF, mul_inv_rev, map_mul]
    rw [show x⁻¹ * (↑t)⁻¹ * (δ₁, δ₂) * ((θ₁.prodMap θ₂) ↑t * (θ₁.prodMap θ₂) x) =
      x⁻¹ * ((↑t)⁻¹ * (δ₁, δ₂) * (θ₁.prodMap θ₂) ↑t) * (θ₁.prodMap θ₂) x by simp only [mul_assoc], key]
  have hWm : Measurable fun x : G₁ × G₂ => W₁ x.1 * W₂ x.2 :=
    ((hW₁c.comp continuous_fst).mul (hW₂c.comp continuous_snd)).measurable
  have hswap := AutomorphicForm.integral_mul_eq_integral_mul_of_forall_integral_subgroup_mul_eq_one μ
    (AutomorphicForm.sigmaCentralizer (θ₁.prodMap θ₂) (δ₁, δ₂)) continuous_subtype_val.measurable
    (GroupOrbital.prodTorusMeasure θ₁ θ₂ δ₁ δ₂ τ₁ τ₂) F hFc.measurable hFT w
    (fun x => W₁ x.1 * W₂ x.2) hw0 (fun x => mul_nonneg (hW₁0 _) (hW₂0 _)) hwm hWm hw1
    (fun x hx => by
      have := hsec x hx
      simpa only [Prod.fst_mul, Prod.snd_mul] using this)
  rw [hswap]
  have hWc : Continuous fun x : G₁ × G₂ => ((W₁ x.1 * W₂ x.2 : ℝ) : ℂ) :=
    Complex.continuous_ofReal.comp ((hW₁c.comp continuous_fst).mul (hW₂c.comp continuous_snd))
  have hWs : HasCompactSupport fun x : G₁ × G₂ => ((W₁ x.1 * W₂ x.2 : ℝ) : ℂ) :=
    (GroupOrbital.hasCompactSupport_prodWeights hW₁s hW₂s).comp_left Complex.ofReal_zero
  have hcast : (fun x : G₁ × G₂ => F x * ((fun x : G₁ × G₂ => W₁ x.1 * W₂ x.2) x : ℂ)) =
      fun x => F x * ((W₁ x.1 * W₂ x.2 : ℝ) : ℂ) := by
    funext x; simp only [Complex.ofReal_mul]
  rw [hcast, hc (fun x => F x * ((W₁ x.1 * W₂ x.2 : ℝ) : ℂ)) (hFc.mul hWc) hWs.mul_left]
  congr 1

end S_AutomorphicForm_integral_twistedConj_prod_mul_eq_mul_integral_integral_of_sigmaCentralizer
end P2MW
export P2MW.S_AutomorphicForm_integral_twistedConj_prod_mul_eq_mul_integral_integral_of_sigmaCentralizer (solution)
