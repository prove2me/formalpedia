-- Prove2me | solution 1 for AutomorphicForm.exists_prod_eq_and_coupled_of_coupled_prod
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.961684+00:00
-- url     : https://prove2.me/submissions/a1344f76-db26-5391-bffe-c66b9aafeb64

import Mathlib
import Definitions.Def_AutomorphicForm_SigmaCentralizer
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_exists_prod_eq_and_coupled_of_coupled_prod

set_option autoImplicit false

open MeasureTheory Topology
open scoped NNReal ENNReal

namespace S30CoupledSplit

open AutomorphicForm

section Algebra

variable {G₁ G₂ : Type} [Group G₁] [Group G₂]

theorem mem_centralizer_prod_iff (γ₁ : G₁) (γ₂ : G₂) (t : G₁ × G₂) :
    t ∈ Subgroup.centralizer ({(γ₁, γ₂)} : Set (G₁ × G₂)) ↔
      t.1 ∈ Subgroup.centralizer ({γ₁} : Set G₁) ∧ t.2 ∈ Subgroup.centralizer ({γ₂} : Set G₂) := by
  obtain ⟨t₁, t₂⟩ := t
  simp only [Subgroup.mem_centralizer_singleton_iff, Prod.mk_mul_mk, Prod.mk.injEq]

theorem mem_sigmaCentralizer_prodMap_iff (θ₁ : G₁ →* G₁) (θ₂ : G₂ →* G₂) (δ₁ : G₁) (δ₂ : G₂) (t : G₁ × G₂) :
    t ∈ sigmaCentralizer (θ₁.prodMap θ₂) (δ₁, δ₂) ↔
      t.1 ∈ sigmaCentralizer θ₁ δ₁ ∧ t.2 ∈ sigmaCentralizer θ₂ δ₂ := by
  obtain ⟨t₁, t₂⟩ := t
  simp only [mem_sigmaCentralizer_iff, MonoidHom.coe_prodMap, Prod.map_apply, Prod.inv_mk,
    Prod.mk_mul_mk, Prod.mk.injEq]

def prodCentMulEquiv (γ₁ : G₁) (γ₂ : G₂) :
    Subgroup.centralizer ({γ₁} : Set G₁) × Subgroup.centralizer ({γ₂} : Set G₂) ≃*
      Subgroup.centralizer ({(γ₁, γ₂)} : Set (G₁ × G₂)) :=
  { toFun := fun t => ⟨((t.1 : G₁), (t.2 : G₂)), (mem_centralizer_prod_iff γ₁ γ₂ _).mpr ⟨t.1.2, t.2.2⟩⟩
    invFun := fun t =>
      (⟨(t : G₁ × G₂).1, ((mem_centralizer_prod_iff γ₁ γ₂ _).mp t.2).1⟩,
       ⟨(t : G₁ × G₂).2, ((mem_centralizer_prod_iff γ₁ γ₂ _).mp t.2).2⟩)
    left_inv := fun _ => rfl
    right_inv := fun _ => rfl
    map_mul' := fun _ _ => rfl }

def prodTorusMulEquiv (θ₁ : G₁ →* G₁) (θ₂ : G₂ →* G₂) (δ₁ : G₁) (δ₂ : G₂) :
    sigmaCentralizer θ₁ δ₁ × sigmaCentralizer θ₂ δ₂ ≃* sigmaCentralizer (θ₁.prodMap θ₂) (δ₁, δ₂) :=
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

def prodCentEquiv (γ₁ : G₁) (γ₂ : G₂) :
    Subgroup.centralizer ({γ₁} : Set G₁) × Subgroup.centralizer ({γ₂} : Set G₂) ≃ₜ*
      Subgroup.centralizer ({(γ₁, γ₂)} : Set (G₁ × G₂)) :=
  { toMulEquiv := prodCentMulEquiv γ₁ γ₂
    continuous_toFun :=
      ((continuous_subtype_val.comp continuous_fst).prodMk (continuous_subtype_val.comp continuous_snd)).subtype_mk _
    continuous_invFun :=
      ((continuous_fst.comp continuous_subtype_val).subtype_mk _).prodMk
        ((continuous_snd.comp continuous_subtype_val).subtype_mk _) }

theorem prodCentEquiv_apply_coe (γ₁ : G₁) (γ₂ : G₂)
    (t : Subgroup.centralizer ({γ₁} : Set G₁) × Subgroup.centralizer ({γ₂} : Set G₂)) :
    ((prodCentEquiv γ₁ γ₂ t : Subgroup.centralizer ({(γ₁, γ₂)} : Set (G₁ × G₂))) : G₁ × G₂) =
      ((t.1 : G₁), (t.2 : G₂)) := rfl

def prodTorusEquiv (θ₁ : G₁ →* G₁) (θ₂ : G₂ →* G₂) (δ₁ : G₁) (δ₂ : G₂) :
    sigmaCentralizer θ₁ δ₁ × sigmaCentralizer θ₂ δ₂ ≃ₜ* sigmaCentralizer (θ₁.prodMap θ₂) (δ₁, δ₂) :=
  { toMulEquiv := prodTorusMulEquiv θ₁ θ₂ δ₁ δ₂
    continuous_toFun :=
      ((continuous_subtype_val.comp continuous_fst).prodMk (continuous_subtype_val.comp continuous_snd)).subtype_mk _
    continuous_invFun :=
      ((continuous_fst.comp continuous_subtype_val).subtype_mk _).prodMk
        ((continuous_snd.comp continuous_subtype_val).subtype_mk _) }

theorem prodTorusEquiv_apply_coe (θ₁ : G₁ →* G₁) (θ₂ : G₂ →* G₂) (δ₁ : G₁) (δ₂ : G₂)
    (t : sigmaCentralizer θ₁ δ₁ × sigmaCentralizer θ₂ δ₂) :
    ((prodTorusEquiv θ₁ θ₂ δ₁ δ₂ t : sigmaCentralizer (θ₁.prodMap θ₂) (δ₁, δ₂)) : G₁ × G₂) =
      ((t.1 : G₁), (t.2 : G₂)) := rfl

theorem isClosed_sigmaCentralizer {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [T2Space G]
    {θ : G →* G} (hθ : Continuous θ) (δ : G) :
    IsClosed (sigmaCentralizer θ δ : Set G) := by
  have h : (sigmaCentralizer θ δ : Set G) = (fun t => t * δ * (θ t)⁻¹) ⁻¹' {δ} := by
    ext t
    simp only [SetLike.mem_coe, mem_sigmaCentralizer_iff, Set.mem_preimage, Set.mem_singleton_iff]
  rw [h]
  exact IsClosed.preimage ((continuous_id.mul continuous_const).mul hθ.inv) isClosed_singleton

theorem isClosed_centralizer {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [T2Space G]
    (γ : G) : IsClosed (Subgroup.centralizer ({γ} : Set G) : Set G) := by
  have h : (Subgroup.centralizer ({γ} : Set G) : Set G) = {x | x * γ = γ * x} := by
    ext x; exact Subgroup.mem_centralizer_singleton_iff
  rw [h]
  exact isClosed_eq (continuous_id.mul continuous_const) (continuous_const.mul continuous_id)

end Topology

section Range

variable {S S' X : Type} [TopologicalSpace S] [MeasurableSpace S] [TopologicalSpace S'] [MeasurableSpace S']
  [TopologicalSpace X] [MeasurableSpace X] [BorelSpace X]

omit [TopologicalSpace S'] in

theorem range_subset_of_map_eq (j : S → X) (ψ : S' → X) (hj : Continuous j) (hjm : Measurable j)
    (hψm : Measurable ψ) (hψr : IsClosed (Set.range ψ))
    (τ : Measure S) [τ.IsOpenPosMeasure] (τ' : Measure S')
    (h : Measure.map j τ = Measure.map ψ τ') : Set.range j ⊆ Set.range ψ := by
  rintro x ⟨s, rfl⟩
  by_contra hx
  have hU : IsOpen (Set.range ψ)ᶜ := hψr.isOpen_compl
  have hpos : 0 < τ (j ⁻¹' (Set.range ψ)ᶜ) :=
    (hU.preimage hj).measure_pos τ ⟨s, hx⟩
  have h1 : Measure.map j τ ((Set.range ψ)ᶜ) = τ (j ⁻¹' (Set.range ψ)ᶜ) := Measure.map_apply hjm hU.measurableSet
  have h2 : Measure.map ψ τ' ((Set.range ψ)ᶜ) = 0 := by
    rw [Measure.map_apply hψm hU.measurableSet]
    have : ψ ⁻¹' (Set.range ψ)ᶜ = ∅ := by
      ext s'; simp
    rw [this, measure_empty]
  rw [h, h2] at h1
  exact absurd h1.symm hpos.ne'

end Range

end S30CoupledSplit

namespace S30CoupledSplit

open AutomorphicForm

section Corr

variable {G H : Type} [Group G] [TopologicalSpace G]
  [Group H] [TopologicalSpace H] [IsTopologicalGroup H]

omit [TopologicalSpace G] [TopologicalSpace H] [IsTopologicalGroup H] in

def corrHom (φ : G →* H) (C : Subgroup G) (T : Subgroup H) (y : H)
    (hCT : ∀ s ∈ C, y * φ s * y⁻¹ ∈ T) : C →* T where
  toFun s := ⟨y * φ s * y⁻¹, hCT s s.2⟩
  map_one' := Subtype.ext (by simp)
  map_mul' a b := Subtype.ext (by
    simp only [Subgroup.coe_mul, map_mul]
    group)

omit [TopologicalSpace G] [TopologicalSpace H] [IsTopologicalGroup H] in
theorem corrHom_apply_coe (φ : G →* H) (C : Subgroup G) (T : Subgroup H) (y : H)
    (hCT : ∀ s ∈ C, y * φ s * y⁻¹ ∈ T) (s : C) : ((corrHom φ C T y hCT s : T) : H) = y * φ s * y⁻¹ := rfl

omit [TopologicalSpace G] [TopologicalSpace H] [IsTopologicalGroup H] in
theorem corrHom_bijective (φ : G →* H) (hφ : Function.Injective φ) (C : Subgroup G) (T : Subgroup H) (y : H)
    (hCT : ∀ s ∈ C, y * φ s * y⁻¹ ∈ T) (hTC : ∀ t ∈ T, ∃ s ∈ C, φ s = y⁻¹ * t * y) :
    Function.Bijective (corrHom φ C T y hCT) := by
  refine ⟨fun a b hab => ?_, fun t => ?_⟩
  · have h := congrArg (fun u : T => (u : H)) hab
    simp only [corrHom_apply_coe, mul_left_inj, mul_right_inj] at h
    exact Subtype.ext (hφ h)
  · obtain ⟨s, hs, hst⟩ := hTC t t.2
    refine ⟨⟨s, hs⟩, Subtype.ext ?_⟩
    rw [corrHom_apply_coe]
    show y * φ s * y⁻¹ = t
    rw [hst]; group

noncomputable def corrEquiv (φ : G →* H) (hφ : IsClosedEmbedding φ) (C : Subgroup G) (T : Subgroup H) (y : H)
    (hCT : ∀ s ∈ C, y * φ s * y⁻¹ ∈ T) (hTC : ∀ t ∈ T, ∃ s ∈ C, φ s = y⁻¹ * t * y) : C ≃ₜ* T :=
  { MulEquiv.ofBijective (corrHom φ C T y hCT) (corrHom_bijective φ hφ.injective C T y hCT hTC) with
    continuous_toFun := by
      show Continuous (corrHom φ C T y hCT)
      exact ((continuous_const.mul (hφ.continuous.comp continuous_subtype_val)).mul continuous_const).subtype_mk _
    continuous_invFun := by
      set E := MulEquiv.ofBijective (corrHom φ C T y hCT) (corrHom_bijective φ hφ.injective C T y hCT hTC)
      show Continuous E.symm
      have hemb : IsEmbedding (fun s : C => φ (s : G)) :=
        hφ.isEmbedding.comp IsEmbedding.subtypeVal
      rw [hemb.continuous_iff]
      have hid : (fun s : C => φ (s : G)) ∘ E.symm = fun t : T => y⁻¹ * (t : H) * y := by
        funext t
        simp only [Function.comp_apply]
        have ht : ((E (E.symm t) : T) : H) = (t : H) := by rw [MulEquiv.apply_symm_apply]
        rw [show ((E (E.symm t) : T) : H) = y * φ (E.symm t : G) * y⁻¹ from rfl] at ht
        rw [← ht]; group
      rw [hid]
      exact (continuous_const.mul continuous_subtype_val).mul continuous_const }

theorem corrEquiv_apply_coe (φ : G →* H) (hφ : IsClosedEmbedding φ) (C : Subgroup G) (T : Subgroup H) (y : H)
    (hCT : ∀ s ∈ C, y * φ s * y⁻¹ ∈ T) (hTC : ∀ t ∈ T, ∃ s ∈ C, φ s = y⁻¹ * t * y) (s : C) :
    ((corrEquiv φ hφ C T y hCT hTC s : T) : H) = y * φ s * y⁻¹ := rfl

end Corr

section HaarProd

variable {C₁ C₂ C : Type} [Group C₁] [TopologicalSpace C₁] [IsTopologicalGroup C₁] [LocallyCompactSpace C₁]
  [SecondCountableTopology C₁] [MeasurableSpace C₁] [BorelSpace C₁]
  [Group C₂] [TopologicalSpace C₂] [IsTopologicalGroup C₂] [LocallyCompactSpace C₂]
  [SecondCountableTopology C₂] [MeasurableSpace C₂] [BorelSpace C₂]
  [Group C] [TopologicalSpace C] [IsTopologicalGroup C] [LocallyCompactSpace C]
  [SecondCountableTopology C] [MeasurableSpace C] [BorelSpace C]

theorem exists_isHaarMeasure_prod_eq (e : C₁ × C₂ ≃ₜ* C) (τ : Measure C) [τ.IsHaarMeasure] :
    ∃ (τ₁ : Measure C₁) (τ₂ : Measure C₂), τ₁.IsHaarMeasure ∧ τ₂.IsHaarMeasure ∧
      τ = Measure.map e (τ₁.prod τ₂) := by
  haveI : BorelSpace (C₁ × C₂) := Prod.borelSpace
  set ν : Measure C := Measure.map e ((Measure.haar : Measure C₁).prod (Measure.haar : Measure C₂)) with hν
  haveI : ((Measure.haar : Measure C₁).prod (Measure.haar : Measure C₂)).IsHaarMeasure := inferInstance
  haveI hνH : ν.IsHaarMeasure := by rw [hν]; exact e.isHaarMeasure_map _
  set s : ℝ≥0 := τ.haarScalarFactor ν with hs
  have hs0 : s ≠ 0 := (Measure.haarScalarFactor_pos_of_isHaarMeasure τ ν).ne'
  have hτ : τ = s • ν := Measure.isMulLeftInvariant_eq_smul τ ν
  refine ⟨(s : ℝ≥0∞) • Measure.haar, Measure.haar, ?_, inferInstance, ?_⟩
  · exact Measure.IsHaarMeasure.smul _ (by exact_mod_cast hs0) ENNReal.coe_ne_top
  · rw [Measure.prod_smul_left, Measure.map_smul, ← hν, hτ]
    rfl

end HaarProd

theorem eq_of_map_eq_of_measurableEmbedding {S X : Type} [MeasurableSpace S] [MeasurableSpace X] {f : S → X}
    (hf : MeasurableEmbedding f) {μ ν : Measure S} (h : Measure.map f μ = Measure.map f ν) : μ = ν := by
  rw [← hf.comap_map μ, ← hf.comap_map ν, h]

end S30CoupledSplit

open S30CoupledSplit AutomorphicForm Topology in

theorem solution
    {G₁ G₂ H₁ H₂ : Type}
    [Group G₁] [TopologicalSpace G₁] [IsTopologicalGroup G₁] [LocallyCompactSpace G₁]
    [SecondCountableTopology G₁] [T2Space G₁]
    [Group G₂] [TopologicalSpace G₂] [IsTopologicalGroup G₂] [LocallyCompactSpace G₂]
    [SecondCountableTopology G₂] [T2Space G₂]
    [Group H₁] [TopologicalSpace H₁] [IsTopologicalGroup H₁] [LocallyCompactSpace H₁]
    [SecondCountableTopology H₁] [T2Space H₁]
    [Group H₂] [TopologicalSpace H₂] [IsTopologicalGroup H₂] [LocallyCompactSpace H₂]
    [SecondCountableTopology H₂] [T2Space H₂]
    (φ₁ : G₁ →* H₁) (hφ₁ : Topology.IsClosedEmbedding φ₁) (φ₂ : G₂ →* H₂) (hφ₂ : Topology.IsClosedEmbedding φ₂)
    (η₁ : H₁ →* H₁) (hη₁ : Continuous η₁) (η₂ : H₂ →* H₂) (hη₂ : Continuous η₂)
    (γ₁ : G₁) (γ₂ : G₂) (δ₁ y₁ : H₁) (δ₂ y₂ : H₂)
    (eC : Subgroup.centralizer ({γ₁} : Set G₁) × Subgroup.centralizer ({γ₂} : Set G₂) →
      Subgroup.centralizer ({(γ₁, γ₂)} : Set (G₁ × G₂)))
    (heC : ∀ p, ((eC p : Subgroup.centralizer ({(γ₁, γ₂)} : Set (G₁ × G₂))) : G₁ × G₂) =
      ((p.1 : G₁), (p.2 : G₂)))
    (eT : AutomorphicForm.sigmaCentralizer η₁ δ₁ × AutomorphicForm.sigmaCentralizer η₂ δ₂ →
      AutomorphicForm.sigmaCentralizer (η₁.prodMap η₂) (δ₁, δ₂))
    (heT : ∀ p, ((eT p : AutomorphicForm.sigmaCentralizer (η₁.prodMap η₂) (δ₁, δ₂)) : H₁ × H₂) =
      ((p.1 : H₁), (p.2 : H₂)))
    (τ : @Measure (Subgroup.centralizer ({(γ₁, γ₂)} : Set (G₁ × G₂))) (borel _))
    (hτ : @Measure.IsHaarMeasure _ _ _ (borel _) τ)
    (τ' : @Measure (AutomorphicForm.sigmaCentralizer (η₁.prodMap η₂) (δ₁, δ₂)) (borel _))
    (hτ' : @Measure.IsHaarMeasure _ _ _ (borel _) τ')
    (hcpl : @Measure.map _ _ (borel _) (borel (H₁ × H₂))
        (fun t : AutomorphicForm.sigmaCentralizer (η₁.prodMap η₂) (δ₁, δ₂) =>
          (y₁, y₂)⁻¹ * (t : H₁ × H₂) * (y₁, y₂)) τ' =
      @Measure.map _ _ (borel _) (borel (H₁ × H₂))
        (fun s : Subgroup.centralizer ({(γ₁, γ₂)} : Set (G₁ × G₂)) => (φ₁.prodMap φ₂) (s : G₁ × G₂)) τ) :
    ∃ (τ₁ : @Measure (Subgroup.centralizer ({γ₁} : Set G₁)) (borel _))
      (τ₂ : @Measure (Subgroup.centralizer ({γ₂} : Set G₂)) (borel _))
      (τ₁' : @Measure (AutomorphicForm.sigmaCentralizer η₁ δ₁) (borel _))
      (τ₂' : @Measure (AutomorphicForm.sigmaCentralizer η₂ δ₂) (borel _)),
      @Measure.IsHaarMeasure _ _ _ (borel _) τ₁ ∧ @Measure.IsHaarMeasure _ _ _ (borel _) τ₂ ∧
      @Measure.IsHaarMeasure _ _ _ (borel _) τ₁' ∧ @Measure.IsHaarMeasure _ _ _ (borel _) τ₂' ∧
      τ = @Measure.map _ _ (@Prod.instMeasurableSpace _ _ (borel _) (borel _)) (borel _) eC
            (@Measure.prod _ _ (borel _) (borel _) τ₁ τ₂) ∧
      τ' = @Measure.map _ _ (@Prod.instMeasurableSpace _ _ (borel _) (borel _)) (borel _) eT
            (@Measure.prod _ _ (borel _) (borel _) τ₁' τ₂') ∧
      @Measure.map _ _ (borel _) (borel H₁)
          (fun t : AutomorphicForm.sigmaCentralizer η₁ δ₁ => y₁⁻¹ * (t : H₁) * y₁) τ₁' =
        @Measure.map _ _ (borel _) (borel H₁)
          (fun s : Subgroup.centralizer ({γ₁} : Set G₁) => φ₁ (s : G₁)) τ₁ ∧
      @Measure.map _ _ (borel _) (borel H₂)
          (fun t : AutomorphicForm.sigmaCentralizer η₂ δ₂ => y₂⁻¹ * (t : H₂) * y₂) τ₂' =
        @Measure.map _ _ (borel _) (borel H₂)
          (fun s : Subgroup.centralizer ({γ₂} : Set G₂) => φ₂ (s : G₂)) τ₂ := by
  classical

  letI mG₁ : MeasurableSpace G₁ := borel _; haveI : BorelSpace G₁ := ⟨rfl⟩
  letI mG₂ : MeasurableSpace G₂ := borel _; haveI : BorelSpace G₂ := ⟨rfl⟩
  letI mH₁ : MeasurableSpace H₁ := borel _; haveI : BorelSpace H₁ := ⟨rfl⟩
  letI mH₂ : MeasurableSpace H₂ := borel _; haveI : BorelSpace H₂ := ⟨rfl⟩
  letI mH : MeasurableSpace (H₁ × H₂) := borel _; haveI : BorelSpace (H₁ × H₂) := ⟨rfl⟩
  letI mG : MeasurableSpace (G₁ × G₂) := borel _; haveI : BorelSpace (G₁ × G₂) := ⟨rfl⟩
  letI mC₁ : MeasurableSpace (Subgroup.centralizer ({γ₁} : Set G₁)) := borel _; haveI : BorelSpace (Subgroup.centralizer ({γ₁} : Set G₁)) := ⟨rfl⟩
  letI mC₂ : MeasurableSpace (Subgroup.centralizer ({γ₂} : Set G₂)) := borel _; haveI : BorelSpace (Subgroup.centralizer ({γ₂} : Set G₂)) := ⟨rfl⟩
  letI mC : MeasurableSpace (Subgroup.centralizer ({(γ₁, γ₂)} : Set (G₁ × G₂))) := borel _; haveI : BorelSpace (Subgroup.centralizer ({(γ₁, γ₂)} : Set (G₁ × G₂))) := ⟨rfl⟩
  letI mT₁ : MeasurableSpace (sigmaCentralizer η₁ δ₁) := borel _; haveI : BorelSpace (sigmaCentralizer η₁ δ₁) := ⟨rfl⟩
  letI mT₂ : MeasurableSpace (sigmaCentralizer η₂ δ₂) := borel _; haveI : BorelSpace (sigmaCentralizer η₂ δ₂) := ⟨rfl⟩
  letI mT : MeasurableSpace (sigmaCentralizer (η₁.prodMap η₂) (δ₁, δ₂)) := borel _; haveI : BorelSpace (sigmaCentralizer (η₁.prodMap η₂) (δ₁, δ₂)) := ⟨rfl⟩
  haveI := hτ; haveI := hτ'

  have hη : Continuous (η₁.prodMap η₂) := by rw [MonoidHom.coe_prodMap]; exact hη₁.prodMap hη₂
  have hC₁c : IsClosed ((Subgroup.centralizer ({γ₁} : Set G₁)) : Set G₁) := isClosed_centralizer γ₁
  have hC₂c : IsClosed ((Subgroup.centralizer ({γ₂} : Set G₂)) : Set G₂) := isClosed_centralizer γ₂
  have hCc : IsClosed ((Subgroup.centralizer ({(γ₁, γ₂)} : Set (G₁ × G₂))) : Set (G₁ × G₂)) := isClosed_centralizer (γ₁, γ₂)
  have hT₁c : IsClosed ((sigmaCentralizer η₁ δ₁) : Set H₁) := isClosed_sigmaCentralizer hη₁ δ₁
  have hT₂c : IsClosed ((sigmaCentralizer η₂ δ₂) : Set H₂) := isClosed_sigmaCentralizer hη₂ δ₂
  have hTc : IsClosed ((sigmaCentralizer (η₁.prodMap η₂) (δ₁, δ₂)) : Set (H₁ × H₂)) := isClosed_sigmaCentralizer hη (δ₁, δ₂)
  haveI : LocallyCompactSpace (Subgroup.centralizer ({γ₁} : Set G₁)) := hC₁c.locallyCompactSpace
  haveI : LocallyCompactSpace (Subgroup.centralizer ({γ₂} : Set G₂)) := hC₂c.locallyCompactSpace
  haveI : LocallyCompactSpace (Subgroup.centralizer ({(γ₁, γ₂)} : Set (G₁ × G₂))) := hCc.locallyCompactSpace
  haveI : LocallyCompactSpace (sigmaCentralizer η₁ δ₁) := hT₁c.locallyCompactSpace
  haveI : LocallyCompactSpace (sigmaCentralizer η₂ δ₂) := hT₂c.locallyCompactSpace
  haveI : LocallyCompactSpace (sigmaCentralizer (η₁.prodMap η₂) (δ₁, δ₂)) := hTc.locallyCompactSpace
  haveI : SecondCountableTopology (Subgroup.centralizer ({γ₁} : Set G₁)) := TopologicalSpace.secondCountableTopology_induced _ _ Subtype.val
  haveI : SecondCountableTopology (Subgroup.centralizer ({γ₂} : Set G₂)) := TopologicalSpace.secondCountableTopology_induced _ _ Subtype.val
  haveI : SecondCountableTopology (Subgroup.centralizer ({(γ₁, γ₂)} : Set (G₁ × G₂))) := TopologicalSpace.secondCountableTopology_induced _ _ Subtype.val
  haveI : SecondCountableTopology (sigmaCentralizer η₁ δ₁) := TopologicalSpace.secondCountableTopology_induced _ _ Subtype.val
  haveI : SecondCountableTopology (sigmaCentralizer η₂ δ₂) := TopologicalSpace.secondCountableTopology_induced _ _ Subtype.val
  haveI : SecondCountableTopology (sigmaCentralizer (η₁.prodMap η₂) (δ₁, δ₂)) := TopologicalSpace.secondCountableTopology_induced _ _ Subtype.val
  haveI : BorelSpace ((Subgroup.centralizer ({γ₁} : Set G₁)) × (Subgroup.centralizer ({γ₂} : Set G₂))) := Prod.borelSpace
  haveI : BorelSpace ((sigmaCentralizer η₁ δ₁) × (sigmaCentralizer η₂ δ₂)) := Prod.borelSpace

  have heC' : eC = ⇑(prodCentEquiv γ₁ γ₂) := by
    funext p; apply Subtype.ext; rw [heC p]; rfl
  have heT' : eT = ⇑(prodTorusEquiv η₁ η₂ δ₁ δ₂) := by
    funext p; apply Subtype.ext; rw [heT p]; rfl

  have hφ : IsClosedEmbedding (φ₁.prodMap φ₂) := by
    rw [MonoidHom.coe_prodMap]; exact hφ₁.prodMap hφ₂
  let j : (sigmaCentralizer (η₁.prodMap η₂) (δ₁, δ₂)) → H₁ × H₂ := fun t => (y₁, y₂)⁻¹ * (t : H₁ × H₂) * (y₁, y₂)
  let ψ : (Subgroup.centralizer ({(γ₁, γ₂)} : Set (G₁ × G₂))) → H₁ × H₂ := fun s => (φ₁.prodMap φ₂) (s : G₁ × G₂)
  have hjc : Continuous j := (continuous_const.mul continuous_subtype_val).mul continuous_const
  have hψc : Continuous ψ := hφ.continuous.comp continuous_subtype_val
  have hjr : IsClosed (Set.range j) := by
    have : Set.range j = ((Homeomorph.mulRight (y₁, y₂)).trans (Homeomorph.mulLeft (y₁, y₂)⁻¹)) ''
        ((sigmaCentralizer (η₁.prodMap η₂) (δ₁, δ₂)) : Set (H₁ × H₂)) := by
      ext z
      simp only [Set.mem_range, Set.mem_image, Homeomorph.trans_apply, Homeomorph.coe_mulLeft,
        Homeomorph.coe_mulRight, SetLike.mem_coe]
      constructor
      · rintro ⟨t, rfl⟩; exact ⟨t, t.2, by simp only [j]; group⟩
      · rintro ⟨t, ht, rfl⟩; exact ⟨⟨t, ht⟩, by simp only [j]; group⟩
    rw [this]
    exact (Homeomorph.isClosedMap _) _ hTc
  have hψr : IsClosed (Set.range ψ) := by
    have : Set.range ψ = (φ₁.prodMap φ₂) '' ((Subgroup.centralizer ({(γ₁, γ₂)} : Set (G₁ × G₂))) : Set (G₁ × G₂)) := by
      ext z; simp only [Set.mem_range, Set.mem_image, SetLike.mem_coe]
      constructor
      · rintro ⟨s, rfl⟩; exact ⟨s, s.2, rfl⟩
      · rintro ⟨s, hs, rfl⟩; exact ⟨⟨s, hs⟩, rfl⟩
    rw [this]
    exact hφ.isClosedMap _ hCc
  have hcpl' : Measure.map j τ' = Measure.map ψ τ := hcpl
  have hTC : Set.range j ⊆ Set.range ψ :=
    range_subset_of_map_eq j ψ hjc hjc.measurable hψc.measurable hψr τ' τ hcpl'
  have hCT : Set.range ψ ⊆ Set.range j :=
    range_subset_of_map_eq ψ j hψc hψc.measurable hjc.measurable hjr τ τ' hcpl'.symm

  have hCT₁ : ∀ s ∈ (Subgroup.centralizer ({γ₁} : Set G₁)), y₁ * φ₁ s * y₁⁻¹ ∈ (sigmaCentralizer η₁ δ₁) := by
    intro s hs
    have hmem : ((s, (1 : G₂)) : G₁ × G₂) ∈ (Subgroup.centralizer ({(γ₁, γ₂)} : Set (G₁ × G₂))) := (mem_centralizer_prod_iff γ₁ γ₂ _).2 ⟨hs, one_mem _⟩
    obtain ⟨t, ht⟩ := hCT ⟨⟨(s, 1), hmem⟩, rfl⟩
    have ht' : (t : H₁ × H₂) = (y₁, y₂) * (φ₁ s, φ₂ 1) * (y₁, y₂)⁻¹ := by
      have : (y₁, y₂)⁻¹ * (t : H₁ × H₂) * (y₁, y₂) = (φ₁ s, φ₂ 1) := ht
      rw [← this]; group
    have h1 := ((mem_sigmaCentralizer_prodMap_iff η₁ η₂ δ₁ δ₂ (t : H₁ × H₂)).1 t.2).1
    rw [ht'] at h1
    simpa using h1
  have hTC₁ : ∀ t ∈ (sigmaCentralizer η₁ δ₁), ∃ s ∈ (Subgroup.centralizer ({γ₁} : Set G₁)), φ₁ s = y₁⁻¹ * t * y₁ := by
    intro t ht
    have hmem : ((t, (1 : H₂)) : H₁ × H₂) ∈ (sigmaCentralizer (η₁.prodMap η₂) (δ₁, δ₂)) :=
      (mem_sigmaCentralizer_prodMap_iff η₁ η₂ δ₁ δ₂ _).2 ⟨ht, one_mem _⟩
    obtain ⟨s, hs⟩ := hTC ⟨⟨(t, 1), hmem⟩, rfl⟩
    refine ⟨(s : G₁ × G₂).1, ((mem_centralizer_prod_iff γ₁ γ₂ _).1 s.2).1, ?_⟩
    have := congrArg Prod.fst hs
    simpa [j, ψ] using this
  have hCT₂ : ∀ s ∈ (Subgroup.centralizer ({γ₂} : Set G₂)), y₂ * φ₂ s * y₂⁻¹ ∈ (sigmaCentralizer η₂ δ₂) := by
    intro s hs
    have hmem : (((1 : G₁), s) : G₁ × G₂) ∈ (Subgroup.centralizer ({(γ₁, γ₂)} : Set (G₁ × G₂))) := (mem_centralizer_prod_iff γ₁ γ₂ _).2 ⟨one_mem _, hs⟩
    obtain ⟨t, ht⟩ := hCT ⟨⟨(1, s), hmem⟩, rfl⟩
    have ht' : (t : H₁ × H₂) = (y₁, y₂) * (φ₁ 1, φ₂ s) * (y₁, y₂)⁻¹ := by
      have : (y₁, y₂)⁻¹ * (t : H₁ × H₂) * (y₁, y₂) = (φ₁ 1, φ₂ s) := ht
      rw [← this]; group
    have h2 := ((mem_sigmaCentralizer_prodMap_iff η₁ η₂ δ₁ δ₂ (t : H₁ × H₂)).1 t.2).2
    rw [ht'] at h2
    simpa using h2
  have hTC₂ : ∀ t ∈ (sigmaCentralizer η₂ δ₂), ∃ s ∈ (Subgroup.centralizer ({γ₂} : Set G₂)), φ₂ s = y₂⁻¹ * t * y₂ := by
    intro t ht
    have hmem : (((1 : H₁), t) : H₁ × H₂) ∈ (sigmaCentralizer (η₁.prodMap η₂) (δ₁, δ₂)) :=
      (mem_sigmaCentralizer_prodMap_iff η₁ η₂ δ₁ δ₂ _).2 ⟨one_mem _, ht⟩
    obtain ⟨s, hs⟩ := hTC ⟨⟨(1, t), hmem⟩, rfl⟩
    refine ⟨(s : G₁ × G₂).2, ((mem_centralizer_prod_iff γ₁ γ₂ _).1 s.2).2, ?_⟩
    have := congrArg Prod.snd hs
    simpa [j, ψ] using this

  let κ₁ := corrEquiv φ₁ hφ₁ (Subgroup.centralizer ({γ₁} : Set G₁)) (sigmaCentralizer η₁ δ₁) y₁ hCT₁ hTC₁
  let κ₂ := corrEquiv φ₂ hφ₂ (Subgroup.centralizer ({γ₂} : Set G₂)) (sigmaCentralizer η₂ δ₂) y₂ hCT₂ hTC₂
  have hκ₁v : ∀ s, ((κ₁ s : (sigmaCentralizer η₁ δ₁)) : H₁) = y₁ * φ₁ s * y₁⁻¹ := fun s => rfl
  have hκ₂v : ∀ s, ((κ₂ s : (sigmaCentralizer η₂ δ₂)) : H₂) = y₂ * φ₂ s * y₂⁻¹ := fun s => rfl

  obtain ⟨τ₁, τ₂, hτ₁, hτ₂, hτeq⟩ := exists_isHaarMeasure_prod_eq (prodCentEquiv γ₁ γ₂) τ
  haveI := hτ₁; haveI := hτ₂

  haveI hτ₁'H : (Measure.map κ₁ τ₁).IsHaarMeasure := κ₁.isHaarMeasure_map τ₁
  haveI hτ₂'H : (Measure.map κ₂ τ₂).IsHaarMeasure := κ₂.isHaarMeasure_map τ₂
  have hκ₁m : Measurable (κ₁ : (Subgroup.centralizer ({γ₁} : Set G₁)) → (sigmaCentralizer η₁ δ₁)) := κ₁.continuous.measurable
  have hκ₂m : Measurable (κ₂ : (Subgroup.centralizer ({γ₂} : Set G₂)) → (sigmaCentralizer η₂ δ₂)) := κ₂.continuous.measurable
  have hm₁ : Measurable (fun t : (sigmaCentralizer η₁ δ₁) => y₁⁻¹ * (t : H₁) * y₁) :=
    ((continuous_const.mul continuous_subtype_val).mul continuous_const).measurable
  have hm₂ : Measurable (fun t : (sigmaCentralizer η₂ δ₂) => y₂⁻¹ * (t : H₂) * y₂) :=
    ((continuous_const.mul continuous_subtype_val).mul continuous_const).measurable
  have hc₁ : Measure.map (fun t : (sigmaCentralizer η₁ δ₁) => y₁⁻¹ * (t : H₁) * y₁) (Measure.map κ₁ τ₁) =
      Measure.map (fun s : (Subgroup.centralizer ({γ₁} : Set G₁)) => φ₁ (s : G₁)) τ₁ := by
    rw [Measure.map_map hm₁ hκ₁m]
    congr 1
    funext s
    simp only [Function.comp_apply, hκ₁v]
    group
  have hc₂ : Measure.map (fun t : (sigmaCentralizer η₂ δ₂) => y₂⁻¹ * (t : H₂) * y₂) (Measure.map κ₂ τ₂) =
      Measure.map (fun s : (Subgroup.centralizer ({γ₂} : Set G₂)) => φ₂ (s : G₂)) τ₂ := by
    rw [Measure.map_map hm₂ hκ₂m]
    congr 1
    funext s
    simp only [Function.comp_apply, hκ₂v]
    group

  have hjemb : MeasurableEmbedding j := by
    have h1 : IsClosedEmbedding (Subtype.val : (sigmaCentralizer (η₁.prodMap η₂) (δ₁, δ₂)) → H₁ × H₂) := hTc.isClosedEmbedding_subtypeVal
    have h2 : IsClosedEmbedding (fun z : H₁ × H₂ => (y₁, y₂)⁻¹ * z * (y₁, y₂)) := by
      have e := ((Homeomorph.mulRight (y₁, y₂)).trans (Homeomorph.mulLeft (y₁, y₂)⁻¹)).isClosedEmbedding
      convert e using 1
      funext z
      simp only [Homeomorph.trans_apply, Homeomorph.coe_mulLeft, Homeomorph.coe_mulRight, mul_assoc]
    exact (h2.comp h1).measurableEmbedding
  have hτ'eq : τ' = Measure.map eT ((Measure.map κ₁ τ₁).prod (Measure.map κ₂ τ₂)) := by
    apply eq_of_map_eq_of_measurableEmbedding hjemb
    have heCm : Measurable (prodCentEquiv γ₁ γ₂ : (Subgroup.centralizer ({γ₁} : Set G₁)) × (Subgroup.centralizer ({γ₂} : Set G₂)) → (Subgroup.centralizer ({(γ₁, γ₂)} : Set (G₁ × G₂)))) := (prodCentEquiv γ₁ γ₂).continuous.measurable
    have heTm : Measurable (prodTorusEquiv η₁ η₂ δ₁ δ₂ : (sigmaCentralizer η₁ δ₁) × (sigmaCentralizer η₂ δ₂) → (sigmaCentralizer (η₁.prodMap η₂) (δ₁, δ₂))) :=
      (prodTorusEquiv η₁ η₂ δ₁ δ₂).continuous.measurable
    rw [hcpl', hτeq, heT', Measure.map_prod_map _ _ hκ₁m hκ₂m,
      Measure.map_map hψc.measurable heCm, Measure.map_map hjc.measurable heTm,
      Measure.map_map (hjc.measurable.comp heTm) (hκ₁m.prodMap hκ₂m)]
    congr 1
    funext p
    obtain ⟨s₁, s₂⟩ := p
    refine Prod.ext ?_ ?_
    · show φ₁ (s₁ : G₁) = y₁⁻¹ * (y₁ * φ₁ (s₁ : G₁) * y₁⁻¹) * y₁
      group
    · show φ₂ (s₂ : G₂) = y₂⁻¹ * (y₂ * φ₂ (s₂ : G₂) * y₂⁻¹) * y₂
      group
  exact ⟨τ₁, τ₂, Measure.map κ₁ τ₁, Measure.map κ₂ τ₂, hτ₁, hτ₂, hτ₁'H, hτ₂'H, by rw [hτeq, heC'], hτ'eq, hc₁, hc₂⟩

end S_AutomorphicForm_exists_prod_eq_and_coupled_of_coupled_prod
end P2MW
export P2MW.S_AutomorphicForm_exists_prod_eq_and_coupled_of_coupled_prod (solution)
