-- Prove2me | Definitions.Def_Development_AutomorphicArithmetic_AutomorphicVarieties_PartsConj
-- name    : Development_AutomorphicArithmetic_AutomorphicVarieties_PartsConj
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T17:32:19.585138+00:00
-- url     : https://prove2.me/theorems/4694e901-b2a4-4aaa-903c-8f1de104c2d2
-- title:
--   Parts Conj
-- statement:
--   Definitions and structural lemmas for Parts Conj, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/AutomorphicVarieties/PartsConj.lean

import Definitions.Def_Formalism_GaloisCohomology_Statement
import Theorems.Thm_Formalism_GaloisCohomology_scalRep_apply
import Theorems.Thm_ReciprocityTheory_Gal_continuous_toGS
import Theorems.Thm_ReciprocityTheory_Gal_isClosed_NS
import Theorems.Thm_ReciprocityTheory_Gal_isOpen_setOf_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.GaloisCohomology.scalRep_apply


set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.GaloisCohomology
namespace UpperTheory.V
section Conj
variable {F Ω : Type} [Field F] [NumberField F] [Field Ω] [Algebra F Ω]
def IsLift (τ : F ≃+* F) (σ : Ω ≃+* Ω) : Prop := ∀ x, σ (algebraMap F Ω x) = algebraMap F Ω (τ x)
variable {τ : F ≃+* F} {σ : Ω ≃+* Ω}
omit [NumberField F] in
theorem IsLift.symm (h : IsLift τ σ) : IsLift τ.symm σ.symm := fun x => by
  rw [RingEquiv.symm_apply_eq, h, RingEquiv.apply_symm_apply]
omit [NumberField F] in
theorem IsLift.trans {τ' : F ≃+* F} {σ' : Ω ≃+* Ω} (h : IsLift τ σ) (h' : IsLift τ' σ') :
    IsLift (τ.trans τ') (σ.trans σ') := fun x => by
  rw [RingEquiv.trans_apply, h, h', RingEquiv.trans_apply]
omit [NumberField F] in
theorem exists_isLift [IsAlgClosure F Ω] (τ : F ≃+* F) : ∃ σ : Ω ≃+* Ω, IsLift τ σ :=
  ⟨IsAlgClosure.equivOfEquiv Ω Ω τ, fun x => IsAlgClosure.equivOfEquiv_algebraMap Ω Ω τ x⟩
def conjGal (h : IsLift τ σ) : G F Ω →* G F Ω where
  toFun g := AlgEquiv.ofRingEquiv (f := (σ.trans g.toRingEquiv).trans σ.symm) fun x => by
    show σ.symm (g (σ (algebraMap F Ω x))) = _
    rw [h, AlgEquiv.commutes, ← h, RingEquiv.symm_apply_apply]
  map_one' := AlgEquiv.ext fun x => σ.symm_apply_apply x
  map_mul' g k := AlgEquiv.ext fun x => by
    show σ.symm (g (k (σ x))) = σ.symm (g (σ (σ.symm (k (σ x)))))
    rw [RingEquiv.apply_symm_apply]
omit [NumberField F] in
theorem apply_conjGal (h : IsLift τ σ) (g : G F Ω) (x : Ω) : σ (conjGal h g x) = g (σ x) :=
  σ.apply_symm_apply _
theorem continuous_conjGal [IsAlgClosure F Ω] (h : IsLift τ σ) : Continuous (conjGal h) := by
  refine continuous_of_continuousAt_one _ ?_
  rw [ContinuousAt, map_one]
  intro s hs
  obtain ⟨E, hE, hs⟩ := (krullTopology_mem_nhds_one_iff F Ω s).1 hs
  let b := Module.finBasis F E
  have ho : IsOpen (⋂ i, {g : G F Ω | g (σ (b i)) = σ (b i)}) :=
    isOpen_iInter_of_finite fun i => isOpen_setOf_apply (F := F) (σ (b i)) (fun t => t = σ (b i))
  rw [Filter.mem_map]
  refine Filter.mem_of_superset (ho.mem_nhds (Set.mem_iInter.2 fun i => rfl)) fun g hg => hs ?_
  have h1 : ∀ i, conjGal h g (b i) = b i := fun i =>
    σ.injective (by rw [apply_conjGal]; exact Set.mem_iInter.1 hg i)
  rw [SetLike.mem_coe, IntermediateField.mem_fixingSubgroup_iff]
  intro x hx
  have e : (conjGal h g).toLinearMap ∘ₗ E.val.toLinearMap = E.val.toLinearMap :=
    b.ext h1
  exact LinearMap.congr_fun e ⟨x, hx⟩
theorem val_lt_one {A A' : ValuationSubring Ω} (hA : ∀ x, σ x ∈ A' ↔ x ∈ A) (x : Ω) :
    A'.valuation (σ x) < 1 ↔ A.valuation x < 1 := by
  rw [valuation_lt_one_iff' (Ω := Ω), valuation_lt_one_iff' (Ω := Ω), hA, ← map_inv₀, hA,
    map_eq_zero_iff _ σ.injective]
theorem conjGal_mem_Dec (h : IsLift τ σ) {A A' : ValuationSubring Ω} (hA : ∀ x, σ x ∈ A' ↔ x ∈ A) {g : G F Ω}
    (hg : g ∈ Dec (F := F) A') : conjGal h g ∈ Dec (F := F) A := by
  rw [mem_Dec]
  ext x
  rw [ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem, ← map_inv, AlgEquiv.smul_def, ← hA, ← hA,
    apply_conjGal]
  exact apply_mem_iff_of_mem_Dec ((Dec (F := F) A').inv_mem hg) _
theorem conjGal_mem_Ine (h : IsLift τ σ) {A A' : ValuationSubring Ω} (hA : ∀ x, σ x ∈ A' ↔ x ∈ A) {g : G F Ω}
    (hg : g ∈ Ine (F := F) A') : conjGal h g ∈ Ine (F := F) A := by
  refine ⟨conjGal_mem_Dec h hA hg.1, fun x hx => ?_⟩
  rw [← val_lt_one hA, map_sub, apply_conjGal]
  exact hg.2 _ ((A'.valuation_le_one_iff _).2 ((hA x).2 ((A.valuation_le_one_iff _).1 hx)))
def preplace (τ : F ≃+* F) (v : HeightOneSpectrum (𝓞 F)) : HeightOneSpectrum (𝓞 F) :=
  (HeightOneSpectrum.equivOfRingEquiv (RingOfIntegers.mapRingEquiv τ)).symm v
omit [NumberField F] in
theorem mem_preplace (τ : F ≃+* F) (v : HeightOneSpectrum (𝓞 F)) (x : 𝓞 F) :
    x ∈ (preplace τ v).asIdeal ↔ RingOfIntegers.mapRingEquiv τ x ∈ v.asIdeal := Iff.rfl
theorem isPlaceOver_preplace (h : IsLift τ σ) {A A' : ValuationSubring Ω} (hA : ∀ x, σ x ∈ A' ↔ x ∈ A)
    {v : HeightOneSpectrum (𝓞 F)} (hv : IsPlaceOver A' v) : IsPlaceOver A (preplace τ v) := by
  intro x
  rw [mem_preplace, ← hv, ← val_lt_one hA, h]
  rfl
omit [NumberField F] in
theorem preplace_mem_Above (τ : F ≃+* F) (l : ℕ) (v : HeightOneSpectrum (𝓞 F)) :
    preplace τ v ∈ Above F l ↔ v ∈ Above F l := by
  show ((l : ℕ) : 𝓞 F) ∈ (preplace τ v).asIdeal ↔ ((l : ℕ) : 𝓞 F) ∈ v.asIdeal
  rw [mem_preplace, map_natCast]
variable [IsAlgClosure F Ω] {l : ℕ} [Fact l.Prime]
theorem conjGal_mem_NS (h : IsLift τ σ) {S : Set (HeightOneSpectrum (𝓞 F))} (hS : S = Above F l) {g : G F Ω}
    (hg : g ∈ NS Ω S) : conjGal h g ∈ NS Ω S := by
  have hc : IsClosed (((NS Ω S).comap (conjGal h) : Subgroup (G F Ω)) : Set (G F Ω)) :=
    (isClosed_NS Ω S).preimage (continuous_conjGal h)
  refine Subgroup.topologicalClosure_minimal _ (Subgroup.normalClosure_le_normal ?_) hc hg
  intro k hk
  simp only [Set.mem_iUnion] at hk
  obtain ⟨v, hv, A', hA', hk⟩ := hk
  have hA : ∀ x, σ x ∈ A' ↔ x ∈ A'.comap σ.toRingHom := fun x => Iff.rfl
  show conjGal h k ∈ NS Ω S
  apply Subgroup.le_topologicalClosure
  apply Subgroup.subset_normalClosure
  simp only [Set.mem_iUnion]
  refine ⟨preplace τ v, ?_, A'.comap σ.toRingHom, isPlaceOver_preplace h hA hA', conjGal_mem_Ine h hA hk⟩
  subst hS
  exact fun hh => hv ((preplace_mem_Above τ l v).1 hh)
def conjGS (D : LData F Ω l) (h : IsLift τ σ) :
    GS Ω (D.S : Set (HeightOneSpectrum (𝓞 F))) →* GS Ω (D.S : Set (HeightOneSpectrum (𝓞 F))) :=
  QuotientGroup.map _ _ (conjGal h) fun _ hg => conjGal_mem_NS h D.hS hg
theorem continuous_conjGS (D : LData F Ω l) (h : IsLift τ σ) : Continuous (conjGS D h) :=
  (QuotientGroup.isQuotientMap_mk _).continuous_iff.2 ((continuous_toGS Ω _).comp (continuous_conjGal h))
theorem chi_toGS (D : LData F Ω l) (g : G F Ω) : D.chi (toGS Ω _ g) = cyclotomicCharacter Ω l g.toRingEquiv :=
  DFunLike.congr_fun D.hchi g
theorem chi_conjGS (D : LData F Ω l) (h : IsLift τ σ) (g : GS Ω (D.S : Set (HeightOneSpectrum (𝓞 F)))) :
    D.chi (conjGS D h g) = D.chi g := by
  obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective _ g
  refine (chi_toGS D (conjGal h g)).trans (Eq.trans ?_ (chi_toGS D g).symm)
  have e : (conjGal h g).toRingEquiv = σ⁻¹ * g.toRingEquiv * σ := rfl
  rw [e, map_mul, map_mul, map_inv, mul_comm, ← mul_assoc, mul_inv_cancel, one_mul]
variable (l) in

def twScal (σ : Ω ≃+* Ω) (e : ℤ) : ℤ_[l] := ((cyclotomicCharacter Ω l σ ^ (-e) : ℤ_[l]ˣ) : ℤ_[l])
theorem qzTw_apply (D : LData F Ω l) (e : ℤ) (g : GS Ω (D.S : Set (HeightOneSpectrum (𝓞 F)))) (m : QZ l) :
    qzTw D e g m = ((D.chi g ^ (-e) : ℤ_[l]ˣ) : ℤ_[l]) • m := rfl
def h1TwistConjByLift (D : LData F Ω l) (e : ℤ) (h : IsLift τ σ) : H1 (qzTw D e) →ₗ[ℤ_[l]] H1 (qzTw D e) :=
  (mapH1 ((qzTw D e).comp (conjGS D h)) (qzTw D e) (twScal l σ e • LinearMap.id) continuous_of_discreteTopology
    (fun g m => by
      show twScal l σ e • qzTw D e (conjGS D h g) m = qzTw D e g (twScal l σ e • m)
      rw [qzTw_apply, qzTw_apply, chi_conjGS, smul_comm])).comp
    (resH1 (qzTw D e) (conjGS D h) (continuous_conjGS D h))
def galoisActionOnCohomology (D : LData F Ω l) (e : ℤ) (τ : F ≃+* F) : Module.End ℤ_[l] (H1 (qzTw D e)) :=
  h1TwistConjByLift D e (exists_isLift (Ω := Ω) τ).choose_spec
end Conj
end UpperTheory.V
end


