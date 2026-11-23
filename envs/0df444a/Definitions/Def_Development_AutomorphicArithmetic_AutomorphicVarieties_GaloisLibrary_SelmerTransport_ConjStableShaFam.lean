-- Prove2me | Definitions.Def_Development_AutomorphicArithmetic_AutomorphicVarieties_GaloisLibrary_SelmerTransport_ConjStableShaFam
-- name    : Development_AutomorphicArithmetic_AutomorphicVarieties_GaloisLibrary_SelmerTransport_ConjStableShaFam
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T17:41:15.680226+00:00
-- url     : https://prove2.me/theorems/0a231d0e-8acf-4be9-98f8-25d49a053df5
-- title:
--   Conj Stable Sha Fam
-- statement:
--   Definitions and structural lemmas for Conj Stable Sha Fam, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/AutomorphicVarieties/GaloisLibrary/SelmerTransport/ConjStableShaFam.lean

import Definitions.Def_Development_AutomorphicArithmetic_AutomorphicVarieties_GaloisLibrary_SelmerTransport_RestrictionMemInvariantH1
import Definitions.Def_Development_AutomorphicArithmetic_AutomorphicVarieties_GaloisLibrary_GaloisCohomologyLength_LevelInertiaLeLevelDec
import Definitions.Def_Development_AutomorphicArithmetic_AutomorphicVarieties_PartsConj
import Definitions.Def_Development_AutomorphicArithmetic_CyclotomicBounds_ClassNumberBounds_TotallyRealRoots_LeNuIffPowMemPrinc
import Theorems.Thm_Formalism_GaloisCohomology_scalRep_apply
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
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.GaloisCohomology TensorProduct
namespace UpperTheory.V.Base
section Coeff
variable (l : ℕ) [Fact l.Prime] (O : Type) [CommRing O] [Algebra ℤ_[l] O]
def QO : Type := O ⊗[ℤ_[l]] QZ l
instance : AddCommGroup (QO l O) := inferInstanceAs (AddCommGroup (O ⊗[ℤ_[l]] QZ l))
instance : Module O (QO l O) := inferInstanceAs (Module O (O ⊗[ℤ_[l]] QZ l))
instance : Module ℤ_[l] (QO l O) := inferInstanceAs (Module ℤ_[l] (O ⊗[ℤ_[l]] QZ l))
instance : IsScalarTower ℤ_[l] O (QO l O) := inferInstanceAs (IsScalarTower ℤ_[l] O (O ⊗[ℤ_[l]] QZ l))
instance : TopologicalSpace (QO l O) := ⊥
instance : DiscreteTopology (QO l O) := ⟨rfl⟩
instance : IsTopologicalAddGroup (QO l O) where
  continuous_add := continuous_of_discreteTopology
  continuous_neg := continuous_of_discreteTopology
def QO.incl : QZ l →ₗ[ℤ_[l]] QO l O := TensorProduct.mk ℤ_[l] O (QZ l) 1
def eO : ℕ∞ := Module.length O (O ⧸ Ideal.span {(l : O)})
abbrev twist₂ {Γ : Type} [Group Γ] {O : Type} [CommRing O] [Algebra ℤ_[l] O] (θ : Γ →* Oˣ) :
    Representation O Γ (QO l O) := scalRep (QO l O) θ
end Coeff
section Fields
variable (k E Ω : Type) [Field k] [Field E] [Field Ω] [Algebra k Ω] [Algebra E Ω]
def galOf : Subgroup (G k Ω) where
  carrier := {σ | ∀ x : E, σ (algebraMap E Ω x) = algebraMap E Ω x}
  one_mem' _ := rfl
  mul_mem' {a b} ha hb x := by rw [AlgEquiv.mul_apply, hb, ha]
  inv_mem' {a} ha x := a.symm_apply_eq.2 (ha x).symm
variable [Algebra k E] [IsScalarTower k E Ω]
def galEmb : G E Ω →* G k Ω := AlgEquiv.restrictScalarsHom k
theorem galEmb_mem (σ : G E Ω) : galEmb k E Ω σ ∈ galOf k E Ω := fun x => σ.commutes x
instance galOf_normal [Normal k E] : (galOf k E Ω).Normal where
  conj_mem σ h g x := by
    have e : (g⁻¹ : G k Ω) (algebraMap E Ω x) = algebraMap E Ω ((g⁻¹ : G k Ω).restrictNormal E x) :=
      (AlgEquiv.restrictNormal_commutes _ E x).symm
    rw [AlgEquiv.mul_apply, AlgEquiv.mul_apply, e, h, ← e]
    exact g.apply_symm_apply _
end Fields
section Sha
variable (k Ω : Type) [Field k] [NumberField k] [Field Ω] [Algebra k Ω] (l : ℕ)
def shaFam : Set (Subgroup (G k Ω)) :=
  {D | (∃ A : ValuationSubring Ω, A.valuation (l : Ω) < 1 ∧ D = Dec (F := k) A) ∨
    ∃ A : ValuationSubring Ω, D = Ine (F := k) A}
theorem valuation_lt_one_iff_mem_and_inv_not_mem {Ω : Type} [Field Ω] (A : ValuationSubring Ω) (z : Ω) :
    A.valuation z < 1 ↔ z ∈ A ∧ (z = 0 ∨ z⁻¹ ∉ A) := by
  rcases eq_or_ne z 0 with rfl | hz
  · simp
  · have h0 : 0 < A.valuation z := by
      rw [zero_lt_iff]
      simpa using hz
    rw [← A.valuation_le_one_iff, ← A.valuation_le_one_iff, map_inv₀, inv_le_one₀ h0]
    simp only [hz, false_or, not_le]
    exact ⟨fun h => ⟨h.le, h⟩, fun h => h.2⟩
theorem comap_valuation_lt_one_iff_selmer_transport {Ω : Type} [Field Ω] (A : ValuationSubring Ω) (f : Ω →+* Ω) (z : Ω) :
    (A.comap f).valuation z < 1 ↔ A.valuation (f z) < 1 := by
  rw [valuation_lt_one_iff_mem_and_inv_not_mem, valuation_lt_one_iff_mem_and_inv_not_mem, ValuationSubring.mem_comap, ValuationSubring.mem_comap,
    map_inv₀, map_eq_zero]
theorem mem_decompositionSubgroup_iff_selmer_transport {k Ω : Type} [Field k] [Field Ω] [Algebra k Ω] (A : ValuationSubring Ω)
    (x : G k Ω) : x ∈ ValuationSubring.decompositionSubgroup k A ↔ ∀ y : Ω, x y ∈ A ↔ y ∈ A := by
  simp only [ValuationSubring.decompositionSubgroup, MulAction.mem_stabilizer_iff]
  constructor
  · intro h y
    have e := SetLike.ext_iff.1 h (x y)
    rw [ValuationSubring.mem_smul_pointwise_iff_exists] at e
    rw [← e]
    constructor
    · rintro ⟨s, hs, hs'⟩
      rw [AlgEquiv.smul_def] at hs'
      rwa [← x.injective hs']
    · intro hy
      exact ⟨y, hy, rfl⟩
  · intro h
    ext y
    rw [ValuationSubring.mem_smul_pointwise_iff_exists]
    constructor
    · rintro ⟨s, hs, rfl⟩
      rw [AlgEquiv.smul_def]
      exact (h s).2 hs
    · intro hy
      refine ⟨x.symm y, (h _).1 (by simpa using hy), by simp [AlgEquiv.smul_def]⟩
theorem conjStable_shaFam : ConjStable (shaFam k Ω l) := by
  intro D hD g
  have key : ∀ x : G k Ω, ∀ y, g ((g⁻¹ * x * g) y) = x (g y) := by
    intro x y
    rw [AlgEquiv.mul_apply, AlgEquiv.mul_apply, ← AlgEquiv.mul_apply g g⁻¹, mul_inv_cancel,
      AlgEquiv.one_apply]
  rcases hD with ⟨A, hl, rfl⟩ | ⟨A, rfl⟩
  · refine ⟨Dec (F := k) (A.comap (g : Ω →+* Ω)), Or.inl ⟨_, ?_, rfl⟩, fun x => ?_⟩
    · rw [comap_valuation_lt_one_iff_selmer_transport]
      simpa using hl
    · simp only [Dec, mem_decompositionSubgroup_iff_selmer_transport, ValuationSubring.mem_comap, RingHom.coe_coe, key]
      constructor
      · intro h y
        exact h (g y)
      · intro h y
        simpa using h (g.symm y)
  · refine ⟨Ine (F := k) (A.comap (g : Ω →+* Ω)), Or.inr ⟨_, rfl⟩, fun x => ?_⟩
    change x ∈ Inertia (F := k) A ↔ g⁻¹ * x * g ∈ Inertia (F := k) (A.comap (g : Ω →+* Ω))
    simp only [Inertia, Set.mem_setOf_eq, mem_decompositionSubgroup_iff_selmer_transport, ValuationSubring.valuation_le_one_iff,
      ValuationSubring.mem_comap, RingHom.coe_coe, comap_valuation_lt_one_iff_selmer_transport, map_sub, key]
    constructor
    · rintro ⟨h1, h2⟩
      exact ⟨fun y => h1 (g y), fun y hy => h2 (g y) hy⟩
    · rintro ⟨h1, h2⟩
      refine ⟨fun y => by simpa using h1 (g.symm y), fun y hy => by simpa using h2 (g.symm y) (by simpa using hy)⟩
variable {k Ω} {R M : Type} [CommRing R] [AddCommGroup M] [Module R M] [TopologicalSpace M] [IsTopologicalAddGroup M]
  [ContinuousConstSMul R M]
abbrev ShaU (ρ : Representation R (G k Ω) M) (l : ℕ) (U : Subgroup (G k Ω)) : Submodule R (H1U ρ U) :=
  LocSel ρ U (shaFam k Ω l)
abbrev shaRep [DiscreteTopology M] (ρ : Representation R (G k Ω) M) (l : ℕ) (U : Subgroup (G k Ω)) [U.Normal] :
    Representation R (G k Ω) (ShaU ρ l U) := selRep ρ U (conjStable_shaFam k Ω l)
abbrev shaEig [DiscreteTopology M] (ρ : Representation R (G k Ω) M) (l : ℕ) (U : Subgroup (G k Ω)) [U.Normal]
    (W : Subgroup (G k Ω)) (ψ : W →* Rˣ) : Submodule R (ShaU ρ l U) := selEig ρ U (conjStable_shaFam k Ω l) W ψ
end Sha
section Tower
variable {k Ω : Type} [Field k] [NumberField k] [Field Ω] [Algebra k Ω] (l : ℕ) [Fact l.Prime]
variable (k Ω) in

def chiO (O : Type) [CommRing O] [Algebra ℤ_[l] O] : G k Ω →* Oˣ :=
  (Units.map (algebraMap ℤ_[l] O).toMonoidHom).comp (cycZ k Ω l)
def levU (U : Subgroup (G k Ω)) (n : ℕ) : Subgroup (G k Ω) := U ⊓ (KStar.TotallyRealRoots.princ l n).comap (cycZ k Ω l)
def cycU (U : Subgroup (G k Ω)) : Subgroup (G k Ω) := U ⊓ (cycZ k Ω l).ker
def delU (U : Subgroup (G k Ω)) : Subgroup (G k Ω) := U ⊓ (CommGroup.torsion ℤ_[l]ˣ).comap (cycZ k Ω l)
def qExp (l : ℕ) : ℕ := if l = 2 then 2 else 1
abbrev gamU (U : Subgroup (G k Ω)) : Subgroup (G k Ω) := levU l U (qExp l)
instance (U : Subgroup (G k Ω)) [U.Normal] (n : ℕ) : (levU l U n).Normal := by unfold levU; infer_instance
instance (U : Subgroup (G k Ω)) [U.Normal] : (cycU l U).Normal := by unfold cycU; infer_instance
instance (U : Subgroup (G k Ω)) [U.Normal] : (delU l U).Normal := by unfold delU; infer_instance
end Tower
section Infl
variable (k : Type) {E Ω : Type} [Field k] [NumberField k] [Field E] [NumberField E] [Field Ω] [Algebra k E] [Algebra k Ω]
  [Algebra E Ω] [IsScalarTower k E Ω] [IsAlgClosure E Ω] {l : ℕ} [Fact l.Prime]
def Infl (D : LData E Ω l) (e : ℤ) (x : H1 (qzTw D e)) (y : H1U (LDataCardLeFinrank.qzG k Ω l e) (galOf k E Ω)) : Prop :=
  ∃ (z : Z1 (qzTw D e)) (z' : Z1U (LDataCardLeFinrank.qzG k Ω l e) (galOf k E Ω)),
    x = Submodule.Quotient.mk z ∧ y = Submodule.Quotient.mk z' ∧
      ∀ σ : G E Ω, z'.1 ⟨galEmb k E Ω σ, galEmb_mem k E Ω σ⟩ = z.1 (toGS Ω _ σ)
end Infl
end UpperTheory.V.Base
end


