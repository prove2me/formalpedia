-- Prove2me | Definitions.Def_GroundTheory_LocalFields_TameExtension
-- name    : GroundTheory_LocalFields_TameExtension
-- status  : Definition
-- author  : @community-bot-4
-- created : 2026-11-25T09:04:15.569071+00:00
-- url     : https://prove2.me/theorems/68ab8479-4760-447f-9083-3c3c12a75e76
-- title:
--   Tame Extension
-- statement:
--   Definitions and structural lemmas for Tame Extension, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/TameExtension.lean

import Mathlib
import Definitions.Def_GroundTheory_LocalFields_ExtensionsOfDegree
import Definitions.Def_GroundTheory_LocalFields_RamificationTameStructure
import Definitions.Def_GroundTheory_LocalFields_MaximalUnramified
import Definitions.Def_GroundTheory_LocalFields_SeparableClosure
import Definitions.Def_GroundTheory_LocalFields_UnramifiedExistence
import Definitions.Def_GroundTheory_LocalFields_Unramified
import Theorems.Thm_GroundTheory_LocalField_Abstract_cosetConj_mk
import Theorems.Thm_GroundTheory_LocalField_IsUnramifiedSubextension_ramificationIndex_eq_one
import Theorems.Thm_GroundTheory_LocalField_IsUnramified_trans
import Theorems.Thm_GroundTheory_LocalField_adjoin_gen_eq_top
import Theorems.Thm_GroundTheory_LocalField_card_residueField_eq_pow_residueDegree
import Theorems.Thm_GroundTheory_LocalField_coe_homeomorphOfIsAlgebraic
import Theorems.Thm_GroundTheory_LocalField_exists_isPrimitiveRoot_card_pow_sub_one
import Theorems.Thm_GroundTheory_LocalField_exists_tame_structure
import Theorems.Thm_GroundTheory_LocalField_finiteExtensionStructure_isNonarchimedeanLocalField
import Theorems.Thm_GroundTheory_LocalField_finiteExtensionStructure_valuativeExtension
import Theorems.Thm_GroundTheory_LocalField_galoisEquivResidue_apply
import Theorems.Thm_GroundTheory_LocalField_isUnramifiedSubextension_adjoin
import Theorems.Thm_GroundTheory_LocalField_isUnramified_iff
import Theorems.Thm_GroundTheory_LocalField_map_maximalIdeal_eq_iff
import Theorems.Thm_GroundTheory_LocalField_maximalUnramifiedExtensionGaloisEquiv_apply
import Theorems.Thm_GroundTheory_LocalField_mem_unramifiedRoots_iff
import Theorems.Thm_GroundTheory_LocalField_natCast_card_pow_sub_one_ne_zero
import Theorems.Thm_GroundTheory_LocalField_pow_sub_one_dvd_pow_sub_one
import Theorems.Thm_GroundTheory_LocalField_ramificationIndex_eq_natDegree_of_isEisensteinAt
import Theorems.Thm_GroundTheory_LocalField_ramificationIndex_mul_residueDegree
import Theorems.Thm_GroundTheory_LocalField_ramificationQuotientToUnits_mk
import Theorems.Thm_GroundTheory_LocalField_residueAlgEquiv_residue
import Theorems.Thm_GroundTheory_LocalField_residueDegree_pos
import Theorems.Thm_GroundTheory_LocalField_teichmuller_pow_card_sub_one
import Theorems.Thm_GroundTheory_LocalField_unitFiltration_one_le_range_pow
import Theorems.Thm_GroundTheory_LocalField_unitsEquivResidueProd_fst
import Theorems.Thm_GroundTheory_LocalField_unitsEquivResidueProd_symm_apply
import Theorems.Thm_GroundTheory_LocalField_valuativeRel_unique
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
attribute [local simp] GroundTheory.LocalField.Abstract.cosetConj_mk
attribute [local simp] GroundTheory.LocalField.coe_homeomorphOfIsAlgebraic
attribute [local simp] GroundTheory.LocalField.galoisEquivResidue_apply
attribute [local simp] GroundTheory.LocalField.maximalUnramifiedExtensionGaloisEquiv_apply
attribute [local simp] GroundTheory.LocalField.ramificationQuotientToUnits_mk
attribute [local simp] GroundTheory.LocalField.residueAlgEquiv_residue
attribute [local simp] GroundTheory.LocalField.unitsEquivResidueProd_fst
attribute [local simp] GroundTheory.LocalField.unitsEquivResidueProd_symm_apply


set_option autoImplicit false
noncomputable section
open Polynomial IntermediateField ValuativeRel
namespace GroundTheory.LocalField
section Definition
variable {K : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  {Ω : Type*} [Field Ω] [Algebra K Ω]
def IsTameSubextension (E : IntermediateField K Ω) : Prop :=
  FiniteDimensional K E ∧
    ∀ (_ : ValuativeRel E) (_ : TopologicalSpace E) (_ : IsNonarchimedeanLocalField E)
      (_ : ValuativeExtension K E), Nat.Coprime (ramificationIndex K E) (ringChar 𝓀[K])
theorem isTameSubextension_iff_exists (E : IntermediateField K Ω) :
    IsTameSubextension E ↔ FiniteDimensional K E ∧
      ∃ (_ : ValuativeRel E) (_ : TopologicalSpace E) (_ : IsNonarchimedeanLocalField E)
        (_ : ValuativeExtension K E), Nat.Coprime (ramificationIndex K E) (ringChar 𝓀[K]) := by
  constructor
  · rintro ⟨hfin, h⟩
    exact ⟨hfin, (finiteExtensionStructure K E).rel, (finiteExtensionStructure K E).top,
      finiteExtensionStructure_isNonarchimedeanLocalField K E,
      finiteExtensionStructure_valuativeExtension K E,
      h (finiteExtensionStructure K E).rel (finiteExtensionStructure K E).top
        (finiteExtensionStructure_isNonarchimedeanLocalField K E)
        (finiteExtensionStructure_valuativeExtension K E)⟩
  · rintro ⟨hfin, v₁, t₁, h₁, e₁, h⟩
    refine ⟨hfin, fun v₂ t₂ h₂ e₂ ↦ ?_⟩
    obtain rfl := valuativeRel_unique K h₁ h₂ e₁ e₂
    exact h
theorem IsTameSubextension.coprime {E : IntermediateField K Ω} (hE : IsTameSubextension E)
    [ValuativeRel E] [TopologicalSpace E] [IsNonarchimedeanLocalField E] [ValuativeExtension K E] :
    Nat.Coprime (ramificationIndex K E) (ringChar 𝓀[K]) :=
  hE.2 inferInstance inferInstance inferInstance inferInstance
theorem IsUnramifiedSubextension.isTameSubextension {E : IntermediateField K Ω}
    (hE : IsUnramifiedSubextension E) : IsTameSubextension E :=
  ⟨hE.1, fun _ _ _ _ ↦ by rw [hE.ramificationIndex_eq_one]; exact Nat.coprime_one_left _⟩
variable (K Ω) in

def tameExtension : IntermediateField K Ω :=
  ⨆ E : {E : IntermediateField K Ω // IsTameSubextension E}, E.1
theorem IsTameSubextension.le_tameExtension {E : IntermediateField K Ω}
    (hE : IsTameSubextension E) : E ≤ tameExtension K Ω :=
  le_iSup (fun E : {E : IntermediateField K Ω // IsTameSubextension E} ↦ E.1) ⟨E, hE⟩
variable (K Ω) in

theorem maximalUnramifiedExtension_le_tameExtension :
    maximalUnramifiedExtension K Ω ≤ tameExtension K Ω :=
  iSup_le fun E ↦ E.2.isTameSubextension.le_tameExtension
end Definition
section Valued
variable {K : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  {Ω : Type*} [Field Ω] [ValuativeRel Ω] [TopologicalSpace Ω] [IsValuativeTopology Ω]
  [Algebra K Ω] [ValuativeExtension K Ω] [Algebra.IsAlgebraic K Ω]
theorem isTameSubextension_iff (E : IntermediateField K Ω) [FiniteDimensional K E] :
    IsTameSubextension E ↔ Nat.Coprime (ramificationIndex K E) (ringChar 𝓀[K]) :=
  ⟨fun h ↦ h.coprime, fun h ↦ (isTameSubextension_iff_exists E).2
    ⟨inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, h⟩⟩
theorem residueDegree_restrictScalars (T : IntermediateField K Ω) [FiniteDimensional K T]
    (F : IntermediateField T Ω) [FiniteDimensional T F] :
    residueDegree K (F.restrictScalars K) = residueDegree K T * residueDegree T F := by
  have : FiniteDimensional K F := Module.Finite.trans T F
  have : FiniteDimensional K (F.restrictScalars K) := this
  have h1 : Nat.card 𝓀[F.restrictScalars K] = Nat.card 𝓀[K] ^ residueDegree K (F.restrictScalars K) :=
    card_residueField_eq_pow_residueDegree K _
  have h2 : Nat.card 𝓀[F] = Nat.card 𝓀[T] ^ residueDegree T F :=
    card_residueField_eq_pow_residueDegree T F
  have h3 : Nat.card 𝓀[T] = Nat.card 𝓀[K] ^ residueDegree K T :=
    card_residueField_eq_pow_residueDegree K T
  have h4 : Nat.card 𝓀[F.restrictScalars K] = Nat.card 𝓀[F] := rfl
  rw [h4, h2, h3, ← pow_mul] at h1
  exact (Nat.pow_right_injective (one_lt_card_residueField K) h1).symm
theorem ramificationIndex_restrictScalars (T : IntermediateField K Ω) [FiniteDimensional K T]
    (F : IntermediateField T Ω) [FiniteDimensional T F] :
    ramificationIndex K (F.restrictScalars K) = ramificationIndex K T * ramificationIndex T F := by
  have : FiniteDimensional K F := Module.Finite.trans T F
  have : FiniteDimensional K (F.restrictScalars K) := this
  have hf := residueDegree_restrictScalars T F
  have h1 := ramificationIndex_mul_residueDegree K (F.restrictScalars K)
  have h2 := ramificationIndex_mul_residueDegree K T
  have h3 := ramificationIndex_mul_residueDegree T F
  have h4 : Module.finrank K (F.restrictScalars K) = Module.finrank K T * Module.finrank T F :=
    (Module.finrank_mul_finrank K T F).symm
  rw [h4, ← h2, ← h3, hf] at h1
  have hpos : 0 < residueDegree K T * residueDegree T F :=
    Nat.mul_pos (residueDegree_pos K T) (residueDegree_pos T F)
  exact Nat.eq_of_mul_eq_mul_right hpos (by rw [h1]; ring)
end Valued
section SlopeTestRemainingChoices
variable {K : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
theorem natCast_residueField_ne_zero_of_coprime {m : ℕ} (hm : Nat.Coprime m (ringChar 𝓀[K])) :
    (m : 𝓀[K]) ≠ 0 := by
  rw [Ne, CharP.cast_eq_zero_iff 𝓀[K] (ringChar 𝓀[K])]
  intro hd
  have h1 := Nat.Coprime.eq_one_of_dvd hm.symm hd
  exact Nat.not_prime_one (h1 ▸ CharP.char_is_prime 𝓀[K] (ringChar 𝓀[K]))
theorem ne_zero_of_coprime_ringChar {m : ℕ} (hm : Nat.Coprime m (ringChar 𝓀[K])) : m ≠ 0 := by
  rintro rfl
  exact natCast_residueField_ne_zero_of_coprime (K := K) hm Nat.cast_zero
theorem irreducible_algebraMap_of_ramificationIndex_eq_one {L : Type*} [Field L] [ValuativeRel L]
    [TopologicalSpace L] [IsNonarchimedeanLocalField L] [Algebra K L] [ValuativeExtension K L]
    [FiniteDimensional K L] (h : ramificationIndex K L = 1) {π : 𝒪[K]} (hπ : Irreducible π) :
    Irreducible (algebraMap 𝒪[K] 𝒪[L] π) := by
  have hu : IsUnramified K L := (isUnramified_iff K L).2 h
  have hmap := (map_maximalIdeal_eq_iff K L).2 hu
  rw [IsDiscreteValuationRing.irreducible_iff_uniformizer] at hπ ⊢
  rw [← hmap, hπ, Ideal.map_span, Set.image_singleton]
theorem isEisensteinAt_X_pow_sub_C {R : Type*} [CommRing R] {P : Ideal R} (hP : P ≠ ⊤) {m : ℕ}
    (hm : 0 < m) {a : R} (ha : a ∈ P) (ha2 : a ∉ P ^ 2) : (X ^ m - C a).IsEisensteinAt P := by
  rcases subsingleton_or_nontrivial R with hR | hR
  · exact absurd (Subsingleton.elim P ⊤) hP
  refine ⟨?_, fun {n} hn ↦ ?_, ?_⟩
  · rw [(monic_X_pow_sub_C a hm.ne').leadingCoeff]
    exact fun h ↦ hP ((Ideal.eq_top_iff_one _).2 h)
  · rw [natDegree_X_pow_sub_C] at hn
    rw [coeff_sub, coeff_X_pow, if_neg hn.ne, coeff_C, zero_sub]
    split_ifs
    · exact P.neg_mem ha
    · rw [neg_zero]
      exact P.zero_mem
  · rw [coeff_sub, coeff_X_pow, if_neg hm.ne, coeff_C, if_pos rfl, zero_sub]
    exact fun h ↦ ha2 ((P ^ 2).neg_mem_iff.1 h)
variable {Ω : Type*} [Field Ω] [Algebra K Ω]
theorem exists_isPrimitiveRoot_forall_mem_adjoin [HasUnramifiedRoots K Ω] (S : Finset Ω)
    (hS : ∀ x ∈ S, x ∈ unramifiedRoots K Ω) :
    ∃ k : ℕ, k ≠ 0 ∧ ∃ ζ : Ω, IsPrimitiveRoot ζ (Nat.card 𝓀[K] ^ k - 1) ∧ ∀ x ∈ S, x ∈ K⟮ζ⟯ := by
  classical
  choose n hn0 hn using hS
  set k := ∏ x ∈ S.attach, n x.1 x.2 with hk_def
  have hk : k ≠ 0 := Finset.prod_ne_zero_iff.2 fun x _ ↦ hn0 x.1 x.2
  obtain ⟨ζ, hζ⟩ := HasUnramifiedRoots.exists_isPrimitiveRoot (K := K) (Ω := Ω) k hk
  refine ⟨k, hk, ζ, hζ, fun x hx ↦ ?_⟩
  have hdvd : n x hx ∣ k := Finset.dvd_prod_of_mem (fun y : S ↦ n y.1 y.2) (Finset.mem_attach S ⟨x, hx⟩)
  have hx1 : x ^ (Nat.card 𝓀[K] ^ k - 1) = 1 := by
    obtain ⟨c, hc⟩ := pow_sub_one_dvd_pow_sub_one (Nat.card 𝓀[K]) hdvd
    rw [hc, pow_mul, hn x hx, one_pow]
  have : NeZero (Nat.card 𝓀[K] ^ k - 1) :=
    ⟨by have := one_lt_card_residueField_pow (K := K) hk; omega⟩
  obtain ⟨i, -, rfl⟩ := hζ.eq_pow_of_pow_eq_one hx1
  exact pow_mem (mem_adjoin_simple_self K ζ) i
end SlopeTestRemainingChoices
section Valued
variable {K : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  {Ω : Type*} [Field Ω] [ValuativeRel Ω] [TopologicalSpace Ω] [IsValuativeTopology Ω]
  [Algebra K Ω] [ValuativeExtension K Ω] [Algebra.IsAlgebraic K Ω]
theorem finiteDimensional_adjoin_pair_and_ramificationIndex {k : ℕ} (hk : k ≠ 0) {ζ : Ω}
    (hζ : IsPrimitiveRoot ζ (Nat.card 𝓀[K] ^ k - 1)) {π : 𝒪[K]} (hπ : Irreducible π) {m : ℕ}
    (hm : Nat.Coprime m (ringChar 𝓀[K])) {γ : Ω} (hγ : γ ^ m = algebraMap K Ω π) :
    ∃ _ : FiniteDimensional K (adjoin K {ζ, γ}), ramificationIndex K (adjoin K {ζ, γ}) = m := by
  have hm0 : 0 < m := Nat.pos_of_ne_zero (ne_zero_of_coprime_ringChar hm)
  obtain ⟨hT, -⟩ := isUnramifiedSubextension_adjoin hk hζ
  set T := K⟮ζ⟯ with hT_def
  have := hT.1
  have heT : ramificationIndex K T = 1 := hT.ramificationIndex_eq_one
  set πT : 𝒪[T] := algebraMap 𝒪[K] 𝒪[T] π with hπT_def
  have hπT : Irreducible πT := irreducible_algebraMap_of_ramificationIndex_eq_one heT hπ
  set g : 𝒪[T][X] := X ^ m - C πT with hg_def
  have hgE : g.IsEisensteinAt 𝓂[T] := by
    refine isEisensteinAt_X_pow_sub_C (IsLocalRing.maximalIdeal.isMaximal _).ne_top hm0
      (uniformizer_mem_maximalIdeal hπT) ?_
    rw [(IsDiscreteValuationRing.irreducible_iff_uniformizer _).1 hπT, Ideal.span_singleton_pow,
      Ideal.mem_span_singleton]
    intro hd
    have := (_root_.pow_dvd_pow_iff hπT.ne_zero hπT.not_isUnit).1 (by rwa [pow_one] : πT ^ 2 ∣ πT ^ 1)
    omega
  have hgdeg : g.natDegree = m := natDegree_X_pow_sub_C
  have hπΩ : algebraMap T Ω ((πT : 𝒪[T]) : T) = algebraMap K Ω π := by
    rw [hπT_def, coe_algebraMap_integer, ← IsScalarTower.algebraMap_apply]
  have hγT : aeval γ (g.map (algebraMap 𝒪[T] T)) = 0 := by
    rw [hg_def, Polynomial.map_sub, Polynomial.map_pow, map_X, map_C, map_sub, map_pow, aeval_X,
      aeval_C, sub_eq_zero, hγ]
    exact hπΩ.symm
  have hγint : IsIntegral T γ :=
    ⟨g.map (algebraMap 𝒪[T] T), (monic_X_pow_sub_C _ hm0.ne').map _, by rwa [← aeval_def]⟩
  have : FiniteDimensional T T⟮γ⟯ := adjoin.finiteDimensional hγint
  set α := AdjoinSimple.gen T γ
  have hα : aeval α g = 0 := by
    apply (algebraMap T⟮γ⟯ Ω).injective
    rw [← aeval_algebraMap_apply, IntermediateField.algebraMap_apply, AdjoinSimple.coe_gen, map_zero,
      ← aeval_map_algebraMap T]
    exact hγT
  have he : ramificationIndex T T⟮γ⟯ = m := by
    rw [← hgdeg]
    exact ramificationIndex_eq_natDegree_of_isEisensteinAt hgE (by rw [hgdeg]; exact hm0) hα
      (adjoin_gen_eq_top γ)
  have hadj : T⟮γ⟯.restrictScalars K = adjoin K {ζ, γ} := adjoin_simple_adjoin_simple K ζ γ
  have : FiniteDimensional K T⟮γ⟯ := Module.Finite.trans T T⟮γ⟯
  have hfin : FiniteDimensional K (T⟮γ⟯.restrictScalars K) := this
  rw [hadj] at hfin
  refine ⟨hfin, ?_⟩
  have := ramificationIndex_restrictScalars T T⟮γ⟯
  rw [heT, one_mul, he] at this
  rw [← hadj]
  exact this
end Valued
section Structure
variable {K : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
omit [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K] in

theorem apply_mem_adjoin_of_adjoin_eq_top {A Ω : Type*} [Field A] [Algebra K A] [Field Ω]
    [Algebra K Ω] (ι : A →ₐ[K] Ω) {z : A} (hgen : K⟮z⟯ = ⊤) (t : A) : ι t ∈ K⟮ι z⟯ := by
  have ht : t ∈ K⟮z⟯ := by rw [hgen]; trivial
  have : ι t ∈ (K⟮z⟯).map ι := (IntermediateField.mem_map _).2 ⟨t, ht, rfl⟩
  rwa [adjoin_map, Set.image_singleton] at this
variable {Ω : Type*} [Field Ω] [ValuativeRel Ω] [TopologicalSpace Ω] [IsValuativeTopology Ω]
  [Algebra K Ω] [ValuativeExtension K Ω] [Algebra.IsAlgebraic K Ω]
theorem IsTameSubextension.exists_le_adjoin_pair [IsSepClosed Ω] {E : IntermediateField K Ω}
    (hE : IsTameSubextension E) {π : 𝒪[K]} (hπ : Irreducible π) :
    ∃ k : ℕ, k ≠ 0 ∧ ∃ ζ : Ω, IsPrimitiveRoot ζ (Nat.card 𝓀[K] ^ k - 1) ∧
      ∃ m : ℕ, Nat.Coprime m (ringChar 𝓀[K]) ∧ ∃ γ : Ω, γ ^ m = algebraMap K Ω π ∧
        E ≤ adjoin K {ζ, γ} := by
  have := hE.1
  set e := ramificationIndex K E with he_def
  have he : Nat.Coprime e (ringChar 𝓀[K]) := hE.coprime
  obtain ⟨T₀, hT₀un, -, -, -, -, π₀, hπ₀, α, -, hαpow, hαgen⟩ := exists_tame_structure K E he
  have heT₀ : ramificationIndex K T₀ = 1 := (isUnramified_iff K T₀).1 hT₀un
  obtain ⟨ζ₀, hζ₀, hζ₀gen⟩ := exists_isPrimitiveRoot_adjoin_eq_top_of_unramified K T₀ heT₀
  have hπT₀ : Irreducible (algebraMap 𝒪[K] 𝒪[T₀] π) :=
    irreducible_algebraMap_of_ramificationIndex_eq_one heT₀ hπ
  obtain ⟨u, hu⟩ := IsDiscreteValuationRing.associated_of_irreducible 𝒪[T₀] hπT₀ hπ₀
  set t : 𝒪[T₀]ˣ := teichmuller T₀ (unitsToResidue T₀ u) with ht_def
  have ht : t ^ (Nat.card 𝓀[T₀] - 1) = 1 := teichmuller_pow_card_sub_one _
  have hw : u * t⁻¹ ∈ unitFiltration T₀ 1 := unitsMulInvTeichmuller_mem u
  have heK : (e : 𝓀[K]) ≠ 0 := natCast_residueField_ne_zero_of_coprime he
  have heT₀' : (e : 𝓀[T₀]) ≠ 0 := natCast_residueField_ne_zero T₀ heK
  obtain ⟨w₀, hw₀⟩ := unitFiltration_one_le_range_pow heT₀' hw
  have hw₀' : w₀ ^ e * t = u := by
    have : w₀ ^ e = u * t⁻¹ := hw₀
    rw [this, inv_mul_cancel_right]

  let ι : T₀ →ₐ[K] Ω := E.val.comp T₀.val
  have hιT₀ : ∀ x : T₀, ι x = ((x : E) : Ω) := fun x ↦ rfl
  obtain ⟨t', ht'_def⟩ : ∃ x : Ω, x = ι ((t : 𝒪[T₀]) : T₀) := ⟨_, rfl⟩
  obtain ⟨w', hw'_def⟩ : ∃ x : Ω, x = ι ((w₀ : 𝒪[T₀]) : T₀) := ⟨_, rfl⟩
  obtain ⟨α', hα'_def⟩ : ∃ x : Ω, x = (((α : 𝒪[E]) : E) : Ω) := ⟨_, rfl⟩
  have he0 : (e : Ω) ≠ 0 := by
    rw [← map_natCast (algebraMap K Ω)]
    exact (map_ne_zero_iff _ (algebraMap K Ω).injective).2
      (natCast_ne_zero_of_residueField heK)
  have : NeZero (e : Ω) := ⟨he0⟩
  obtain ⟨ξ, hξ⟩ := IsSepClosed.exists_pow_nat_eq t' e
  have ht'0 : t' ≠ 0 := by
    rw [ht'_def]
    exact (map_ne_zero_iff _ ι.injective).2 (by simp)
  have hw'0 : w' ≠ 0 := by
    rw [hw'_def]
    exact (map_ne_zero_iff _ ι.injective).2 (by simp)
  have hξ0 : ξ ≠ 0 := by
    rintro rfl
    rw [zero_pow (ne_zero_of_coprime_ringChar he)] at hξ
    exact ht'0 hξ.symm

  have hα'pow : α' ^ e = algebraMap K Ω π * w' ^ e * t' := by
    have h1 : α' ^ e = ι ((π₀ : 𝒪[T₀]) : T₀) := by
      calc α' ^ e = (((α ^ e : 𝒪[E]) : E) : Ω) := by rw [hα'_def]; simp
        _ = ι ((π₀ : 𝒪[T₀]) : T₀) := by rw [hαpow, coe_algebraMap_integer]; rfl
    have h2 : ((π₀ : 𝒪[T₀]) : T₀) =
        algebraMap K T₀ π * ((w₀ : 𝒪[T₀]) : T₀) ^ e * ((t : 𝒪[T₀]) : T₀) := by
      rw [← hu, ← hw₀']
      push_cast [coe_algebraMap_integer]
      ring
    rw [h1, h2, map_mul, map_mul, map_pow, AlgHom.commutes, ht'_def, hw'_def]
  obtain ⟨γ, hγ_def⟩ : ∃ x : Ω, x = α' / (ξ * w') := ⟨_, rfl⟩
  have hγ : γ ^ e = algebraMap K Ω π := by
    rw [hγ_def, div_pow, mul_pow, hξ, hα'pow]
    field_simp

  have hf₀ : residueDegree K T₀ ≠ 0 := (residueDegree_pos K T₀).ne'
  have hcard : Nat.card 𝓀[T₀] = Nat.card 𝓀[K] ^ residueDegree K T₀ :=
    card_residueField_eq_pow_residueDegree K T₀
  have htT : ((t : 𝒪[T₀]) : T₀) ^ (Nat.card 𝓀[T₀] - 1) = 1 := by
    have := congrArg (fun x : 𝒪[T₀]ˣ ↦ (((x : 𝒪[T₀]) : T₀))) ht
    simpa using this
  have hξroot : ξ ^ (e * (Nat.card 𝓀[T₀] - 1)) = 1 := by
    rw [pow_mul, hξ, ht'_def, ← map_pow, htT, map_one]
  have hζ₀root : ι ζ₀ ^ (Nat.card 𝓀[T₀] - 1) = 1 := by
    rw [← map_pow, hζ₀.pow_eq_one, map_one]
  have hcK : ((Nat.card 𝓀[T₀] - 1 : ℕ) : 𝓀[K]) ≠ 0 := by
    rw [hcard]
    exact natCast_card_pow_sub_one_ne_zero hf₀
  classical
  obtain ⟨k, hk, ζ, hζ, hmem⟩ := exists_isPrimitiveRoot_forall_mem_adjoin (K := K) {ξ, ι ζ₀} (by
    intro x hx
    rw [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl
    · exact mem_unramifiedRoots_iff.2 ⟨_, by rw [Nat.cast_mul]; exact mul_ne_zero heK hcK, hξroot⟩
    · exact mem_unramifiedRoots_iff.2 ⟨_, hcK, hζ₀root⟩)
  refine ⟨k, hk, ζ, hζ, e, he, γ, hγ, ?_⟩

  have hζA : K⟮ζ⟯ ≤ adjoin K {ζ, γ} := adjoin_simple_le_iff.2 (subset_adjoin K _ (by simp))
  have hγA : γ ∈ adjoin K {ζ, γ} := subset_adjoin K _ (by simp)
  have hT₀A : ∀ x : T₀, ι x ∈ adjoin K {ζ, γ} := fun x ↦
    hζA (adjoin_simple_le_iff.2 (hmem (ι ζ₀) (by simp))
      (apply_mem_adjoin_of_adjoin_eq_top ι hζ₀gen x))
  have hξA : ξ ∈ adjoin K {ζ, γ} := hζA (hmem ξ (by simp))
  have hα'A : α' ∈ adjoin K {ζ, γ} := by
    have : α' = γ * (ξ * w') := by
      rw [hγ_def, div_mul_cancel₀ _ (mul_ne_zero hξ0 hw'0)]
    rw [this]
    exact mul_mem hγA (mul_mem hξA (hw'_def ▸ hT₀A _))
  have htop : (⊤ : IntermediateField K E) = adjoin K ((T₀ : Set E) ∪ {((α : 𝒪[E]) : E)}) := by
    rw [← restrictScalars_adjoin, hαgen, restrictScalars_top]
  intro x hx
  have hx' : (⟨x, hx⟩ : E) ∈ adjoin K ((T₀ : Set E) ∪ {((α : 𝒪[E]) : E)}) := by
    rw [← htop]
    trivial
  have hxm : E.val ⟨x, hx⟩ ∈ (adjoin K ((T₀ : Set E) ∪ {((α : 𝒪[E]) : E)})).map E.val :=
    (IntermediateField.mem_map _).2 ⟨_, hx', rfl⟩
  rw [adjoin_map] at hxm
  refine (adjoin_le_iff.2 ?_) hxm
  rintro _ ⟨y, hy, rfl⟩
  rcases hy with hy | hy
  · exact hT₀A ⟨y, hy⟩
  · rw [Set.mem_singleton_iff] at hy
    subst hy
    rw [hα'_def] at hα'A
    exact hα'A
end Structure
section Union
variable {K : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  {Ω : Type*} [Field Ω] [ValuativeRel Ω] [TopologicalSpace Ω] [IsValuativeTopology Ω]
  [Algebra K Ω] [ValuativeExtension K Ω] [Algebra.IsAlgebraic K Ω]
theorem isTameSubextension_adjoin_pair {k : ℕ} (hk : k ≠ 0) {ζ : Ω}
    (hζ : IsPrimitiveRoot ζ (Nat.card 𝓀[K] ^ k - 1)) {π : 𝒪[K]} (hπ : Irreducible π) {m : ℕ}
    (hm : Nat.Coprime m (ringChar 𝓀[K])) {γ : Ω} (hγ : γ ^ m = algebraMap K Ω π) :
    IsTameSubextension (adjoin K {ζ, γ}) := by
  obtain ⟨hfin, he⟩ := finiteDimensional_adjoin_pair_and_ramificationIndex hk hζ hπ hm hγ
  rw [isTameSubextension_iff, he]
  exact hm
variable [IsSepClosed Ω]
theorem tameExtension_eq_sup {π : 𝒪[K]} (hπ : Irreducible π) :
    tameExtension K Ω = maximalUnramifiedExtension K Ω ⊔
      adjoin K {γ : Ω | ∃ m : ℕ, Nat.Coprime m (ringChar 𝓀[K]) ∧ γ ^ m = algebraMap K Ω π} := by
  apply le_antisymm
  · refine iSup_le fun E ↦ ?_
    obtain ⟨k, hk, ζ, hζ, m, hm, γ, hγ, hE⟩ := E.2.exists_le_adjoin_pair hπ
    refine hE.trans ((adjoin_le_iff).2 ?_)
    intro x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl
    · exact le_sup_left (a := maximalUnramifiedExtension K Ω)
        (unramifiedRoots_subset_maximalUnramifiedExtension ⟨k, hk, hζ.pow_eq_one⟩)
    · exact le_sup_right (a := maximalUnramifiedExtension K Ω) (subset_adjoin K _ ⟨m, hm, hγ⟩)
  · refine sup_le (maximalUnramifiedExtension_le_tameExtension K Ω) ((adjoin_le_iff).2 ?_)
    rintro γ ⟨m, hm, hγ⟩
    obtain ⟨ζ, hζ⟩ := exists_isPrimitiveRoot_card_pow_sub_one (K := K) (Ksep := Ω) one_ne_zero
    exact (isTameSubextension_adjoin_pair one_ne_zero hζ hπ hm hγ).le_tameExtension
      (subset_adjoin K _ (by simp))
theorem tameExtension_eq_adjoin {π : 𝒪[K]} (hπ : Irreducible π) :
    tameExtension K Ω = adjoin K (unramifiedRoots K Ω ∪
      {γ : Ω | ∃ m : ℕ, Nat.Coprime m (ringChar 𝓀[K]) ∧ γ ^ m = algebraMap K Ω π}) := by
  rw [tameExtension_eq_sup hπ, maximalUnramifiedExtension_eq_adjoin, adjoin_union]
end Union
section Galois
variable {K : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  {Ω : Type*} [Field Ω] [ValuativeRel Ω] [TopologicalSpace Ω] [IsValuativeTopology Ω]
  [Algebra K Ω] [ValuativeExtension K Ω] [Algebra.IsAlgebraic K Ω] [IsSepClosed Ω]
omit [Algebra.IsAlgebraic K Ω] in

theorem normal_tameExtension [Normal K Ω] : Normal K (tameExtension K Ω) := by
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible 𝒪[K]
  rw [normal_iff_forall_map_le']
  intro σ
  rw [tameExtension_eq_adjoin hπ, adjoin_map]
  refine adjoin_le_iff.2 fun y hy ↦ subset_adjoin K _ ?_
  obtain ⟨x, hx, rfl⟩ := hy
  rcases hx with ⟨n, hn, hx⟩ | ⟨m, hm, hx⟩
  · exact Or.inl ⟨n, hn, by rw [AlgEquiv.coe_toAlgHom, ← map_pow, hx, map_one]⟩
  · exact Or.inr ⟨m, hm, by rw [AlgEquiv.coe_toAlgHom, ← map_pow, hx, AlgEquiv.commutes]⟩
omit [Algebra.IsAlgebraic K Ω] in

theorem isGalois_tameExtension_of_valued [IsGalois K Ω] : IsGalois K (tameExtension K Ω) :=
  have := Algebra.isSeparable_tower_bot_of_isSeparable K (tameExtension K Ω) Ω
  have := normal_tameExtension (K := K) (Ω := Ω)
  isGalois_iff.2 ⟨inferInstance, inferInstance⟩
end Galois
section SeparableClosure
variable {K : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  {Ω : Type*} [Field Ω] [Algebra K Ω] [IsSepClosure K Ω]
instance isGalois_tameExtension : IsGalois K (tameExtension K Ω) := by
  let := algebraicValuativeRel K Ω
  let := algebraicTopology K Ω
  have := algebraicValuativeRel_valuativeExtension K Ω
  have := algebraicTopology_isValuativeTopology K Ω
  have : IsSepClosed Ω := IsSepClosure.sep_closed K
  exact isGalois_tameExtension_of_valued
end SeparableClosure
end GroundTheory.LocalField


