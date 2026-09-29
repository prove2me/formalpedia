-- Prove2me | solution 1 for AlgebraicCurve.Place.eq_of_comap_eq_of_forall_mem_nonunits_iff
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:01.734404+00:00
-- url     : https://prove2.me/submissions/e68cf470-b08d-58ff-9528-016c56a4b81b

import Mathlib
import Definitions.Def_AlgebraicCurve_DivisorClassGroup
import Theorems.Thm_ValuationSubring_mem_adjoin_singleton_of_isIntegral_of_separable_minpoly
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicCurve_Place_eq_of_comap_eq_of_forall_mem_nonunits_iff

set_option autoImplicit false

p2m_open "AlgebraicCurve P2MW.S_AlgebraicCurve_Place_eq_of_comap_eq_of_forall_mem_nonunits_iff.AlgebraicCurve"
open scoped Pointwise

namespace AlgebraicCurve
p2m_export "AlgebraicCurve" "Place"
namespace ValLoc
p2m_open "AlgebraicCurve"

section Transport

variable {K K' : Type*} [Field K] [Field K']

theorem mem_nonunits_comap_iff (A : ValuationSubring K') (φ : K →+* K') (x : K) :
    x ∈ (A.comap φ).nonunits ↔ φ x ∈ A.nonunits := by
  rw [ValuationSubring.mem_nonunits_iff_or, ValuationSubring.mem_nonunits_iff_or, map_eq_zero_iff φ φ.injective,
    ← map_inv₀, ValuationSubring.mem_comap]

theorem inv_mem_of_not_mem_nonunits (A : ValuationSubring K) {x : K} (h : x ∉ A.nonunits) : x⁻¹ ∈ A := by
  rw [ValuationSubring.mem_nonunits_iff_or, not_or, not_not] at h
  exact h.2

theorem ne_top_of_mem_nonunits (A : ValuationSubring K) {x : K} (hx : x ∈ A.nonunits) (hx0 : x ≠ 0) : A ≠ ⊤ := by
  intro h
  rw [ValuationSubring.mem_nonunits_iff_or] at hx
  rcases hx with hx | hx
  · exact hx0 hx
  · apply hx; rw [h]; trivial

end Transport

section PrimElt

variable {κ : Type*} [Field κ] {F : Type*} [Field F] [Algebra κ F]
  {κ' : Type*} [Field κ'] [Algebra κ κ']
  {F' : Type*} [Field F'] [Algebra κ' F'] [Algebra F F'] [Algebra κ F']
  [IsScalarTower κ F F'] [IsScalarTower κ κ' F']

theorem exists_finset_mem_adjoin (hgen : Algebra.adjoin F (Set.range (algebraMap κ' F')) = ⊤) (x : F') :
    ∃ T : Finset κ', x ∈ Algebra.adjoin F ((algebraMap κ' F') '' (T : Set κ')) := by
  classical
  have hx : x ∈ Algebra.adjoin F (Set.range (algebraMap κ' F')) := by rw [hgen]; exact Algebra.mem_top
  induction hx using Algebra.adjoin_induction with
  | mem y hy =>
      obtain ⟨a, rfl⟩ := hy
      exact ⟨{a}, Algebra.subset_adjoin ⟨a, by simp, rfl⟩⟩
  | algebraMap r => exact ⟨∅, Subalgebra.algebraMap_mem _ r⟩
  | add y z _ _ hy hz =>
      obtain ⟨T₁, h₁⟩ := hy
      obtain ⟨T₂, h₂⟩ := hz
      refine ⟨T₁ ∪ T₂, Subalgebra.add_mem _ (Algebra.adjoin_mono ?_ h₁) (Algebra.adjoin_mono ?_ h₂)⟩
      · exact Set.image_mono (by simp)
      · exact Set.image_mono (by simp)
  | mul y z _ _ hy hz =>
      obtain ⟨T₁, h₁⟩ := hy
      obtain ⟨T₂, h₂⟩ := hz
      refine ⟨T₁ ∪ T₂, Subalgebra.mul_mem _ (Algebra.adjoin_mono ?_ h₁) (Algebra.adjoin_mono ?_ h₂)⟩
      · exact Set.image_mono (by simp)
      · exact Set.image_mono (by simp)

variable [Algebra.IsAlgebraic κ κ'] [Algebra.IsSeparable κ κ']

theorem exists_mem_adjoin_simple (hgen : Algebra.adjoin F (Set.range (algebraMap κ' F')) = ⊤) (x : F') :
    ∃ c : F', c ∈ Set.range (algebraMap κ' F') ∧ IsIntegral κ c ∧ (minpoly κ c).Separable ∧
      x ∈ IntermediateField.adjoin F ({c} : Set F') := by
  classical
  obtain ⟨T, hT⟩ := exists_finset_mem_adjoin hgen x
  set E : IntermediateField κ κ' := IntermediateField.adjoin κ (T : Set κ') with hE
  haveI : FiniteDimensional κ E :=
    IntermediateField.finiteDimensional_adjoin fun t _ => (Algebra.IsAlgebraic.isAlgebraic (R := κ) t).isIntegral
  obtain ⟨α, hα⟩ := Field.exists_primitive_element κ E

  let g : E →ₐ[κ] F' := (IsScalarTower.toAlgHom κ κ' F').comp E.val
  refine ⟨g α, ⟨(α : κ'), rfl⟩, (Algebra.IsIntegral.isIntegral (R := κ) α).map g, ?_, ?_⟩
  · rw [minpoly.algHom_eq g g.toRingHom.injective α]
    exact Algebra.IsSeparable.isSeparable κ α
  ·
    have hT' : (algebraMap κ' F') '' (T : Set κ') ⊆ (IntermediateField.adjoin F ({g α} : Set F') : Set F') := by
      rintro _ ⟨t, ht, rfl⟩
      have htE : (⟨t, IntermediateField.subset_adjoin κ _ ht⟩ : E) ∈ IntermediateField.adjoin κ ({α} : Set E) := by
        rw [hα]; exact IntermediateField.mem_top
      have hmap := IntermediateField.adjoin_map κ ({α} : Set E) g
      have : g ⟨t, IntermediateField.subset_adjoin κ _ ht⟩ ∈ (IntermediateField.adjoin κ ({α} : Set E)).map g :=
        ⟨_, htE, rfl⟩
      rw [hmap, Set.image_singleton] at this
      have hle : IntermediateField.adjoin κ ({g α} : Set F') ≤
          (IntermediateField.adjoin F ({g α} : Set F')).restrictScalars κ :=
        IntermediateField.adjoin_le_iff.mpr (IntermediateField.subset_adjoin F _)
      exact hle this
    exact (Algebra.adjoin_le (S := (IntermediateField.adjoin F ({g α} : Set F')).toSubalgebra) hT') hT

end PrimElt

end AlgebraicCurve.ValLoc

namespace AlgebraicCurve
p2m_export "AlgebraicCurve" "Place"
namespace ValLoc
p2m_open "AlgebraicCurve"

section Key

variable {κ : Type*} [Field κ] {F : Type*} [Field F] [Algebra κ F]
  {κ' : Type*} [Field κ'] [Algebra κ κ']
  {F' : Type*} [Field F'] [Algebra κ' F'] [Algebra F F'] [Algebra κ F']
  [IsScalarTower κ F F'] [IsScalarTower κ κ' F']

theorem isIntegral_map_of_comap_eq {P : Place κ F} {W : Place κ' F'}
    (hW : W.toValuationSubring.comap (algebraMap F F') = P.toValuationSubring)
    {L : IntermediateField F F'} {z : L}
    (hz : @IsIntegral P.toValuationSubring L _ _ (((algebraMap F L).comp P.toValuationSubring.subtype).toAlgebra) z) :
    IsIntegral W.toValuationSubring ((z : F')) := by
  letI : Algebra P.toValuationSubring L := ((algebraMap F L).comp P.toValuationSubring.subtype).toAlgebra

  have hmem : ∀ o : P.toValuationSubring, algebraMap F F' (o : F) ∈ W.toValuationSubring := fun o => by
    have h : (o : F) ∈ W.toValuationSubring.comap (algebraMap F F') := by rw [hW]; exact o.2
    exact h
  let φ : P.toValuationSubring →+* W.toValuationSubring :=
    ((algebraMap F F').comp P.toValuationSubring.subtype).codRestrict W.toValuationSubring.toSubring (fun o => hmem o)
  obtain ⟨p, hp, hpz⟩ := hz
  refine ⟨p.map φ, hp.map φ, ?_⟩
  have h1 : (algebraMap L F') (Polynomial.eval₂ (algebraMap P.toValuationSubring L) z p) = 0 := by rw [hpz, map_zero]
  rw [Polynomial.hom_eval₂] at h1
  rw [Polynomial.eval₂_map]
  convert h1 using 1
  rfl

theorem mem_iff_mem_of_mem_adjoin_simple [Algebra.IsAlgebraic κ κ'] [Algebra.IsSeparable κ κ']
    (P : Place κ F) (W₁ W₂ : Place κ' F')
    (h₁ : W₁.toValuationSubring.comap (algebraMap F F') = P.toValuationSubring)
    (h₂ : W₂.toValuationSubring.comap (algebraMap F F') = P.toValuationSubring)
    (hc : ∀ x ∈ Subring.closure
        ((algebraMap F F') '' (P.toValuationSubring : Set F) ∪ Set.range (algebraMap κ' F')),
      x ∈ W₁.toValuationSubring.nonunits ↔ x ∈ W₂.toValuationSubring.nonunits)
    (c : F') (hcR : c ∈ Set.range (algebraMap κ' F')) (hci : IsIntegral κ c) (hsep : (minpoly κ c).Separable)
    (x : F') (hx : x ∈ IntermediateField.adjoin F ({c} : Set F')) :
    x ∈ W₁.toValuationSubring ↔ x ∈ W₂.toValuationSubring := by
  classical

  set L : IntermediateField F F' := IntermediateField.adjoin F ({c} : Set F') with hLdef
  set 𝒪 : ValuationSubring F := P.toValuationSubring with h𝒪def
  letI : Algebra 𝒪 L := ((algebraMap F L).comp 𝒪.subtype).toAlgebra
  haveI : IsScalarTower 𝒪 F L := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  haveI : IsPrincipalIdealRing 𝒪 := P.isPrincipalIdealRing'
  haveI : IsDedekindDomain 𝒪 := inferInstance
  have hciF : IsIntegral F c := hci.tower_top
  haveI : FiniteDimensional F L := IntermediateField.adjoin.finiteDimensional hciF
  haveI : Algebra.IsSeparable F L :=
    (IntermediateField.isSeparable_adjoin_simple_iff_isSeparable (F := F) (x := c)).mpr
      (IsSeparable.tower_top F (show IsSeparable κ c from hsep))

  set S := integralClosure 𝒪 L with hSdef
  haveI : IsDedekindDomain S := integralClosure.isDedekindDomain 𝒪 F L
  haveI : IsFractionRing S L := IsIntegralClosure.isFractionRing_of_finite_extension 𝒪 F L S

  let A : Place κ' F' → ValuationSubring L := fun W => W.toValuationSubring.comap (algebraMap L F')
  have hA_mem : ∀ (W : Place κ' F') (y : L), y ∈ A W ↔ (y : F') ∈ W.toValuationSubring := fun W y => Iff.rfl

  have hSA : ∀ W : Place κ' F', W.toValuationSubring.comap (algebraMap F F') = 𝒪 → S.toSubring ≤ (A W).toSubring := by
    intro W hW y hy
    have hint : IsIntegral W.toValuationSubring ((y : F')) := isIntegral_map_of_comap_eq hW hy
    exact (hA_mem W y).mpr (IsIntegrallyClosed.isIntegral_iff.mp hint |>.choose_spec ▸ (Subtype.mem _))

  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible 𝒪
  have hπ0 : (π : F) ≠ 0 := by
    intro h; apply hπ.ne_zero; exact Subtype.ext h
  have hπm : (π : F) ∈ 𝒪.nonunits := by
    rw [ValuationSubring.mem_nonunits_iff_exists_mem_maximalIdeal]
    exact ⟨π.2, by simpa using hπ.not_isUnit⟩
  have hπA : ∀ W : Place κ' F', W.toValuationSubring.comap (algebraMap F F') = 𝒪 →
      (algebraMap F L (π : F) : L) ∈ (A W).nonunits := by
    intro W hW
    rw [mem_nonunits_comap_iff]
    show algebraMap F F' (π : F) ∈ W.toValuationSubring.nonunits
    rw [← mem_nonunits_comap_iff, hW]; exact hπm
  have hA_ne_top : ∀ W : Place κ' F', W.toValuationSubring.comap (algebraMap F F') = 𝒪 → A W ≠ ⊤ := fun W hW =>
    ne_top_of_mem_nonunits (A W) (hπA W hW) (by
      rw [map_ne_zero_iff _ (algebraMap F L).injective]; exact hπ0)

  let incl : ∀ W : Place κ' F', W.toValuationSubring.comap (algebraMap F F') = 𝒪 → (S →+* (A W)) :=
    fun W hW => Subring.inclusion (hSA W hW)
  let 𝔓 : ∀ W : Place κ' F', W.toValuationSubring.comap (algebraMap F F') = 𝒪 → Ideal S :=
    fun W hW => (IsLocalRing.maximalIdeal (A W)).comap (incl W hW)
  have h𝔓mem : ∀ (W : Place κ' F') (hW) (s : S), s ∈ 𝔓 W hW ↔ (s : L) ∈ (A W).nonunits := by
    intro W hW s
    rw [Ideal.mem_comap, ← ValuationSubring.coe_mem_nonunits_iff]; rfl
  have h𝔓prime : ∀ W hW, (𝔓 W hW).IsPrime := fun W hW => Ideal.comap_isPrime _ _
  have hπS : IsIntegral 𝒪 (algebraMap F L (π : F)) := by
    have : algebraMap F L (π : F) = algebraMap 𝒪 L π := rfl
    rw [this]; exact isIntegral_algebraMap
  have h𝔓ne : ∀ W hW, 𝔓 W hW ≠ ⊥ := by
    intro W hW h
    have hmem : (⟨algebraMap F L (π : F), hπS⟩ : S) ∈ 𝔓 W hW := (h𝔓mem W hW _).mpr (hπA W hW)
    rw [h, Ideal.mem_bot, Subtype.ext_iff] at hmem
    exact (map_ne_zero_iff _ (algebraMap F L).injective).mpr hπ0 hmem
  let v : ∀ W : Place κ' F', W.toValuationSubring.comap (algebraMap F F') = 𝒪 → IsDedekindDomain.HeightOneSpectrum S :=
    fun W hW => ⟨𝔓 W hW, h𝔓prime W hW, h𝔓ne W hW⟩

  have hloc : ∀ W hW, IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime L (v W hW) = A W := by
    intro W hW
    refine ValuationSubring.eq_of_le_of_ne_top _ ?_ (hA_ne_top W hW)
    rintro y ⟨a, s, hs, rfl⟩
    have ha : ((a : S) : L) ∈ A W := hSA W hW a.2
    have hsA : ((s : S) : L) ∈ A W := hSA W hW s.2
    have hsn : ((s : S) : L) ∉ (A W).nonunits := fun hn => hs ((h𝔓mem W hW s).mpr hn)
    exact (A W).mul_mem _ _ ha (inv_mem_of_not_mem_nonunits (A W) hsn)

  have hgenL : IntermediateField.adjoin F ({(⟨c, IntermediateField.mem_adjoin_simple_self F c⟩ : L)} : Set L) = ⊤ := by
    apply IntermediateField.lift_injective
    rw [IntermediateField.lift_top]
    show IntermediateField.map L.val _ = L
    rw [IntermediateField.adjoin_map, Set.image_singleton]
    rfl
  have hR : ∀ z : L, z ∈ Algebra.adjoin 𝒪 ({(⟨c, IntermediateField.mem_adjoin_simple_self F c⟩ : L)} : Set L) →
      (z : F') ∈ Subring.closure ((algebraMap F F') '' (P.toValuationSubring : Set F) ∪ Set.range (algebraMap κ' F')) := by
    intro z hz
    induction hz using Algebra.adjoin_induction with
    | mem y hy =>
        rw [Set.mem_singleton_iff] at hy; subst hy
        exact Subring.subset_closure (Or.inr hcR)
    | algebraMap o => exact Subring.subset_closure (Or.inl ⟨o, o.2, rfl⟩)
    | add y y' _ _ hy hy' => rw [IntermediateField.coe_add]; exact Subring.add_mem _ hy hy'
    | mul y y' _ _ hy hy' => rw [IntermediateField.coe_mul]; exact Subring.mul_mem _ hy hy'
  have h𝔓eq : 𝔓 W₁ h₁ = 𝔓 W₂ h₂ := by
    ext s
    rw [h𝔓mem W₁ h₁, h𝔓mem W₂ h₂, mem_nonunits_comap_iff, mem_nonunits_comap_iff]
    apply hc
    apply hR
    have hcL : IsIntegral κ (⟨c, IntermediateField.mem_adjoin_simple_self F c⟩ : L) := by
      refine (isIntegral_algHom_iff ((L.val).restrictScalars κ) Subtype.val_injective).mp ?_
      exact hci
    have hsepL : (minpoly κ (⟨c, IntermediateField.mem_adjoin_simple_self F c⟩ : L)).Separable := by
      rw [← minpoly.algHom_eq ((L.val).restrictScalars κ) Subtype.val_injective]
      exact hsep
    exact ValuationSubring.mem_adjoin_singleton_of_isIntegral_of_separable_minpoly 𝒪 P.algebraMap_mem' _ hcL hsepL hgenL (s : L) s.2

  have hAeq : A W₁ = A W₂ := by
    rw [← hloc W₁ h₁, ← hloc W₂ h₂]
    have : v W₁ h₁ = v W₂ h₂ := IsDedekindDomain.HeightOneSpectrum.ext h𝔓eq
    rw [this]
  have := congrArg (fun B : ValuationSubring L => (⟨x, hx⟩ : L) ∈ B) hAeq
  simpa [hA_mem] using this

end Key

end AlgebraicCurve.ValLoc

open AlgebraicCurve.ValLoc in

theorem solution
    {κ : Type*} [Field κ] {F : Type*} [Field F] [Algebra κ F]
    {κ' : Type*} [Field κ'] [Algebra κ κ'] [Algebra.IsAlgebraic κ κ'] [Algebra.IsSeparable κ κ']
    {F' : Type*} [Field F'] [Algebra κ' F'] [Algebra F F'] [Algebra κ F']
    [IsScalarTower κ F F'] [IsScalarTower κ κ' F'] [Algebra.IsIntegral F F']
    (hgen : Algebra.adjoin F (Set.range (algebraMap κ' F')) = ⊤)
    (P : Place κ F) (W₁ W₂ : Place κ' F')
    (h₁ : W₁.toValuationSubring.comap (algebraMap F F') = P.toValuationSubring)
    (h₂ : W₂.toValuationSubring.comap (algebraMap F F') = P.toValuationSubring)
    (hc : ∀ x ∈ Subring.closure
        ((algebraMap F F') '' (P.toValuationSubring : Set F) ∪ Set.range (algebraMap κ' F')),
      x ∈ W₁.toValuationSubring.nonunits ↔ x ∈ W₂.toValuationSubring.nonunits) :
    W₁ = W₂ := by
  ext x
  obtain ⟨c, hcR, hci, hsep, hx⟩ := exists_mem_adjoin_simple (κ := κ) hgen x
  exact mem_iff_mem_of_mem_adjoin_simple P W₁ W₂ h₁ h₂ hc c hcR hci hsep x hx

end S_AlgebraicCurve_Place_eq_of_comap_eq_of_forall_mem_nonunits_iff
end P2MW
export P2MW.S_AlgebraicCurve_Place_eq_of_comap_eq_of_forall_mem_nonunits_iff (solution)
