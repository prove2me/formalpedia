-- Prove2me | solution 1 for AlgebraicCurve.existsUnique_point_localRing_eq_and_specializes_closedPoint_and_forall_eq_of_isProper_of_isIntegrallyClosed
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:02.4153+00:00
-- url     : https://prove2.me/submissions/f0308705-3893-50ee-a564-8e653ba32cfa

import Mathlib
import Definitions.Def_AlgebraicCurve_SemistableModel
import Definitions.Def_AlgebraicCurve_IsCurveOver
import Theorems.Thm_AlgebraicGeometry_Scheme_exists_eq_closedPoint_and_forall_mem_of_valuationSubring
import Theorems.Thm_AlgebraicGeometry_Scheme_eq_of_forall_mem_valuationSubring_of_isSeparated
import Theorems.Thm_AlgebraicCurve_exists_place_toSubring_eq_of_isIntegrallyClosedIn_of_isNoetherianRing
import Theorems.Thm_AlgebraicGeometry_Scheme_exists_specializes_isLocalization_atPrime_stalk
import Theorems.Thm_AlgebraicGeometry_Scheme_exists_fromSpecStalk_specializes_and_mem_iff_residue_eq_zero_and_eq_genericPoint_iff
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicCurve_existsUnique_point_localRing_eq_and_specializes_closedPoint_and_forall_eq_of_isProper_of_isIntegrallyClosed

set_option autoImplicit false

open AlgebraicCurve IsLocalRing CategoryTheory AlgebraicGeometry

namespace M3aGlue

section PlaceEval

variable {L F : Type} [Field L] [IsAlgClosed L] [Field F] [Algebra L F] [IsCurveOver L F]

theorem algebraMap_residueField_bijective (P : Place L F) :
    Function.Bijective (algebraMap L P.ResidueField) := by
  haveI : Module.Finite L P.ResidueField := IsCurveOver.finiteResidue P
  haveI : Algebra.IsIntegral L P.ResidueField := Algebra.IsIntegral.of_finite L P.ResidueField
  exact IsAlgClosed.algebraMap_bijective_of_isIntegral

noncomputable def residueEquiv (P : Place L F) : L ≃+* P.ResidueField :=
  RingEquiv.ofBijective (algebraMap L P.ResidueField) (algebraMap_residueField_bijective P)

@[scoped simp] theorem residueEquiv_apply (P : Place L F) (a : L) :
    residueEquiv P a = algebraMap L P.ResidueField a := rfl

noncomputable def evalHom (P : Place L F) : ↥P.toValuationSubring →+* L :=
  (residueEquiv P).symm.toRingHom.comp (IsLocalRing.residue ↥P.toValuationSubring)

theorem algebraMap_evalHom (P : Place L F) (x : ↥P.toValuationSubring) :
    algebraMap L P.ResidueField (evalHom P x) = IsLocalRing.residue _ x := by
  change residueEquiv P ((residueEquiv P).symm (IsLocalRing.residue _ x)) = _
  exact (residueEquiv P).apply_symm_apply _

theorem evalAt_eq_evalHom (P : Place L F) {f : F} (hf : f ∈ P.toValuationSubring) :
    P.evalAt f = evalHom P ⟨f, hf⟩ := by
  rw [Place.evalAt_of_mem _ hf]
  apply (algebraMap_residueField_bijective P).1
  rw [Place.algebraMap_residueInv _ (algebraMap_residueField_bijective P).2, algebraMap_evalHom]

theorem evalHom_eq_zero_iff (P : Place L F) (x : ↥P.toValuationSubring) :
    evalHom P x = 0 ↔ x ∈ maximalIdeal ↥P.toValuationSubring := by
  rw [← (algebraMap_residueField_bijective P).1.eq_iff, algebraMap_evalHom, map_zero,
    IsLocalRing.residue_eq_zero_iff]

theorem isUnit_iff_evalHom_ne_zero (P : Place L F) (x : ↥P.toValuationSubring) :
    IsUnit x ↔ evalHom P x ≠ 0 := by
  rw [Ne, evalHom_eq_zero_iff]
  exact (IsLocalRing.notMem_maximalIdeal).symm

theorem evalHom_algebraMap (P : Place L F) (a : L) :
    evalHom P ⟨algebraMap L F a, P.algebraMap_mem' a⟩ = a := by
  apply (algebraMap_residueField_bijective P).1
  rw [algebraMap_evalHom]
  change IsLocalRing.residue _ (algebraMap L ↥P.toValuationSubring a) = _
  rw [IsScalarTower.algebraMap_apply L ↥P.toValuationSubring P.ResidueField a]
  rfl

end PlaceEval

section ValHelpers

variable {K : Type} [Field K]

theorem isUnit_iff_inv_mem (W : ValuationSubring K) {w : K} (hw : w ∈ W) (hw0 : w ≠ 0) :
    IsUnit (⟨w, hw⟩ : ↥W) ↔ w⁻¹ ∈ W := by
  constructor
  · rintro ⟨u, hu⟩
    have h1 : (u : ↥W).1 * (↑u⁻¹ : ↥W).1 = 1 := by
      rw [← Subring.coe_mul]; exact congrArg Subtype.val u.mul_inv
    rw [hu] at h1
    rw [← eq_inv_of_mul_eq_one_right h1]
    exact Subtype.mem _
  · intro h
    exact ⟨⟨⟨w, hw⟩, ⟨w⁻¹, h⟩, Subtype.ext (mul_inv_cancel₀ hw0), Subtype.ext (inv_mul_cancel₀ hw0)⟩, rfl⟩

theorem not_isUnit_zero_mk (W : ValuationSubring K) : ¬ IsUnit (⟨(0 : K), zero_mem W⟩ : ↥W) := by
  have : (⟨(0 : K), zero_mem W⟩ : ↥W) = 0 := rfl
  rw [this]; exact not_isUnit_zero

end ValHelpers

section VP

variable {L F : Type} [Field L] [IsAlgClosed L] [Field F] [Algebra L F] [IsCurveOver L F]

noncomputable def VP (A : ValuationSubring L) (P : Place L F) : ValuationSubring F where
  carrier := {f | ∃ hf : f ∈ P.toValuationSubring, evalHom P ⟨f, hf⟩ ∈ A}
  mul_mem' := by
    rintro f g ⟨hf, hfA⟩ ⟨hg, hgA⟩
    refine ⟨mul_mem hf hg, ?_⟩
    have : (⟨f * g, mul_mem hf hg⟩ : ↥P.toValuationSubring) = ⟨f, hf⟩ * ⟨g, hg⟩ := rfl
    rw [this, map_mul]; exact mul_mem hfA hgA
  one_mem' := ⟨one_mem _, by
    have : (⟨(1 : F), one_mem _⟩ : ↥P.toValuationSubring) = 1 := rfl
    rw [this, map_one]; exact one_mem _⟩
  add_mem' := by
    rintro f g ⟨hf, hfA⟩ ⟨hg, hgA⟩
    refine ⟨add_mem hf hg, ?_⟩
    have : (⟨f + g, add_mem hf hg⟩ : ↥P.toValuationSubring) = ⟨f, hf⟩ + ⟨g, hg⟩ := rfl
    rw [this, map_add]; exact add_mem hfA hgA
  zero_mem' := ⟨zero_mem _, by
    have : (⟨(0 : F), zero_mem _⟩ : ↥P.toValuationSubring) = 0 := rfl
    rw [this, map_zero]; exact zero_mem _⟩
  neg_mem' := by
    rintro f ⟨hf, hfA⟩
    refine ⟨neg_mem hf, ?_⟩
    have : (⟨-f, neg_mem hf⟩ : ↥P.toValuationSubring) = -⟨f, hf⟩ := rfl
    rw [this, map_neg]; exact neg_mem hfA
  mem_or_inv_mem' := by
    intro f
    by_cases hf : f ∈ P.toValuationSubring
    · by_cases hfA : evalHom P ⟨f, hf⟩ ∈ A
      · exact Or.inl ⟨hf, hfA⟩
      ·
        right
        have hne : evalHom P ⟨f, hf⟩ ≠ 0 := fun h => hfA (h ▸ zero_mem _)
        have hu : IsUnit (⟨f, hf⟩ : ↥P.toValuationSubring) := (isUnit_iff_evalHom_ne_zero P _).2 hne
        have hf0 : f ≠ 0 := fun h => hne (by
          have : (⟨f, hf⟩ : ↥P.toValuationSubring) = 0 := Subtype.ext h
          rw [this, map_zero])
        obtain ⟨u, hu⟩ := hu
        have hinv : f⁻¹ = ((u⁻¹ : (↥P.toValuationSubring)ˣ) : ↥P.toValuationSubring) := by
          have h1 : (u : ↥P.toValuationSubring).1 * (↑u⁻¹ : ↥P.toValuationSubring).1 = 1 := by
            rw [← Subring.coe_mul]
            exact congrArg Subtype.val u.mul_inv
          rw [hu] at h1
          exact (eq_inv_of_mul_eq_one_right h1).symm ▸ rfl
        have hfi : f⁻¹ ∈ P.toValuationSubring := by rw [hinv]; exact Subtype.mem _
        refine ⟨hfi, ?_⟩
        have hprod : evalHom P ⟨f, hf⟩ * evalHom P ⟨f⁻¹, hfi⟩ = 1 := by
          rw [← map_mul]
          have : (⟨f, hf⟩ : ↥P.toValuationSubring) * ⟨f⁻¹, hfi⟩ = 1 :=
            Subtype.ext (mul_inv_cancel₀ hf0)
          rw [this, map_one]
        have : evalHom P ⟨f⁻¹, hfi⟩ = (evalHom P ⟨f, hf⟩)⁻¹ := (eq_inv_of_mul_eq_one_right hprod)
        rw [this]
        rcases A.mem_or_inv_mem (evalHom P ⟨f, hf⟩) with h | h
        · exact absurd h hfA
        · exact h
    ·
      right
      have hfi : f⁻¹ ∈ P.toValuationSubring := (P.toValuationSubring.mem_or_inv_mem f).resolve_left hf
      refine ⟨hfi, ?_⟩
      have hmax : (⟨f⁻¹, hfi⟩ : ↥P.toValuationSubring) ∈ maximalIdeal _ := by
        intro hu
        obtain ⟨u, hu⟩ := hu
        apply hf
        have hf0 : f ≠ 0 := by rintro rfl; exact hf (zero_mem _)
        have : f = ((u⁻¹ : (↥P.toValuationSubring)ˣ) : ↥P.toValuationSubring) := by
          have h1 : (u : ↥P.toValuationSubring).1 * (↑u⁻¹ : ↥P.toValuationSubring).1 = 1 := by
            rw [← Subring.coe_mul]
            exact congrArg Subtype.val u.mul_inv
          rw [hu] at h1
          have := eq_inv_of_mul_eq_one_right h1
          rw [inv_inv] at this
          exact this.symm ▸ rfl
        rw [this]; exact Subtype.mem _
      rw [(evalHom_eq_zero_iff P _).2 hmax]
      exact zero_mem _

theorem mem_VP_iff (A : ValuationSubring L) (P : Place L F) (f : F) :
    f ∈ VP A P ↔ ∃ hf : f ∈ P.toValuationSubring, evalHom P ⟨f, hf⟩ ∈ A := Iff.rfl

theorem mem_of_mem_VP {A : ValuationSubring L} {P : Place L F} {f : F} (h : f ∈ VP A P) :
    f ∈ P.toValuationSubring := h.1

theorem evalAt_mem_of_mem_VP {A : ValuationSubring L} {P : Place L F} {f : F} (h : f ∈ VP A P) :
    P.evalAt f ∈ A := by
  rw [evalAt_eq_evalHom P h.1]; exact h.2

theorem isUnit_VP_iff (A : ValuationSubring L) (P : Place L F) (f : F) (h : f ∈ VP A P) :
    IsUnit (⟨f, h⟩ : ↥(VP A P)) ↔ IsUnit (⟨P.evalAt f, evalAt_mem_of_mem_VP h⟩ : ↥A) := by
  obtain ⟨hf, hfA⟩ := h
  have hev : P.evalAt f = evalHom P ⟨f, hf⟩ := evalAt_eq_evalHom P hf
  by_cases hf0 : f = 0
  · subst hf0
    have h0 : P.evalAt (0 : F) = 0 := by
      rw [hev]
      have : (⟨(0 : F), hf⟩ : ↥P.toValuationSubring) = 0 := rfl
      rw [this, map_zero]
    constructor
    · intro hu; exact absurd hu (not_isUnit_zero_mk _)
    · intro hu
      exfalso
      have : (⟨P.evalAt (0 : F), evalAt_mem_of_mem_VP ⟨hf, hfA⟩⟩ : ↥A) = 0 := Subtype.ext h0
      rw [this] at hu; exact not_isUnit_zero hu
  rw [isUnit_iff_inv_mem (VP A P) ⟨hf, hfA⟩ hf0]
  by_cases he0 : evalHom P ⟨f, hf⟩ = 0
  ·
    have hfm : (⟨f, hf⟩ : ↥P.toValuationSubring) ∈ maximalIdeal _ := (evalHom_eq_zero_iff P _).1 he0
    have hfi : f⁻¹ ∉ P.toValuationSubring := fun hfi =>
      hfm ((isUnit_iff_inv_mem P.toValuationSubring hf hf0).2 hfi)
    have h0 : (⟨P.evalAt f, evalAt_mem_of_mem_VP ⟨hf, hfA⟩⟩ : ↥A) = 0 :=
      Subtype.ext (show P.evalAt f = ((0 : ↥A) : L) by rw [hev, he0]; rfl)
    rw [h0]
    constructor
    · intro h; exact absurd (mem_of_mem_VP h) hfi
    · intro h; exact absurd h not_isUnit_zero
  ·
    have hu : IsUnit (⟨f, hf⟩ : ↥P.toValuationSubring) := (isUnit_iff_evalHom_ne_zero P _).2 he0
    have hfi : f⁻¹ ∈ P.toValuationSubring := (isUnit_iff_inv_mem P.toValuationSubring hf hf0).1 hu
    have hinv : evalHom P ⟨f⁻¹, hfi⟩ = (evalHom P ⟨f, hf⟩)⁻¹ := by
      apply eq_inv_of_mul_eq_one_right
      rw [← map_mul]
      have : (⟨f, hf⟩ : ↥P.toValuationSubring) * ⟨f⁻¹, hfi⟩ = 1 := Subtype.ext (mul_inv_cancel₀ hf0)
      rw [this, map_one]
    have hne : (P.evalAt f) ≠ 0 := by rw [hev]; exact he0
    rw [isUnit_iff_inv_mem A (evalAt_mem_of_mem_VP ⟨hf, hfA⟩) hne, mem_VP_iff]
    constructor
    · rintro ⟨hfi', hA'⟩
      rw [hev, ← hinv]; convert hA'
    · intro hA'
      refine ⟨hfi, ?_⟩
      rw [hinv, ← hev]; exact hA'

noncomputable def evVP (A : ValuationSubring L) (P : Place L F) : ↥(VP A P) →+* ↥A where
  toFun f := ⟨evalHom P ⟨(f : F), f.2.1⟩, f.2.2⟩
  map_one' := by
    apply Subtype.ext
    change evalHom P ⟨1, _⟩ = 1
    exact map_one (evalHom P)
  map_mul' f g := by
    apply Subtype.ext
    change evalHom P ⟨(f : F) * (g : F), _⟩ = evalHom P ⟨(f : F), f.2.1⟩ * evalHom P ⟨(g : F), g.2.1⟩
    rw [← map_mul]; rfl
  map_zero' := by
    apply Subtype.ext
    change evalHom P ⟨0, _⟩ = 0
    exact map_zero (evalHom P)
  map_add' f g := by
    apply Subtype.ext
    change evalHom P ⟨(f : F) + (g : F), _⟩ = evalHom P ⟨(f : F), f.2.1⟩ + evalHom P ⟨(g : F), g.2.1⟩
    rw [← map_add]; rfl

theorem coe_evVP (A : ValuationSubring L) (P : Place L F) (f : ↥(VP A P)) :
    ((evVP A P f : ↥A) : L) = evalHom P ⟨(f : F), f.2.1⟩ := rfl

theorem coe_evVP' (A : ValuationSubring L) (P : Place L F) (f : ↥(VP A P)) :
    ((evVP A P f : ↥A) : L) = P.evalAt (f : F) := by
  rw [coe_evVP, evalAt_eq_evalHom P f.2.1]

theorem algebraMap_mem_VP (A : ValuationSubring L) (P : Place L F) (a : ↥A) :
    algebraMap L F (a : L) ∈ VP A P :=
  ⟨P.algebraMap_mem' _, by rw [evalHom_algebraMap]; exact a.2⟩

end VP

end M3aGlue
p2m_reactivate "P2MW.S_AlgebraicCurve_existsUnique_point_localRing_eq_and_specializes_closedPoint_and_forall_eq_of_isProper_of_isIntegrallyClosed.M3aGlue"

namespace M3aGlue

section Transport

variable {F : Type} [Field F] {X : Scheme.{0}} [IsIntegral X] (φ : F ≃+* X.functionField)

noncomputable def locHom (z : X) : X.presheaf.stalk z →+* F :=
  (φ.symm : X.functionField ≃+* F).toRingHom.comp (algebraMap (X.presheaf.stalk z) X.functionField)

theorem locHom_apply (z : X) (s : X.presheaf.stalk z) :
    locHom φ z s = φ.symm (algebraMap (X.presheaf.stalk z) X.functionField s) := rfl

theorem φ_locHom (z : X) (s : X.presheaf.stalk z) :
    φ (locHom φ z s) = algebraMap (X.presheaf.stalk z) X.functionField s := by
  rw [locHom_apply, RingEquiv.apply_symm_apply]

theorem locHom_injective (z : X) : Function.Injective (locHom φ z) :=
  φ.symm.injective.comp (IsFractionRing.injective (X.presheaf.stalk z) X.functionField)

theorem range_locHom (z : X) : (locHom φ z).range = SemistableModel.localRing X φ z := rfl

theorem mem_localRing_iff (z : X) (f : F) :
    f ∈ SemistableModel.localRing X φ z ↔ ∃ s, locHom φ z s = f := Iff.rfl

theorem locHom_mem (z : X) (s : X.presheaf.stalk z) : locHom φ z s ∈ SemistableModel.localRing X φ z :=
  ⟨s, rfl⟩

noncomputable def locEquiv (z : X) : X.presheaf.stalk z ≃+* ↥(SemistableModel.localRing X φ z) :=
  RingEquiv.ofBijective (locHom φ z).rangeRestrict
    ⟨fun a b h => locHom_injective φ z (congrArg Subtype.val h), (locHom φ z).rangeRestrict_surjective⟩

@[scoped simp] theorem coe_locEquiv (z : X) (s : X.presheaf.stalk z) :
    ((locEquiv φ z s : ↥(SemistableModel.localRing X φ z)) : F) = locHom φ z s := rfl

theorem isUnit_iff_exists_mul_eq_one (z : X) (s : X.presheaf.stalk z) :
    IsUnit s ↔ ∃ g ∈ SemistableModel.localRing X φ z, locHom φ z s * g = 1 := by
  constructor
  · rintro ⟨u, rfl⟩
    refine ⟨locHom φ z ((u⁻¹ : (X.presheaf.stalk z)ˣ) : X.presheaf.stalk z), locHom_mem φ z _, ?_⟩
    rw [← map_mul, Units.mul_inv, map_one]
  · rintro ⟨g, ⟨t, rfl⟩, h⟩
    change locHom φ z s * locHom φ z t = 1 at h
    rw [← map_mul] at h
    have h1 : s * t = 1 := locHom_injective φ z (by rw [h, map_one])
    exact IsUnit.of_mul_eq_one t h1

theorem locHom_stalkSpecializes {z₁ z₂ : X} (h : z₁ ⤳ z₂) (s : X.presheaf.stalk z₂) :
    locHom φ z₁ ((X.presheaf.stalkSpecializes h).hom s) = locHom φ z₂ s := by
  simp only [locHom_apply, RingHom.algebraMap_toAlgebra]
  congr 1
  change (X.presheaf.stalkSpecializes h ≫ X.presheaf.stalkSpecializes _).hom s = _
  rw [TopCat.Presheaf.stalkSpecializes_comp]

theorem localRing_le_of_specializes {z₁ z₂ : X} (h : z₁ ⤳ z₂) :
    SemistableModel.localRing X φ z₂ ≤ SemistableModel.localRing X φ z₁ := by
  rintro f ⟨s, rfl⟩
  exact ⟨(X.presheaf.stalkSpecializes h).hom s, locHom_stalkSpecializes φ h s⟩

noncomputable def VK (V : ValuationSubring F) : ValuationSubring X.functionField :=
  V.comap (φ.symm : X.functionField ≃+* F).toRingHom

theorem mem_VK_iff (V : ValuationSubring F) (k : X.functionField) : k ∈ VK φ V ↔ φ.symm k ∈ V := Iff.rfl

theorem algebraMap_mem_VK_iff (V : ValuationSubring F) (z : X) (s : X.presheaf.stalk z) :
    algebraMap (X.presheaf.stalk z) X.functionField s ∈ VK φ V ↔ locHom φ z s ∈ V := Iff.rfl

theorem mem_VK_nonunits_iff (V : ValuationSubring F) (k : X.functionField) :
    k ∈ (VK φ V).nonunits ↔ φ.symm k ∈ V.nonunits := by
  rw [ValuationSubring.mem_nonunits_iff_or, ValuationSubring.mem_nonunits_iff_or, mem_VK_iff, map_inv₀,
    map_eq_zero_iff _ φ.symm.injective]

theorem forall_mem_VK_iff (V : ValuationSubring F) (z : X) :
    (∀ s : X.presheaf.stalk z, algebraMap (X.presheaf.stalk z) X.functionField s ∈ VK φ V) ↔
      SemistableModel.localRing X φ z ≤ V.toSubring := by
  constructor
  · rintro h f ⟨s, rfl⟩; exact h s
  · intro h s; exact h (locHom_mem φ z s)

theorem mem_nonunits_iff_not_isUnit (V : ValuationSubring F) {f : F} (hf : f ∈ V) :
    f ∈ V.nonunits ↔ ¬ IsUnit (⟨f, hf⟩ : ↥V) := by
  have := (ValuationSubring.coe_mem_nonunits_iff (A := V) (a := ⟨f, hf⟩))
  exact this

end Transport
p2m_reactivate "P2MW.S_AlgebraicCurve_existsUnique_point_localRing_eq_and_specializes_closedPoint_and_forall_eq_of_isProper_of_isIntegrallyClosed.M3aGlue"

end M3aGlue
p2m_reactivate "P2MW.S_AlgebraicCurve_existsUnique_point_localRing_eq_and_specializes_closedPoint_and_forall_eq_of_isProper_of_isIntegrallyClosed.M3aGlue"

namespace M3aGlue

theorem eq_bot_or_eq_maximalIdeal {L : Type} [Field L] (A : ValuationSubring L)
    (hrk : ∀ a b : ↥A, a ∈ maximalIdeal ↥A → b ≠ 0 → ∃ n : ℕ, b ∣ a ^ n)
    (𝔭 : Ideal ↥A) [𝔭.IsPrime] : 𝔭 = ⊥ ∨ 𝔭 = maximalIdeal ↥A := by
  classical
  by_cases h : 𝔭 = ⊥
  · exact Or.inl h
  · right
    obtain ⟨b, hb𝔭, hb0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot h
    refine le_antisymm (IsLocalRing.le_maximalIdeal (Ideal.IsPrime.ne_top ‹_›)) ?_
    intro a ha
    obtain ⟨n, c, hc⟩ := hrk a b ha hb0
    have : a ^ n ∈ 𝔭 := by rw [hc]; exact Ideal.mul_mem_right _ _ hb𝔭
    exact Ideal.IsPrime.mem_of_pow_mem ‹_› n this

theorem eq_top_or_eq_of_le {L : Type} [Field L] (A : ValuationSubring L)
    (hrk : ∀ a b : ↥A, a ∈ maximalIdeal ↥A → b ≠ 0 → ∃ n : ℕ, b ∣ a ^ n)
    (W : ValuationSubring L) (hW : A ≤ W) : W = ⊤ ∨ W = A := by
  classical
  by_cases h : W = A
  · exact Or.inr h
  · left
    have hnle : ¬ (W ≤ A) := fun hle => h (le_antisymm hle hW)
    obtain ⟨w, hwW, hwA⟩ := Set.not_subset.mp hnle
    have hw0 : w ≠ 0 := fun h0 => hwA (h0 ▸ A.zero_mem)
    have hwinv : w⁻¹ ∈ A := (A.mem_or_inv_mem w).resolve_left hwA

    have hwinv𝔪 : (⟨w⁻¹, hwinv⟩ : ↥A) ∈ maximalIdeal ↥A := by
      rw [ValuationSubring.valuation_lt_one_iff]
      have h1 : ¬ A.valuation w ≤ 1 := fun hle => hwA ((A.valuation_le_one_iff w).mp hle)
      show A.valuation w⁻¹ < 1
      rw [map_inv₀, inv_lt_one₀ (lt_of_le_of_ne zero_le' ((map_ne_zero A.valuation).mpr hw0).symm)]
      exact lt_of_not_ge h1

    refine eq_top_iff.mpr fun l _ => ?_
    by_cases hlA : l ∈ A
    · exact hW hlA
    · have hl0 : l ≠ 0 := fun h0 => hlA (h0 ▸ A.zero_mem)
      have hlinv : l⁻¹ ∈ A := (A.mem_or_inv_mem l).resolve_left hlA
      have hlinv0 : (⟨l⁻¹, hlinv⟩ : ↥A) ≠ 0 := fun h0 => by
        apply inv_ne_zero hl0; exact congrArg Subtype.val h0
      obtain ⟨n, c, hc⟩ := hrk ⟨w⁻¹, hwinv⟩ ⟨l⁻¹, hlinv⟩ hwinv𝔪 hlinv0

      have hcL : (w⁻¹) ^ n = l⁻¹ * (c : L) := by
        have := congrArg (fun z : ↥A => (z : L)) hc
        simpa using this
      have hl : l = (c : L) * w ^ n := by
        have hwn : w ^ n ≠ 0 := pow_ne_zero _ hw0
        have h1 : l * (w⁻¹) ^ n = (c : L) := by rw [hcL, ← mul_assoc, mul_inv_cancel₀ hl0, one_mul]
        calc l = l * (w⁻¹) ^ n * w ^ n := by rw [inv_pow, mul_assoc, inv_mul_cancel₀ hwn, mul_one]
          _ = (c : L) * w ^ n := by rw [h1]
      rw [hl]
      exact mul_mem (hW c.2) (pow_mem hwW n)

theorem algebraMap_germ_appTop {R : Type} [CommRing R] {X : Scheme.{0}} [IsIntegral X]
    (f : X ⟶ Spec (CommRingCat.of R)) (y : X) (a : R) :
    algebraMap (X.presheaf.stalk y) X.functionField
      ((X.presheaf.germ ⊤ y trivial).hom (f.appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of R)).inv a))) =
    SemistableModel.baseToFunctionField f a := by
  unfold SemistableModel.baseToFunctionField
  rw [RingHom.comp_apply, RingHom.comp_apply, RingHom.algebraMap_toAlgebra, ← CommRingCat.comp_apply,
    TopCat.Presheaf.germ_stalkSpecializes]

theorem isUnit_germ_appTop_iff {R : Type} [CommRing R] {X : Scheme.{0}}
    (f : X ⟶ Spec (CommRingCat.of R)) (y : X) (a : R) :
    IsUnit ((X.presheaf.germ ⊤ y trivial).hom (f.appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of R)).inv a))) ↔
      a ∉ (f.base y).asIdeal := by

  have h1 : (X.presheaf.germ ⊤ y trivial).hom (f.appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of R)).inv a)) =
      (f.stalkMap y).hom (((Spec (CommRingCat.of R)).presheaf.germ ⊤ (f.base y) trivial).hom
        ((Scheme.ΓSpecIso (CommRingCat.of R)).inv a)) := by
    have h := Scheme.Hom.germ_stalkMap f ⊤ y trivial
    have h' := congrArg (fun g => g.hom ((Scheme.ΓSpecIso (CommRingCat.of R)).inv a)) h
    simp only [CommRingCat.hom_comp, RingHom.comp_apply] at h'
    exact h'.symm
  have h2 : ((Spec (CommRingCat.of R)).presheaf.germ ⊤ (f.base y) trivial).hom
      ((Scheme.ΓSpecIso (CommRingCat.of R)).inv a) = (StructureSheaf.toStalk R (f.base y)).hom a := by
    have h := congrArg (fun g => g.hom a) (StructureSheaf.algebraMap_germ (R := R) ⊤ (f.base y) trivial)
    simp only [CommRingCat.hom_comp, RingHom.comp_apply] at h
    rw [Scheme.ΓSpecIso_inv]
    exact h
  rw [h1, h2]

  have hloc : IsLocalHom (f.stalkMap y).hom :=
    Scheme.Hom.instIsLocalHomCarrierStalkCommRingCatPresheafCoeContinuousMapCarrierCarrierHomTopCatBaseRingHomHomStalkMap f y
  have h3 : IsUnit ((f.stalkMap y).hom ((StructureSheaf.toStalk R (f.base y)).hom a)) ↔
      IsUnit ((StructureSheaf.toStalk R (f.base y)).hom a) :=
    ⟨fun hu => hloc.map_nonunit _ hu, fun hu => hu.map _⟩
  rw [h3, ← StructureSheaf.stalkAlgebra_map]

  have h4 : algebraMap R ((Spec.structureSheaf R).presheaf.stalk (f.base y)) a =
      StructureSheaf.stalkIso R (f.base y) (algebraMap R (Localization.AtPrime (f.base y).asIdeal) a) :=
    ((StructureSheaf.stalkIso R (f.base y)).commutes a).symm
  rw [h4]
  have h5 : IsUnit (StructureSheaf.stalkIso R (f.base y) (algebraMap R (Localization.AtPrime (f.base y).asIdeal) a)) ↔
      IsUnit (algebraMap R (Localization.AtPrime (f.base y).asIdeal) a) :=
    ⟨fun hu => by simpa using hu.map (StructureSheaf.stalkIso R (f.base y)).symm, fun hu => hu.map _⟩
  rw [h5, IsLocalization.AtPrime.isUnit_to_map_iff (Localization.AtPrime (f.base y).asIdeal) (f.base y).asIdeal]
  rfl

theorem isNoetherianRing_stalk_of_asIdeal_eq_bot {L : Type} [Field L] (A : ValuationSubring L)
    (hrk : ∀ a b : ↥A, a ∈ maximalIdeal ↥A → b ≠ 0 → ∃ n : ℕ, b ∣ a ^ n)
    (hA : (A : Set L) ≠ Set.univ)
    (X : Scheme.{0}) (toBase : X ⟶ Spec (CommRingCat.of ↥A)) [LocallyOfFiniteType toBase]
    (y : X) (hy : (toBase.base y).asIdeal = ⊥) :
    IsNoetherianRing (X.presheaf.stalk y) := by
  classical

  obtain ⟨l, hlA⟩ : ∃ l : L, l ∉ A := by
    by_contra h; push Not at h
    exact hA (Set.eq_univ_of_forall fun l => h l)
  have hl0 : l ≠ 0 := fun h0 => hlA (h0 ▸ A.zero_mem)
  have hlinv : l⁻¹ ∈ A := (A.mem_or_inv_mem l).resolve_left hlA
  set a : ↥A := ⟨l⁻¹, hlinv⟩ with hadef
  have ha0 : a ≠ 0 := fun h0 => inv_ne_zero hl0 (congrArg Subtype.val h0)
  have ha𝔪 : a ∈ maximalIdeal ↥A := by
    rw [ValuationSubring.valuation_lt_one_iff]
    have h1 : ¬ A.valuation l ≤ 1 := fun hle => hlA ((A.valuation_le_one_iff l).mp hle)
    show A.valuation l⁻¹ < 1
    rw [map_inv₀, inv_lt_one₀ (lt_of_le_of_ne zero_le' ((map_ne_zero A.valuation).mpr hl0).symm)]
    exact lt_of_not_ge h1

  set a' : Γ(Spec (CommRingCat.of ↥A), ⊤) := (Scheme.ΓSpecIso (CommRingCat.of ↥A)).inv a with ha'
  set U : (Spec (CommRingCat.of ↥A)).Opens := (Spec (CommRingCat.of ↥A)).basicOpen a' with hU
  have hUaff : IsAffineOpen U := (isAffineOpen_top (Spec (CommRingCat.of ↥A))).basicOpen a'
  have hyU : toBase.base y ∈ U := by
    rw [hU, ha', basicOpen_eq_of_affine]
    show a ∉ (toBase.base y).asIdeal
    rw [hy]; exact ha0

  haveI hloc : IsLocalization.Away a' ↑Γ(Spec (CommRingCat.of ↥A), U) := (isAffineOpen_top (Spec (CommRingCat.of ↥A))).isLocalization_basicOpen a'

  let e : ↥A ≃+* ↑Γ(Spec (CommRingCat.of ↥A), ⊤) := (Scheme.ΓSpecIso (CommRingCat.of ↥A)).symm.commRingCatIsoToRingEquiv
  have he : ∀ b : ↥A, e b = (Scheme.ΓSpecIso (CommRingCat.of ↥A)).inv b := fun b => rfl
  have hfield : IsField ↑Γ(Spec (CommRingCat.of ↥A), U) := by
    refine ⟨⟨0, 1, ?_⟩, mul_comm, fun {z} hz => ?_⟩
    · intro h01

      have : (algebraMap ↑Γ(Spec (CommRingCat.of ↥A), ⊤) ↑Γ(Spec (CommRingCat.of ↥A), U)) (e a) ≠ 0 := by
        intro h0
        rw [IsLocalization.map_eq_zero_iff (Submonoid.powers a')] at h0
        obtain ⟨⟨m, hm⟩, hm0⟩ := h0
        obtain ⟨k, rfl⟩ := (Submonoid.mem_powers_iff _ _).mp hm
        have : e (a ^ k * a) = 0 := by rw [map_mul, map_pow, he a]; exact hm0
        exact (mul_ne_zero (pow_ne_zero _ ha0) ha0) (e.injective (by rw [this, map_zero]))
      exact this (by rw [← mul_one ((algebraMap _ _) (e a)), ← h01, mul_zero])
    ·
      obtain ⟨⟨x, s⟩, rfl⟩ := IsLocalization.mk'_surjective (Submonoid.powers a') z
      obtain ⟨x₀, rfl⟩ : ∃ x₀ : ↥A, e x₀ = x := ⟨e.symm x, e.apply_symm_apply x⟩
      have hx₀ : x₀ ≠ 0 := by
        intro h0; apply hz
        show IsLocalization.mk' _ (e x₀) s = 0
        rw [h0, map_zero, IsLocalization.mk'_zero]
      have hunit : IsUnit (algebraMap ↑Γ(Spec (CommRingCat.of ↥A), ⊤) ↑Γ(Spec (CommRingCat.of ↥A), U) (e x₀)) := by
        by_cases hu : IsUnit x₀
        · exact (hu.map e).map _
        · obtain ⟨n, c, hc⟩ := hrk a x₀ ha𝔪 hx₀

          have hau : IsUnit (algebraMap ↑Γ(Spec (CommRingCat.of ↥A), ⊤) ↑Γ(Spec (CommRingCat.of ↥A), U) (e a)) := by
            rw [he]; exact IsLocalization.Away.algebraMap_isUnit a'
          have : IsUnit (algebraMap ↑Γ(Spec (CommRingCat.of ↥A), ⊤) ↑Γ(Spec (CommRingCat.of ↥A), U) (e x₀) *
              algebraMap ↑Γ(Spec (CommRingCat.of ↥A), ⊤) ↑Γ(Spec (CommRingCat.of ↥A), U) (e c)) := by
            rw [← map_mul, ← map_mul, ← hc, map_pow, map_pow]; exact hau.pow n
          exact isUnit_of_mul_isUnit_left this
      obtain ⟨w, hw⟩ := hunit.exists_right_inv
      refine ⟨w * algebraMap _ _ (s : ↑Γ(Spec (CommRingCat.of ↥A), ⊤)), ?_⟩
      show IsLocalization.mk' _ (e x₀) s * (w * _) = 1
      rw [mul_comm w, ← mul_assoc, IsLocalization.mk'_spec, hw]
  letI : Field ↑Γ(Spec (CommRingCat.of ↥A), U) := hfield.toField
  haveI : IsNoetherianRing ↑Γ(Spec (CommRingCat.of ↥A), U) := inferInstance
  haveI : IsLocallyNoetherian (Spec Γ(Spec (CommRingCat.of ↥A), U)) := inferInstance
  haveI : IsLocallyNoetherian ↑U := isLocallyNoetherian_of_isOpenImmersion hUaff.isoSpec.hom

  set V : X.Opens := toBase ⁻¹ᵁ U with hV
  haveI : IsLocallyNoetherian ↑V := LocallyOfFiniteType.isLocallyNoetherian (toBase ∣_ U)
  have hyV : y ∈ V := hyU
  haveI : IsNoetherianRing (((↑V : Scheme).presheaf).stalk (⟨y, hyV⟩ : ↑V)) := inferInstance

  haveI : IsIso (V.ι.stalkMap ⟨y, hyV⟩) := inferInstance
  let ε := (asIso (V.ι.stalkMap ⟨y, hyV⟩)).commRingCatIsoToRingEquiv
  exact isNoetherianRing_of_ringEquiv _ ε.symm

end M3aGlue
p2m_reactivate "P2MW.S_AlgebraicCurve_existsUnique_point_localRing_eq_and_specializes_closedPoint_and_forall_eq_of_isProper_of_isIntegrallyClosed.M3aGlue"

namespace M3aGlue

section Centre

variable {F : Type} [Field F] {X : Scheme.{0}} [IsIntegral X] {φ : F ≃+* X.functionField}

def IsCentre (φ : F ≃+* X.functionField) (V : ValuationSubring F) (z : X) : Prop :=
  SemistableModel.localRing X φ z ≤ V.toSubring ∧
    ∀ s ∈ maximalIdeal (X.presheaf.stalk z), locHom φ z s ∈ V.nonunits

theorem IsCentre.sub {V : ValuationSubring F} {z : X} (h : IsCentre φ V z) :
    ∀ s : X.presheaf.stalk z, algebraMap (X.presheaf.stalk z) X.functionField s ∈ VK φ V :=
  (forall_mem_VK_iff φ V z).2 h.1

theorem IsCentre.dom {V : ValuationSubring F} {z : X} (h : IsCentre φ V z) :
    ∀ s ∈ maximalIdeal (X.presheaf.stalk z), algebraMap (X.presheaf.stalk z) X.functionField s ∈ (VK φ V).nonunits :=
  fun s hs => (mem_VK_nonunits_iff φ V _).2 (h.2 s hs)

theorem isCentre_of_VK (φ : F ≃+* X.functionField) {V : ValuationSubring F} {z : X}
    (hsub : ∀ s : X.presheaf.stalk z, algebraMap (X.presheaf.stalk z) X.functionField s ∈ VK φ V)
    (hdom : ∀ s ∈ maximalIdeal (X.presheaf.stalk z),
      algebraMap (X.presheaf.stalk z) X.functionField s ∈ (VK φ V).nonunits) : IsCentre φ V z :=
  ⟨(forall_mem_VK_iff φ V z).1 hsub, fun s hs => (mem_VK_nonunits_iff φ V _).1 (hdom s hs)⟩

theorem IsCentre.mem {V : ValuationSubring F} {z : X} (h : IsCentre φ V z) (s : X.presheaf.stalk z) :
    locHom φ z s ∈ V := h.1 (locHom_mem φ z s)

theorem IsCentre.isUnit_iff {V : ValuationSubring F} {z : X} (h : IsCentre φ V z) (s : X.presheaf.stalk z) :
    IsUnit s ↔ IsUnit (⟨locHom φ z s, h.mem s⟩ : ↥V) := by
  constructor
  · intro hu
    let ρ : X.presheaf.stalk z →+* ↥V := (locHom φ z).codRestrict V.toSubring h.mem
    exact hu.map ρ
  · intro hu
    by_contra hs
    have := h.2 s hs
    rw [mem_nonunits_iff_not_isUnit V (h.mem s)] at this
    exact this hu

theorem isCentre_of_localRing_eq {V : ValuationSubring F} {z : X}
    (h : SemistableModel.localRing X φ z = V.toSubring) : IsCentre φ V z := by
  refine ⟨le_of_eq h, fun s hs => ?_⟩
  rw [ValuationSubring.mem_nonunits_iff_or]
  by_cases h0 : locHom φ z s = 0
  · exact Or.inl h0
  · right
    intro hinv
    apply hs
    rw [isUnit_iff_exists_mul_eq_one φ z s]
    refine ⟨(locHom φ z s)⁻¹, ?_, mul_inv_cancel₀ h0⟩
    rw [h]; exact hinv

theorem IsCentre.eq {V : ValuationSubring F} {z₁ z₂ : X} (h₁ : IsCentre φ V z₁)
    {O : Type} [CommRing O] (f : X ⟶ Spec (CommRingCat.of O)) [IsSeparated f]
    (h₂ : IsCentre φ V z₂) : z₁ = z₂ :=
  AlgebraicGeometry.Scheme.eq_of_forall_mem_valuationSubring_of_isSeparated f (VK φ V) z₁ z₂
    h₁.sub h₁.dom h₂.sub h₂.dom

end Centre
p2m_reactivate "P2MW.S_AlgebraicCurve_existsUnique_point_localRing_eq_and_specializes_closedPoint_and_forall_eq_of_isProper_of_isIntegrallyClosed.M3aGlue"

section EvalClause

variable {L F : Type} [Field L] [IsAlgClosed L] [Field F] [Algebra L F] [IsCurveOver L F]
variable {X : Scheme.{0}} [IsIntegral X] (φ : F ≃+* X.functionField) (A : ValuationSubring L) (P : Place L F)

theorem eval_clause_of_isCentre {z : X} (h : IsCentre φ (VP A P) z) :
    ∀ f : F, f ∈ SemistableModel.localRing X φ z →
      f ∈ P.toValuationSubring ∧ ∃ hA : P.evalAt f ∈ A,
        (IsUnit (⟨P.evalAt f, hA⟩ : ↥A) ↔ ∃ g ∈ SemistableModel.localRing X φ z, f * g = 1) := by
  intro f hf
  obtain ⟨s, hs⟩ := hf
  change locHom φ z s = f at hs
  subst hs
  have hV : locHom φ z s ∈ VP A P := h.mem s
  refine ⟨mem_of_mem_VP hV, evalAt_mem_of_mem_VP hV, ?_⟩
  rw [← isUnit_VP_iff A P _ hV, ← h.isUnit_iff, isUnit_iff_exists_mul_eq_one φ z s]

theorem isCentre_of_eval_clause {z : X}
    (h : ∀ f : F, f ∈ SemistableModel.localRing X φ z →
      f ∈ P.toValuationSubring ∧ ∃ hA : P.evalAt f ∈ A,
        (IsUnit (⟨P.evalAt f, hA⟩ : ↥A) ↔ ∃ g ∈ SemistableModel.localRing X φ z, f * g = 1)) :
    IsCentre φ (VP A P) z := by
  have hmem : ∀ s : X.presheaf.stalk z, locHom φ z s ∈ VP A P := fun s => by
    obtain ⟨hf, hA, -⟩ := h _ (locHom_mem φ z s)
    exact ⟨hf, by rw [← evalAt_eq_evalHom P hf]; exact hA⟩
  refine ⟨fun f ⟨s, hs⟩ => hs ▸ hmem s, fun s hs => ?_⟩
  rw [mem_nonunits_iff_not_isUnit _ (hmem s), isUnit_VP_iff A P _ (hmem s)]
  obtain ⟨hf, hA, hiff⟩ := h _ (locHom_mem φ z s)
  intro hu
  have := (isUnit_iff_exists_mul_eq_one φ z s).2 (hiff.1 hu)
  exact hs this

end EvalClause
p2m_reactivate "P2MW.S_AlgebraicCurve_existsUnique_point_localRing_eq_and_specializes_closedPoint_and_forall_eq_of_isProper_of_isIntegrallyClosed.M3aGlue"

end M3aGlue
p2m_reactivate "P2MW.S_AlgebraicCurve_existsUnique_point_localRing_eq_and_specializes_closedPoint_and_forall_eq_of_isProper_of_isIntegrallyClosed.M3aGlue"

section Main

open M3aGlue

theorem solution
    {L : Type} [Field L] [IsAlgClosed L] (A : ValuationSubring L)
    (hrk : ∀ a b : ↥A, a ∈ maximalIdeal ↥A → b ≠ 0 → ∃ n : ℕ, b ∣ a ^ n)
    (hA : (A : Set L) ≠ Set.univ)
    {F : Type} [Field F] [Algebra L F] [IsCurveOver L F] [Algebra.EssFiniteType L F]
    (X : Scheme.{0}) (toBase : X ⟶ Spec (CommRingCat.of ↥A))
    [IsIntegral X] [IsProper toBase]
    (hn : ∀ y : X, IsIntegrallyClosed (X.presheaf.stalk y))
    (φ : F ≃+* X.functionField)
    (hφ : ∀ a : ↥A, φ (algebraMap L F (a : L)) = SemistableModel.baseToFunctionField toBase a)
    (P : Place L F) :
    ∃ pt : X,
      SemistableModel.localRing X φ pt = P.toValuationSubring.toSubring ∧
      (∀ pt' : X, SemistableModel.localRing X φ pt' = P.toValuationSubring.toSubring → pt' = pt) ∧
      (toBase.base pt).asIdeal = ⊥ ∧
      ∃ x : X, pt ⤳ x ∧ x ≠ pt ∧ toBase.base x = closedPoint ↥A ∧ (∀ y : X, x ⤳ y → y = x) ∧
        (∀ y : X, pt ⤳ y → y = pt ∨ y = x) ∧
        (∀ f : F, f ∈ SemistableModel.localRing X φ x →
          f ∈ P.toValuationSubring ∧ ∃ h : P.evalAt f ∈ A,
            (IsUnit (⟨P.evalAt f, h⟩ : ↥A) ↔ ∃ g ∈ SemistableModel.localRing X φ x, f * g = 1)) ∧
        (∀ x' : X, toBase.base x' = closedPoint ↥A → (∀ y : X, x' ⤳ y → y = x') →
          (∀ f : F, f ∈ SemistableModel.localRing X φ x' →
            f ∈ P.toValuationSubring ∧ ∃ h : P.evalAt f ∈ A,
              (IsUnit (⟨P.evalAt f, h⟩ : ↥A) ↔ ∃ g ∈ SemistableModel.localRing X φ x', f * g = 1)) → x' = x) ∧
        (∀ y : X, (toBase.base y).asIdeal = ⊥ → y ≠ genericPoint X →
          ∃ P' : Place L F, SemistableModel.localRing X φ y = P'.toValuationSubring.toSubring) := by
  classical

  have hφ' : ∀ a : ↥A, φ.symm (SemistableModel.baseToFunctionField toBase a) = algebraMap L F (a : L) := fun a => by
    rw [← hφ, RingEquiv.symm_apply_apply]

  let cst : ∀ z : X, ↥A → X.presheaf.stalk z := fun z a =>
    (X.presheaf.germ ⊤ z trivial).hom (toBase.appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of ↥A)).inv a))
  have hcst : ∀ (z : X) (a : ↥A), locHom φ z (cst z a) = algebraMap L F (a : L) := fun z a => by
    rw [locHom_apply]
    change φ.symm (algebraMap _ _ ((X.presheaf.germ ⊤ z trivial).hom _)) = _
    rw [algebraMap_germ_appTop toBase z a, hφ']
  have hcstU : ∀ (z : X) (a : ↥A), IsUnit (cst z a) ↔ a ∉ (toBase.base z).asIdeal := fun z a =>
    isUnit_germ_appTop_iff toBase z a
  have h𝔪 : ∃ ϖ : ↥A, ϖ ∈ maximalIdeal ↥A ∧ ϖ ≠ 0 := by
    by_contra hcon
    push Not at hcon
    apply hA
    refine Set.eq_univ_of_forall fun l => ?_
    rcases A.mem_or_inv_mem l with hl | hl
    · exact hl
    · by_cases hl0 : l = 0
      · rw [hl0]; exact A.zero_mem
      · have hu : IsUnit (⟨l⁻¹, hl⟩ : ↥A) := by
          by_contra hnu
          exact (inv_ne_zero hl0) (congrArg Subtype.val (hcon ⟨l⁻¹, hl⟩ hnu))
        have := (isUnit_iff_inv_mem A hl (inv_ne_zero hl0)).1 hu
        rwa [inv_inv] at this

  have hOV : ∀ a : ↥A, (X.presheaf.germ ⊤ (genericPoint X) trivial).hom
      (toBase.appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of ↥A)).inv a)) ∈ VK φ (VP A P) := fun a => by
    change SemistableModel.baseToFunctionField toBase a ∈ VK φ (VP A P)
    rw [mem_VK_iff, hφ']; exact algebraMap_mem_VP A P a
  have hmV : ∀ a ∈ IsLocalRing.maximalIdeal ↥A, (X.presheaf.germ ⊤ (genericPoint X) trivial).hom
      (toBase.appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of ↥A)).inv a)) ∈ (VK φ (VP A P)).nonunits := fun a ha => by
    change SemistableModel.baseToFunctionField toBase a ∈ (VK φ (VP A P)).nonunits
    rw [mem_VK_nonunits_iff, hφ', mem_nonunits_iff_not_isUnit _ (algebraMap_mem_VP A P a), isUnit_VP_iff]
    have hev : P.evalAt (algebraMap L F (a : L)) = a := by
      rw [evalAt_eq_evalHom P (P.algebraMap_mem' _), evalHom_algebraMap]
    have : (⟨P.evalAt (algebraMap L F (a : L)), evalAt_mem_of_mem_VP (algebraMap_mem_VP A P a)⟩ : ↥A) = a :=
      Subtype.ext hev
    rw [this]; exact ha
  obtain ⟨x, hxbase, hxsub, hxdom⟩ :=
    AlgebraicGeometry.Scheme.exists_eq_closedPoint_and_forall_mem_of_valuationSubring toBase (VK φ (VP A P)) hOV hmV
  have hxle : SemistableModel.localRing X φ x ≤ (VP A P).toSubring := (forall_mem_VK_iff φ _ x).1 hxsub
  have hxdom' : ∀ s ∈ maximalIdeal (X.presheaf.stalk x), locHom φ x s ∈ (VP A P).nonunits := fun s hs =>
    (mem_VK_nonunits_iff φ _ _).1 (hxdom s hs)
  have hxC : IsCentre φ (VP A P) x := ⟨hxle, hxdom'⟩

  have hx_eval : ∀ f : F, f ∈ SemistableModel.localRing X φ x →
      f ∈ P.toValuationSubring ∧ ∃ h : P.evalAt f ∈ A,
        (IsUnit (⟨P.evalAt f, h⟩ : ↥A) ↔ ∃ g ∈ SemistableModel.localRing X φ x, f * g = 1) :=
    eval_clause_of_isCentre φ A P hxC

  have hxOP : ∀ s : X.presheaf.stalk x, locHom φ x s ∈ P.toValuationSubring := fun s =>
    mem_of_mem_VP (hxle (locHom_mem φ x s))
  let ρx : X.presheaf.stalk x →+* ↥P.toValuationSubring :=
    (locHom φ x).codRestrict P.toValuationSubring.toSubring hxOP
  let 𝔮 : Ideal (X.presheaf.stalk x) := Ideal.comap ρx (maximalIdeal ↥P.toValuationSubring)
  haveI h𝔮 : 𝔮.IsPrime := Ideal.comap_isPrime ρx _
  obtain ⟨pt, hptx, hloc⟩ := AlgebraicGeometry.Scheme.exists_specializes_isLocalization_atPrime_stalk x 𝔮
  letI instAlg : Algebra (X.presheaf.stalk x) (X.presheaf.stalk pt) := (X.presheaf.stalkSpecializes hptx).hom.toAlgebra
  have hloc' : IsLocalization.AtPrime (X.presheaf.stalk pt) 𝔮 := hloc
  have halg : ∀ a : X.presheaf.stalk x, locHom φ pt (algebraMap _ (X.presheaf.stalk pt) a) = locHom φ x a :=
    fun a => locHom_stalkSpecializes φ hptx a
  have hρx : ∀ a : X.presheaf.stalk x, ((ρx a : ↥P.toValuationSubring) : F) = locHom φ x a := fun a => rfl
  have hmem𝔮 : ∀ a : X.presheaf.stalk x, a ∈ 𝔮 ↔ ρx a ∈ maximalIdeal ↥P.toValuationSubring := fun a => Iff.rfl
  have hbU : ∀ b : 𝔮.primeCompl, IsUnit (ρx b) := fun b => by
    by_contra hnu
    exact b.2 ((hmem𝔮 b).2 hnu)
  have hpt_key : ∀ s' : X.presheaf.stalk pt, ∃ t : ↥P.toValuationSubring, (t : F) = locHom φ pt s' ∧
      (s' ∈ maximalIdeal (X.presheaf.stalk pt) ↔ t ∈ maximalIdeal ↥P.toValuationSubring) := by
    intro s'
    obtain ⟨a, b, rfl⟩ := IsLocalization.exists_mk'_eq 𝔮.primeCompl s'
    obtain ⟨u, hu⟩ := hbU b
    refine ⟨ρx a * ↑u⁻¹, ?_, ?_⟩
    · have hspec := IsLocalization.mk'_spec (X.presheaf.stalk pt) a b
      have h1 := congrArg (locHom φ pt) hspec
      rw [map_mul, halg, halg] at h1

      have hb0 : locHom φ x (b : X.presheaf.stalk x) ≠ 0 := by
        rw [← hρx, ← hu]
        exact fun h => (Units.ne_zero u) (Subtype.ext h)
      have h2 : locHom φ pt (IsLocalization.mk' (X.presheaf.stalk pt) a b) =
          locHom φ x a * (locHom φ x (b : X.presheaf.stalk x))⁻¹ := by
        rw [← h1, mul_inv_cancel_right₀ hb0]
      rw [h2, Subring.coe_mul, hρx]
      congr 1
      have h3 : ((u : ↥P.toValuationSubring) : F) * ((↑u⁻¹ : ↥P.toValuationSubring) : F) = 1 := by
        rw [← Subring.coe_mul]; exact congrArg Subtype.val u.mul_inv
      rw [hu, hρx] at h3
      exact (eq_inv_of_mul_eq_one_right h3)
    · rw [IsLocalization.AtPrime.mk'_mem_maximal_iff (X.presheaf.stalk pt) 𝔮 a b, hmem𝔮]
      constructor
      · intro h; exact Ideal.mul_mem_right _ _ h
      · intro h
        have := Ideal.mul_mem_right (↑u : ↥P.toValuationSubring) _ h
        rwa [mul_assoc, Units.inv_mul, mul_one] at this
  have hpt_le : SemistableModel.localRing X φ pt ≤ P.toValuationSubring.toSubring := by
    rintro f ⟨s', rfl⟩
    obtain ⟨t, ht, -⟩ := hpt_key s'
    change locHom φ pt s' ∈ P.toValuationSubring.toSubring
    rw [← ht]; exact t.2
  have hpt_dom : ∀ s ∈ maximalIdeal (X.presheaf.stalk pt), locHom φ pt s ∈ P.toValuationSubring.nonunits := by
    intro s hs
    obtain ⟨t, ht, hiff⟩ := hpt_key s
    rw [← ht, ValuationSubring.coe_mem_nonunits_iff]
    exact hiff.1 hs
  have hptC : IsCentre φ P.toValuationSubring pt := ⟨hpt_le, hpt_dom⟩

  have hcstOP : ∀ (z : X) (hz : IsCentre φ P.toValuationSubring z) (a : ↥A), a ≠ 0 → IsUnit (cst z a) := by
    intro z hz a ha0
    rw [hz.isUnit_iff]
    have ha0' : algebraMap L F (a : L) ≠ 0 := by
      rw [map_ne_zero_iff _ (algebraMap L F).injective]
      exact fun h => ha0 (Subtype.ext h)
    have : (⟨locHom φ z (cst z a), hz.mem (cst z a)⟩ : ↥P.toValuationSubring) =
        ⟨algebraMap L F (a : L), P.algebraMap_mem' _⟩ := Subtype.ext (hcst z a)
    rw [this, isUnit_iff_inv_mem _ _ ha0', ← map_inv₀]
    exact P.algebraMap_mem' _
  have hgen_of_centre : ∀ (z : X), IsCentre φ P.toValuationSubring z → (toBase.base z).asIdeal = ⊥ := by
    intro z hz
    refine (Submodule.eq_bot_iff _).2 fun a ha => ?_
    by_contra ha0
    exact ((hcstU z a).1 (hcstOP z hz a ha0)) ha
  have hpt_gen : (toBase.base pt).asIdeal = ⊥ := hgen_of_centre pt hptC

  have hLmem : ∀ (z : X), (toBase.base z).asIdeal = ⊥ → ∀ l : L, algebraMap L F l ∈ SemistableModel.localRing X φ z := by
    intro z hz l
    obtain ⟨c, d, hd, rfl⟩ := IsFractionRing.div_surjective (A := ↥A) l
    have hd0 : d ≠ 0 := nonZeroDivisors.ne_zero hd
    have hdU : IsUnit (cst z d) := (hcstU z d).2 (by rw [hz]; exact fun h => hd0 h)
    obtain ⟨u, hu⟩ := hdU
    rw [map_div₀]
    change algebraMap L F (c : L) / algebraMap L F (d : L) ∈ SemistableModel.localRing X φ z
    rw [div_eq_mul_inv]
    refine Subring.mul_mem _ (hcst z c ▸ locHom_mem φ z (cst z c)) ?_
    have : (algebraMap L F (d : L))⁻¹ = locHom φ z ((u⁻¹ : (X.presheaf.stalk z)ˣ) : X.presheaf.stalk z) := by
      rw [← hcst z d, ← hu]
      symm
      apply eq_inv_of_mul_eq_one_right
      rw [← map_mul, Units.mul_inv, map_one]
    rw [this]; exact locHom_mem φ z _

  have hplace : ∀ (z : X), (toBase.base z).asIdeal = ⊥ → SemistableModel.localRing X φ z ≠ ⊤ →
      ∃ P' : Place L F, P'.toValuationSubring.toSubring = SemistableModel.localRing X φ z := by
    intro z hz hne
    haveI : IsNoetherianRing (X.presheaf.stalk z) :=
      isNoetherianRing_stalk_of_asIdeal_eq_bot A hrk hA X toBase z hz
    haveI : IsNoetherianRing ↥(SemistableModel.localRing X φ z) :=
      isNoetherianRing_of_ringEquiv (X.presheaf.stalk z) (locEquiv φ z)
    haveI : IsLocalRing ↥(SemistableModel.localRing X φ z) :=
      IsLocalRing.of_surjective' (locEquiv φ z).toRingHom (locEquiv φ z).surjective
    have halgR : ∀ r : ↥(SemistableModel.localRing X φ z), algebraMap ↥(SemistableModel.localRing X φ z) F r = (r : F) :=
      fun r => rfl
    haveI : IsFractionRing ↥(SemistableModel.localRing X φ z) F := by
      rw [IsFractionRing, isLocalization_iff]
      refine ⟨?_, ?_, ?_⟩
      · intro y
        rw [halgR]
        exact isUnit_iff_ne_zero.2 fun h => nonZeroDivisors.ne_zero y.2 (Subtype.ext h)
      · intro w
        obtain ⟨a, b, hb, hab⟩ := IsFractionRing.div_surjective (A := X.presheaf.stalk z) (φ w)
        have hb0 : b ≠ 0 := nonZeroDivisors.ne_zero hb
        have hb0' : (locEquiv φ z b) ≠ 0 := fun h => hb0 ((locEquiv φ z).injective (by rw [h, map_zero]))
        refine ⟨(locEquiv φ z a, ⟨locEquiv φ z b, mem_nonZeroDivisors_of_ne_zero hb0'⟩), ?_⟩
        change w * (locEquiv φ z b : F) = (locEquiv φ z a : F)
        rw [coe_locEquiv, coe_locEquiv]
        apply φ.injective
        have hKb : algebraMap (X.presheaf.stalk z) X.functionField b ≠ 0 :=
          fun h => hb0 (IsFractionRing.injective (X.presheaf.stalk z) X.functionField (by rw [h, map_zero]))
        rw [map_mul, φ_locHom, φ_locHom, ← hab, div_mul_cancel₀ _ hKb]
      · intro a b h
        exact ⟨1, by rw [halgR, halgR] at h; rw [Subtype.ext h]⟩
    have hic : IsIntegrallyClosedIn ↥(SemistableModel.localRing X φ z) F := by
      have hK : IsIntegrallyClosedIn (X.presheaf.stalk z) X.functionField :=
        (isIntegrallyClosed_iff_isIntegrallyClosedIn X.functionField).1 (hn z)
      rw [isIntegrallyClosedIn_iff] at hK ⊢
      refine ⟨fun a b h => Subtype.ext (by rwa [halgR, halgR] at h), fun {w} hw => ?_⟩
      have hcomp : (φ : F ≃+* X.functionField).toRingHom.comp (algebraMap ↥(SemistableModel.localRing X φ z) F) =
          (algebraMap (X.presheaf.stalk z) X.functionField).comp (locEquiv φ z).symm.toRingHom := by
        ext r
        obtain ⟨s, rfl⟩ := (locEquiv φ z).surjective r
        change φ ((locEquiv φ z s : ↥(SemistableModel.localRing X φ z)) : F) = algebraMap _ _ ((locEquiv φ z).symm (locEquiv φ z s))
        rw [RingEquiv.symm_apply_apply, coe_locEquiv, φ_locHom]
      obtain ⟨p, hp, hpw⟩ := hw
      have hint : IsIntegral (X.presheaf.stalk z) (φ w) := by
        refine ⟨p.map (locEquiv φ z).symm.toRingHom, hp.map _, ?_⟩
        rw [Polynomial.eval₂_map, ← hcomp]
        change Polynomial.eval₂ ((φ : F ≃+* X.functionField).toRingHom.comp _) ((φ : F ≃+* X.functionField).toRingHom w) p = 0
        rw [← Polynomial.hom_eval₂, hpw, map_zero]
      obtain ⟨s, hs⟩ := hK.2 hint
      refine ⟨locEquiv φ z s, ?_⟩
      rw [halgR, coe_locEquiv, locHom_apply, hs, RingEquiv.symm_apply_apply]
    exact AlgebraicCurve.exists_place_toSubring_eq_of_isIntegrallyClosedIn_of_isNoetherianRing
      (SemistableModel.localRing X φ z) hic (hLmem z hz) hne
  have hpt_eq : SemistableModel.localRing X φ pt = P.toValuationSubring.toSubring := by
    have hne : SemistableModel.localRing X φ pt ≠ ⊤ := by
      intro h
      apply P.ne_top'
      ext f
      refine ⟨fun _ => ValuationSubring.mem_top f, fun _ => ?_⟩
      have hf : f ∈ SemistableModel.localRing X φ pt := by rw [h]; exact Subring.mem_top f
      exact hpt_le hf
    obtain ⟨P₀, hP₀⟩ := hplace pt hpt_gen hne
    apply le_antisymm hpt_le
    intro f hf
    by_contra hfR
    have hf0 : f ≠ 0 := by rintro rfl; exact hfR (Subring.zero_mem _)

    have hfi : f⁻¹ ∈ SemistableModel.localRing X φ pt := by
      rw [← hP₀]; exact (P₀.toValuationSubring.mem_or_inv_mem f).resolve_left (hP₀.symm ▸ hfR :)
    obtain ⟨s, hs⟩ := hfi
    change locHom φ pt s = f⁻¹ at hs
    have hsm : s ∈ maximalIdeal (X.presheaf.stalk pt) := by
      intro hsu
      apply hfR
      obtain ⟨u, rfl⟩ := hsu
      have : f = locHom φ pt ((u⁻¹ : (X.presheaf.stalk pt)ˣ) : X.presheaf.stalk pt) := by
        have h1 : locHom φ pt (u : X.presheaf.stalk pt) * locHom φ pt ((u⁻¹ : (X.presheaf.stalk pt)ˣ) : X.presheaf.stalk pt) = 1 := by
          rw [← map_mul, Units.mul_inv, map_one]
        rw [eq_inv_of_mul_eq_one_right h1, hs, inv_inv]
      rw [this]; exact locHom_mem φ pt _
    have := hpt_dom s hsm
    rw [hs, ValuationSubring.inv_mem_nonunits_iff] at this
    rcases this with h | h
    · exact hf0 h
    · exact h hf

  have hpt_uniq : ∀ pt' : X, SemistableModel.localRing X φ pt' = P.toValuationSubring.toSubring → pt' = pt :=
    fun pt' h => (isCentre_of_localRing_eq h).eq toBase hptC

  have hx_ne : x ≠ pt := by
    intro h
    obtain ⟨ϖ, hϖ, hϖ0⟩ := h𝔪
    have : (toBase.base x).asIdeal = maximalIdeal ↥A := by rw [hxbase]; rfl
    rw [h, hpt_gen] at this
    exact hϖ0 ((Submodule.eq_bot_iff _).1 this.symm ϖ hϖ)

  have hVPcentre : ∀ z : X, SemistableModel.localRing X φ z ≤ (VP A P).toSubring → IsCentre φ (VP A P) z := by
    intro z hz
    have hmem : ∀ s, locHom φ z s ∈ VP A P := fun s => hz (locHom_mem φ z s)
    let ρ : X.presheaf.stalk z →+* ↥(VP A P) := (locHom φ z).codRestrict (VP A P).toSubring hmem
    let g : X.presheaf.stalk z →+* ResidueField ↥A := (IsLocalRing.residue ↥A).comp ((evVP A P).comp ρ)
    have hρcst : ∀ a : ↥A, evVP A P (ρ (cst z a)) = a := fun a => by
      apply Subtype.ext
      rw [coe_evVP]
      have : (⟨((ρ (cst z a) : ↥(VP A P)) : F), (ρ (cst z a)).2.1⟩ : ↥P.toValuationSubring) =
          ⟨algebraMap L F (a : L), P.algebraMap_mem' _⟩ := Subtype.ext (hcst z a)
      rw [this, evalHom_algebraMap]
    have hg_surj : Function.Surjective g := fun k => by
      obtain ⟨a, rfl⟩ := IsLocalRing.residue_surjective k
      exact ⟨cst z a, by change IsLocalRing.residue ↥A (evVP A P (ρ (cst z a))) = _; rw [hρcst]⟩
    have hker : RingHom.ker g = maximalIdeal _ :=
      IsLocalRing.eq_maximalIdeal (RingHom.ker_isMaximal_of_surjective g hg_surj)
    refine ⟨hz, fun s hs => ?_⟩
    rw [mem_nonunits_iff_not_isUnit _ (hmem s), isUnit_VP_iff]
    rw [← hker, RingHom.mem_ker] at hs
    have hs' : evVP A P (ρ s) ∈ maximalIdeal ↥A := (IsLocalRing.residue_eq_zero_iff _).1 hs
    intro hu
    apply hs'
    have : evVP A P (ρ s) = ⟨P.evalAt (locHom φ z s), evalAt_mem_of_mem_VP (hmem s)⟩ :=
      Subtype.ext (coe_evVP' A P (ρ s))
    rw [this]; exact hu
  have hx_closed : ∀ y : X, x ⤳ y → y = x := fun y hy =>
    (hVPcentre y ((localRing_le_of_specializes φ hy).trans hxle)).eq toBase hxC

  have hspec : ∀ y : X, pt ⤳ y → y = pt ∨ y = x := by
    intro y hy
    have hyle : SemistableModel.localRing X φ y ≤ P.toValuationSubring.toSubring :=
      hpt_eq ▸ localRing_le_of_specializes φ hy
    have hmem : ∀ s, locHom φ y s ∈ P.toValuationSubring := fun s => hyle (locHom_mem φ y s)
    let ρ : X.presheaf.stalk y →+* ↥P.toValuationSubring := (locHom φ y).codRestrict P.toValuationSubring.toSubring hmem
    let g : X.presheaf.stalk y →+* L := (evalHom P).comp ρ
    obtain ⟨W, hW, hWloc⟩ := IsLocalRing.exists_factor_valuationRing g
    have hg_cst : ∀ a : ↥A, g (cst y a) = a := fun a => by
      change evalHom P (ρ (cst y a)) = a
      have : ρ (cst y a) = ⟨algebraMap L F (a : L), P.algebraMap_mem' _⟩ := Subtype.ext (hcst y a)
      rw [this, evalHom_algebraMap]
    have hAW : A ≤ W := fun l hl => by
      have := hW (cst y ⟨l, hl⟩); rwa [hg_cst] at this
    rcases eq_top_or_eq_of_le A hrk W hAW with hW' | hW'
    ·
      left
      refine IsCentre.eq (V := P.toValuationSubring) ⟨hyle, fun s hs => ?_⟩ toBase hptC
      rw [mem_nonunits_iff_not_isUnit _ (hmem s), isUnit_iff_evalHom_ne_zero, not_not]
      by_contra hne
      apply hs
      have hu : IsUnit (g.codRestrict W.toSubring hW s) := by
        change IsUnit (⟨g s, hW s⟩ : ↥W)
        rw [isUnit_iff_inv_mem W (hW s) hne, hW']
        exact ValuationSubring.mem_top _
      exact hWloc.1 _ hu
    ·
      right
      have hyVP : SemistableModel.localRing X φ y ≤ (VP A P).toSubring := by
        rintro f ⟨s, rfl⟩
        refine ⟨hmem s, ?_⟩
        have := hW s
        rw [hW'] at this
        exact this
      exact (hVPcentre y hyVP).eq toBase hxC

  have hsp_uniq : ∀ x' : X, toBase.base x' = closedPoint ↥A → (∀ y : X, x' ⤳ y → y = x') →
      (∀ f : F, f ∈ SemistableModel.localRing X φ x' →
        f ∈ P.toValuationSubring ∧ ∃ h : P.evalAt f ∈ A,
          (IsUnit (⟨P.evalAt f, h⟩ : ↥A) ↔ ∃ g ∈ SemistableModel.localRing X φ x', f * g = 1)) → x' = x := by
    intro x' _ _ hev
    exact (isCentre_of_eval_clause φ A P hev).eq toBase hxC

  have hgen : ∀ y : X, (toBase.base y).asIdeal = ⊥ → y ≠ genericPoint X →
      ∃ P' : Place L F, SemistableModel.localRing X φ y = P'.toValuationSubring.toSubring := by
    intro y hy hyη
    have hne : SemistableModel.localRing X φ y ≠ ⊤ := by
      intro htop
      apply hyη
      have hmax : maximalIdeal (X.presheaf.stalk y) = ⊥ := by
        refine (Submodule.eq_bot_iff _).2 fun s hs => ?_
        by_contra hs0
        apply hs
        rw [isUnit_iff_exists_mul_eq_one φ y s]
        refine ⟨(locHom φ y s)⁻¹, by rw [htop]; exact Subring.mem_top _, mul_inv_cancel₀ ?_⟩
        exact (map_ne_zero_iff _ (locHom_injective φ y)).2 hs0
      obtain ⟨hη, -, hiff⟩ :=
        AlgebraicGeometry.Scheme.exists_fromSpecStalk_specializes_and_mem_iff_residue_eq_zero_and_eq_genericPoint_iff
          y (⊥ : Ideal (X.presheaf.stalk y))
      have hcl : IsLocalRing.closedPoint (X.presheaf.stalk y) = ⟨⊥, Ideal.bot_prime⟩ := PrimeSpectrum.ext hmax
      have hy' := Scheme.fromSpecStalk_closedPoint (X := X) (x := y)
      rw [hcl] at hy'
      rw [← hy']
      exact hiff.2 rfl
    obtain ⟨P', hP'⟩ := hplace y hy hne
    exact ⟨P', hP'.symm⟩
  exact ⟨pt, hpt_eq, hpt_uniq, hpt_gen, x, hptx, hx_ne, hxbase, hx_closed, hspec, hx_eval, hsp_uniq, hgen⟩

end Main
p2m_reactivate "P2MW.S_AlgebraicCurve_existsUnique_point_localRing_eq_and_specializes_closedPoint_and_forall_eq_of_isProper_of_isIntegrallyClosed.M3aGlue"

end S_AlgebraicCurve_existsUnique_point_localRing_eq_and_specializes_closedPoint_and_forall_eq_of_isProper_of_isIntegrallyClosed
end P2MW
export P2MW.S_AlgebraicCurve_existsUnique_point_localRing_eq_and_specializes_closedPoint_and_forall_eq_of_isProper_of_isIntegrallyClosed (solution)
