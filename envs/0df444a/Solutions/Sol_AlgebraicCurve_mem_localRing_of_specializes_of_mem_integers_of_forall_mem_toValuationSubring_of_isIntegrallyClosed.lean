-- Prove2me | solution 1 for AlgebraicCurve.mem_localRing_of_specializes_of_mem_integers_of_forall_mem_toValuationSubring_of_isIntegrallyClosed
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:02.4153+00:00
-- url     : https://prove2.me/submissions/1c6032bb-ab15-5f99-993b-a49d3464bd77

import Mathlib
import Definitions.Def_AlgebraicCurve_SemistableModel
import Definitions.Def_AlgebraicCurve_RegularProlongation
import Definitions.Def_AlgebraicCurve_IsCurveOver
import Definitions.Def_ModularCurve_UVCrossingModel
import Theorems.Thm_AlgebraicGeometry_Scheme_eq_of_forall_mem_valuationSubring_of_isSeparated
import Theorems.Thm_AlgebraicCurve_exists_place_toSubring_eq_of_isIntegrallyClosedIn_of_isNoetherianRing
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicCurve_mem_localRing_of_specializes_of_mem_integers_of_forall_mem_toValuationSubring_of_isIntegrallyClosed

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
p2m_reactivate "P2MW.S_AlgebraicCurve_mem_localRing_of_specializes_of_mem_integers_of_forall_mem_toValuationSubring_of_isIntegrallyClosed.M3aGlue"

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
p2m_reactivate "P2MW.S_AlgebraicCurve_mem_localRing_of_specializes_of_mem_integers_of_forall_mem_toValuationSubring_of_isIntegrallyClosed.M3aGlue"

end M3aGlue
p2m_reactivate "P2MW.S_AlgebraicCurve_mem_localRing_of_specializes_of_mem_integers_of_forall_mem_toValuationSubring_of_isIntegrallyClosed.M3aGlue"

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
p2m_reactivate "P2MW.S_AlgebraicCurve_mem_localRing_of_specializes_of_mem_integers_of_forall_mem_toValuationSubring_of_isIntegrallyClosed.M3aGlue"

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
p2m_reactivate "P2MW.S_AlgebraicCurve_mem_localRing_of_specializes_of_mem_integers_of_forall_mem_toValuationSubring_of_isIntegrallyClosed.M3aGlue"

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
p2m_reactivate "P2MW.S_AlgebraicCurve_mem_localRing_of_specializes_of_mem_integers_of_forall_mem_toValuationSubring_of_isIntegrallyClosed.M3aGlue"

end M3aGlue
p2m_reactivate "P2MW.S_AlgebraicCurve_mem_localRing_of_specializes_of_mem_integers_of_forall_mem_toValuationSubring_of_isIntegrallyClosed.M3aGlue"

section MainK7a

open M3aGlue ModularCurve ModularCurve.UVCrossingModel

theorem solution
    {L : Type} [Field L] [IsAlgClosed L] (A : ValuationSubring L)
    (hrk : ∀ a b : ↥A, a ∈ maximalIdeal ↥A → b ≠ 0 → ∃ n : ℕ, b ∣ a ^ n)
    {F : Type} [Field F] [Algebra L F] [IsCurveOver L F] [Algebra.EssFiniteType L F]
    (X : Scheme.{0}) (toBase : X ⟶ Spec (CommRingCat.of ↥A))
    [IsIntegral X] [IsProper toBase] [Flat toBase] [LocallyOfFinitePresentation toBase]
    (hn : ∀ y : X, IsIntegrallyClosed (X.presheaf.stalk y))
    (φ : F ≃+* X.functionField)
    (hφ : ∀ a : ↥A, φ (algebraMap L F (a : L)) = SemistableModel.baseToFunctionField toBase a)

    (A₀ : Type) [CommRing A₀] [IsDomain A₀] [IsDiscreteValuationRing A₀]
    (ι₀ : A₀ →+* ↥A) [IsLocalHom ι₀] (hι₀ : Function.Injective ι₀)
    (ϖ₀ : A₀) (hϖ₀ : maximalIdeal A₀ = Ideal.span {ϖ₀})
    (halg : ∀ a : ↥A, IsAlgebraic ↥(ι₀.range) a)
    (X₀ : Scheme.{0}) (toBase₀ : X₀ ⟶ Spec (CommRingCat.of A₀))
    [IsIntegral X₀] [IsProper toBase₀] [Flat toBase₀] [LocallyOfFinitePresentation toBase₀]
    (iso : X ≅ Limits.pullback toBase₀ (Spec.map (CommRingCat.ofHom ι₀)))
    (hiso : iso.hom ≫ Limits.pullback.snd toBase₀ (Spec.map (CommRingCat.ofHom ι₀)) = toBase)

    (x : X) (hx : toBase.base x = closedPoint ↥A) (hxc : ∀ y : X, x ⤳ y → y = x)
    (η₁ η₂ : X) (h₁ : η₁ ⤳ x) (h₂ : η₂ ⤳ x) (h₁x : η₁ ≠ x) (h₂x : η₂ ≠ x) (h₁₂ : η₁ ≠ η₂)
    (hη : ∀ η : X, η ⤳ x → η ≠ x → toBase.base η = closedPoint ↥A → η = η₁ ∨ η = η₂)
    {Fbar₁ : Type} [Field Fbar₁] [Algebra (ResidueField ↥A) Fbar₁]
    {Fbar₂ : Type} [Field Fbar₂] [Algebra (ResidueField ↥A) Fbar₂]
    (R₁ : RegularProlongation A F Fbar₁) (R₂ : RegularProlongation A F Fbar₂)
    (hR₁ : R₁.integers.toSubring = SemistableModel.localRing X φ η₁)
    (hR₂ : R₂.integers.toSubring = SemistableModel.localRing X φ η₂)

    (x₀ : X₀) (hx₀ : (iso.hom ≫ Limits.pullback.fst toBase₀ (Spec.map (CommRingCat.ofHom ι₀))).base x = x₀)
    (w : ℕ) (hw : 1 ≤ w)
    (e : AdicCompletion (maximalIdeal (X₀.presheaf.stalk x₀)) (X₀.presheaf.stalk x₀) ≃+*
      UVCrossingModel (AdicCompletion (maximalIdeal A₀) A₀)
        ((algebraMap A₀ (AdicCompletion (maximalIdeal A₀) A₀) ϖ₀) ^ w))
    (he : ∀ a : A₀,
      e (algebraMap (X₀.presheaf.stalk x₀) (AdicCompletion (maximalIdeal (X₀.presheaf.stalk x₀)) (X₀.presheaf.stalk x₀))
          ((X₀.presheaf.germ ⊤ x₀ trivial).hom
            (toBase₀.appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of A₀)).inv.hom a)))) =
        const ((algebraMap A₀ (AdicCompletion (maximalIdeal A₀) A₀) ϖ₀) ^ w)
          (algebraMap A₀ (AdicCompletion (maximalIdeal A₀) A₀) a))

    (S : Set (Place L F))
    (hS : ∀ P : Place L F, P ∈ S ↔
      ∀ f : F, f ∈ SemistableModel.localRing X φ x → f ∈ P.toValuationSubring ∧ ∃ h : P.evalAt f ∈ A,
        (IsUnit (⟨P.evalAt f, h⟩ : ↥A) ↔ ∃ g ∈ SemistableModel.localRing X φ x, f * g = 1))
    :
    ∀ f : F, f ∈ R₁.integers → f ∈ R₂.integers → (∀ P ∈ S, f ∈ P.toValuationSubring) →
      ∀ y : X, y ⤳ x → y ≠ x → f ∈ SemistableModel.localRing X φ y := by
  classical
  intro f hf₁ hf₂ hfS y hyx hyne

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
  have hϖ : ι₀ ϖ₀ ∈ maximalIdeal ↥A ∧ ι₀ ϖ₀ ≠ 0 := by
    have hϖ₀m : ϖ₀ ∈ maximalIdeal A₀ := by rw [hϖ₀]; exact Ideal.mem_span_singleton_self ϖ₀
    have hϖ₀0 : ϖ₀ ≠ 0 := by
      intro h
      apply IsDiscreteValuationRing.not_isField A₀
      rw [IsLocalRing.isField_iff_maximalIdeal_eq, hϖ₀, h, Ideal.span_singleton_eq_bot]
    refine ⟨?_, fun h => hϖ₀0 (hι₀ (by rw [h, map_zero]))⟩
    intro hu
    exact hϖ₀m ((IsLocalHom.map_nonunit (f := ι₀) ϖ₀) hu)
  have hA : (A : Set L) ≠ Set.univ := by
    intro hA
    apply hϖ.1
    have hne : ((ι₀ ϖ₀ : ↥A) : L) ≠ 0 := fun h => hϖ.2 (Subtype.ext h)
    rw [isUnit_iff_inv_mem A (ι₀ ϖ₀).2 hne]
    · have : ((ι₀ ϖ₀ : ↥A) : L)⁻¹ ∈ (A : Set L) := by rw [hA]; trivial
      exact this

  by_cases hyb : toBase.base y = closedPoint ↥A
  · rcases hη y hyx hyne hyb with rfl | rfl
    · have : f ∈ R₁.integers.toSubring := hf₁
      rwa [hR₁] at this
    · have : f ∈ R₂.integers.toSubring := hf₂
      rwa [hR₂] at this

  have hygen : (toBase.base y).asIdeal = ⊥ := by
    rcases eq_bot_or_eq_maximalIdeal A hrk (toBase.base y).asIdeal with h | h
    · exact h
    · exact absurd (PrimeSpectrum.ext h) hyb
  by_cases htop : SemistableModel.localRing X φ y = ⊤
  · rw [htop]; exact Subring.mem_top f

  have hnorm : IsIntegrallyClosed (X.presheaf.stalk y) := hn y
  have hLmem : ∀ l : L, algebraMap L F l ∈ SemistableModel.localRing X φ y := by
    intro l
    obtain ⟨c, d, hd, rfl⟩ := IsFractionRing.div_surjective (A := ↥A) l
    have hd0 : d ≠ 0 := nonZeroDivisors.ne_zero hd
    have hdU : IsUnit (cst y d) := (hcstU y d).2 (by rw [hygen]; exact fun h => hd0 h)
    obtain ⟨u, hu⟩ := hdU
    rw [map_div₀]
    change algebraMap L F (c : L) / algebraMap L F (d : L) ∈ SemistableModel.localRing X φ y
    rw [div_eq_mul_inv]
    refine Subring.mul_mem _ (hcst y c ▸ locHom_mem φ y (cst y c)) ?_
    have : (algebraMap L F (d : L))⁻¹ = locHom φ y ((u⁻¹ : (X.presheaf.stalk y)ˣ) : X.presheaf.stalk y) := by
      rw [← hcst y d, ← hu]
      symm
      apply eq_inv_of_mul_eq_one_right
      rw [← map_mul, Units.mul_inv, map_one]
    rw [this]; exact locHom_mem φ y _
  obtain ⟨P, hP⟩ : ∃ P : Place L F, P.toValuationSubring.toSubring = SemistableModel.localRing X φ y := by
    haveI : IsNoetherianRing (X.presheaf.stalk y) :=
      isNoetherianRing_stalk_of_asIdeal_eq_bot A hrk hA X toBase y hygen
    haveI : IsNoetherianRing ↥(SemistableModel.localRing X φ y) :=
      isNoetherianRing_of_ringEquiv (X.presheaf.stalk y) (locEquiv φ y)
    haveI : IsLocalRing ↥(SemistableModel.localRing X φ y) :=
      IsLocalRing.of_surjective' (locEquiv φ y).toRingHom (locEquiv φ y).surjective
    have halgR : ∀ r : ↥(SemistableModel.localRing X φ y), algebraMap ↥(SemistableModel.localRing X φ y) F r = (r : F) :=
      fun r => rfl
    haveI : IsFractionRing ↥(SemistableModel.localRing X φ y) F := by
      rw [IsFractionRing, isLocalization_iff]
      refine ⟨?_, ?_, ?_⟩
      · intro s
        rw [halgR]
        exact isUnit_iff_ne_zero.2 fun h => nonZeroDivisors.ne_zero s.2 (Subtype.ext h)
      · intro w
        obtain ⟨a, b, hb, hab⟩ := IsFractionRing.div_surjective (A := X.presheaf.stalk y) (φ w)
        have hb0 : b ≠ 0 := nonZeroDivisors.ne_zero hb
        have hb0' : (locEquiv φ y b) ≠ 0 := fun h => hb0 ((locEquiv φ y).injective (by rw [h, map_zero]))
        refine ⟨(locEquiv φ y a, ⟨locEquiv φ y b, mem_nonZeroDivisors_of_ne_zero hb0'⟩), ?_⟩
        change w * (locEquiv φ y b : F) = (locEquiv φ y a : F)
        rw [coe_locEquiv, coe_locEquiv]
        apply φ.injective
        have hKb : algebraMap (X.presheaf.stalk y) X.functionField b ≠ 0 :=
          fun h => hb0 (IsFractionRing.injective (X.presheaf.stalk y) X.functionField (by rw [h, map_zero]))
        rw [map_mul, φ_locHom, φ_locHom, ← hab, div_mul_cancel₀ _ hKb]
      · intro a b h
        exact ⟨1, by rw [halgR, halgR] at h; rw [Subtype.ext h]⟩
    have hic : IsIntegrallyClosedIn ↥(SemistableModel.localRing X φ y) F := by
      have hK : IsIntegrallyClosedIn (X.presheaf.stalk y) X.functionField :=
        (isIntegrallyClosed_iff_isIntegrallyClosedIn X.functionField).1 hnorm
      rw [isIntegrallyClosedIn_iff] at hK ⊢
      refine ⟨fun a b h => Subtype.ext (by rwa [halgR, halgR] at h), fun {w} hw => ?_⟩
      have hcomp : (φ : F ≃+* X.functionField).toRingHom.comp (algebraMap ↥(SemistableModel.localRing X φ y) F) =
          (algebraMap (X.presheaf.stalk y) X.functionField).comp (locEquiv φ y).symm.toRingHom := by
        ext r
        obtain ⟨s, rfl⟩ := (locEquiv φ y).surjective r
        change φ ((locEquiv φ y s : ↥(SemistableModel.localRing X φ y)) : F) = algebraMap _ _ ((locEquiv φ y).symm (locEquiv φ y s))
        rw [RingEquiv.symm_apply_apply, coe_locEquiv, φ_locHom]
      obtain ⟨p, hp, hpw⟩ := hw
      have hint : IsIntegral (X.presheaf.stalk y) (φ w) := by
        refine ⟨p.map (locEquiv φ y).symm.toRingHom, hp.map _, ?_⟩
        rw [Polynomial.eval₂_map, ← hcomp]
        change Polynomial.eval₂ ((φ : F ≃+* X.functionField).toRingHom.comp _) ((φ : F ≃+* X.functionField).toRingHom w) p = 0
        rw [← Polynomial.hom_eval₂, hpw, map_zero]
      obtain ⟨s, hs⟩ := hK.2 hint
      refine ⟨locEquiv φ y s, ?_⟩
      rw [halgR, coe_locEquiv, locHom_apply, hs, RingEquiv.symm_apply_apply]
    exact AlgebraicCurve.exists_place_toSubring_eq_of_isIntegrallyClosedIn_of_isNoetherianRing
      (SemistableModel.localRing X φ y) hic hLmem htop

  have hyC : IsCentre φ P.toValuationSubring y := isCentre_of_localRing_eq hP.symm
  have hxle : SemistableModel.localRing X φ x ≤ P.toValuationSubring.toSubring :=
    hP ▸ localRing_le_of_specializes φ hyx
  have hmem : ∀ s, locHom φ x s ∈ P.toValuationSubring := fun s => hxle (locHom_mem φ x s)

  have hVPcentre : ∀ z : X, SemistableModel.localRing X φ z ≤ (VP A P).toSubring → IsCentre φ (VP A P) z := by
    intro z hz
    have hmemz : ∀ s, locHom φ z s ∈ VP A P := fun s => hz (locHom_mem φ z s)
    let ρ : X.presheaf.stalk z →+* ↥(VP A P) := (locHom φ z).codRestrict (VP A P).toSubring hmemz
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
    rw [mem_nonunits_iff_not_isUnit _ (hmemz s), isUnit_VP_iff]
    rw [← hker, RingHom.mem_ker] at hs
    have hs' : evVP A P (ρ s) ∈ maximalIdeal ↥A := (IsLocalRing.residue_eq_zero_iff _).1 hs
    intro hu
    apply hs'
    have : evVP A P (ρ s) = ⟨P.evalAt (locHom φ z s), evalAt_mem_of_mem_VP (hmemz s)⟩ :=
      Subtype.ext (coe_evVP' A P (ρ s))
    rw [this]; exact hu

  have hxC : IsCentre φ (VP A P) x := by
    let ρ : X.presheaf.stalk x →+* ↥P.toValuationSubring := (locHom φ x).codRestrict P.toValuationSubring.toSubring hmem
    let g : X.presheaf.stalk x →+* L := (evalHom P).comp ρ
    obtain ⟨W, hW, hWloc⟩ := IsLocalRing.exists_factor_valuationRing g
    have hg_cst : ∀ a : ↥A, g (cst x a) = a := fun a => by
      change evalHom P (ρ (cst x a)) = a
      have : ρ (cst x a) = ⟨algebraMap L F (a : L), P.algebraMap_mem' _⟩ := Subtype.ext (hcst x a)
      rw [this, evalHom_algebraMap]
    have hAW : A ≤ W := fun l hl => by
      have := hW (cst x ⟨l, hl⟩); rwa [hg_cst] at this
    rcases eq_top_or_eq_of_le A hrk W hAW with hW' | hW'
    · exfalso
      apply hyne
      symm
      refine IsCentre.eq (V := P.toValuationSubring) ⟨hxle, fun s hs => ?_⟩ toBase hyC
      rw [mem_nonunits_iff_not_isUnit _ (hmem s), isUnit_iff_evalHom_ne_zero, not_not]
      by_contra hne
      apply hs
      have hu : IsUnit (g.codRestrict W.toSubring hW s) := by
        change IsUnit (⟨g s, hW s⟩ : ↥W)
        rw [isUnit_iff_inv_mem W (hW s) hne, hW']
        exact ValuationSubring.mem_top _
      exact hWloc.1 _ hu
    · apply hVPcentre x
      rintro g' ⟨s, rfl⟩
      refine ⟨hmem s, ?_⟩
      have := hW s
      rw [hW'] at this
      exact this

  have hPS : P ∈ S := (hS P).2 (eval_clause_of_isCentre φ A P hxC)
  have := hfS P hPS
  change f ∈ P.toValuationSubring.toSubring at this
  rwa [hP] at this

end MainK7a
p2m_reactivate "P2MW.S_AlgebraicCurve_mem_localRing_of_specializes_of_mem_integers_of_forall_mem_toValuationSubring_of_isIntegrallyClosed.M3aGlue"

end S_AlgebraicCurve_mem_localRing_of_specializes_of_mem_integers_of_forall_mem_toValuationSubring_of_isIntegrallyClosed
end P2MW
export P2MW.S_AlgebraicCurve_mem_localRing_of_specializes_of_mem_integers_of_forall_mem_toValuationSubring_of_isIntegrallyClosed (solution)
