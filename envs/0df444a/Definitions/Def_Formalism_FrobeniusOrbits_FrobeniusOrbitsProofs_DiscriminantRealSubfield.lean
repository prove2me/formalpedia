-- Prove2me | Definitions.Def_Formalism_FrobeniusOrbits_FrobeniusOrbitsProofs_DiscriminantRealSubfield
-- name    : Formalism_FrobeniusOrbits_FrobeniusOrbitsProofs_DiscriminantRealSubfield
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T16:56:48.631804+00:00
-- url     : https://prove2.me/theorems/0213b718-f37a-4a18-8051-406806a06a1d
-- title:
--   Discriminant Real Subfield
-- statement:
--   Definitions and structural lemmas for Discriminant Real Subfield, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FrobeniusOrbits/FrobeniusOrbitsProofs/DiscriminantRealSubfield.lean

import Mathlib
import Definitions.Def_Formalism_FrobeniusOrbits_DiscrMaximalRealCyclotomic
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IntermediateField Polynomial
noncomputable section
namespace Formalism.FrobeniusOrbits
namespace Discr
section Cyc
variable {K : Type*} [Field K] [NumberField K] {e : ℕ} {z : K}
def th (z : K) : ℚ⟮z + z⁻¹⟯ := AdjoinSimple.gen ℚ (z + z⁻¹)
variable [IsCyclotomicExtension {2 ^ (e + 2)} ℚ K]
end Cyc
end Discr
namespace Discr
variable {L : Type} [Field L] [NumberField L]
lemma real_subfield_le_adjoin (ζ : L) : F1 ζ ≤ ℚ⟮ζ⟯ := by
  unfold F1
  exact IntermediateField.adjoin_simple_le_iff.mpr
    (add_mem (IntermediateField.mem_adjoin_simple_self ℚ ζ)
      (inv_mem (IntermediateField.mem_adjoin_simple_self ℚ ζ)))
abbrev Fz (ζ : L) : IntermediateField ℚ ℚ⟮ζ⟯ :=
  @IntermediateField.adjoin ℚ _ ℚ⟮ζ⟯ _ DivisionRing.toRatAlgebra
    {(AdjoinSimple.gen ℚ ζ) + (AdjoinSimple.gen ℚ ζ)⁻¹}
lemma mem_F_iff (ζ : L) (x : ℚ⟮ζ⟯) :
    x ∈ Fz ζ ↔ (x : L) ∈ F1 ζ := by
  have key : ∀ (f : ℚ →+* ℚ⟮ζ⟯) (q : ℚ),
      (IntermediateField.val ℚ⟮ζ⟯ : ℚ⟮ζ⟯ →+* L) (f q) = algebraMap ℚ L q := fun f q =>
    RingHom.congr_fun
      (RingHom.ext_rat ((IntermediateField.val ℚ⟮ζ⟯ : ℚ⟮ζ⟯ →+* L).comp f) (algebraMap ℚ L)) q
  constructor
  · intro hx
    refine (Subfield.closure_le
      (t := (F1 ζ).toSubfield.comap (IntermediateField.val ℚ⟮ζ⟯ : ℚ⟮ζ⟯ →+* L))).mpr ?_ hx
    rintro y (⟨q, rfl⟩ | rfl)
    · rw [SetLike.mem_coe, Subfield.mem_comap, key]
      exact (F1 ζ).algebraMap_mem q
    · show (ζ + ζ⁻¹ : L) ∈ F1 ζ
      unfold F1
      exact IntermediateField.mem_adjoin_simple_self ℚ _
  · intro hx
    have hS : (F1 ζ).toSubfield ≤
        (Fz ζ).toSubfield.map (IntermediateField.val ℚ⟮ζ⟯ : ℚ⟮ζ⟯ →+* L) := by
      unfold F1
      refine Subfield.closure_le.mpr ?_
      rintro y (⟨q, rfl⟩ | rfl)
      · exact ⟨_, (Fz ζ).algebraMap_mem q, key _ q⟩
      · exact ⟨AdjoinSimple.gen ℚ ζ + (AdjoinSimple.gen ℚ ζ)⁻¹,
          Subfield.subset_closure (Or.inr rfl), rfl⟩
    obtain ⟨y, hy, hyx⟩ := hS hx
    have hxy : y = x := Subtype.ext hyx
    subst hxy
    exact hy
def equivF (ζ : L) : Fz ζ ≃+* F1 ζ where
  toFun x := ⟨((x : ℚ⟮ζ⟯) : L), (mem_F_iff ζ x).1 x.2⟩
  invFun y := ⟨⟨y, real_subfield_le_adjoin ζ y.2⟩, (mem_F_iff ζ ⟨y, real_subfield_le_adjoin ζ y.2⟩).2 y.2⟩
  left_inv _ := Subtype.ext (Subtype.ext rfl)
  right_inv := fun ⟨_, _⟩ => rfl
  map_mul' _ _ := rfl
  map_add' _ _ := rfl
end Discr
end Formalism.FrobeniusOrbits


