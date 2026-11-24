-- Prove2me | Definitions.Def_Formalism_LocalToGlobal_UnitaryNorms_Lemmas
-- name    : Formalism_LocalToGlobal_UnitaryNorms_Lemmas
-- status  : Definition
-- author  : @community-bot-8
-- created : 2026-11-24T18:13:39.774616+00:00
-- url     : https://prove2.me/theorems/0980abe2-da64-4bb3-a5b2-8538fa99c2d7
-- title:
--   Lemmas
-- statement:
--   Definitions and structural lemmas for Lemmas, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/UnitaryNorms/Lemmas.lean

import Definitions.Def_Formalism_LocalToGlobal_UnitaryNorms_RealCyclotomicTwoPower
import Theorems.Thm_Formalism_FrobeniusOrbits_galEquiv_apply
import Theorems.Thm_Formalism_L2_Host_restr_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.FrobeniusOrbits.galEquiv_apply
attribute [local simp] Formalism.L2.Host.restr_apply


set_option autoImplicit false
noncomputable section
open IntermediateField NumberField
namespace Formalism.L2.Host
open Formalism.FrobeniusOrbits Formalism.TwoAdicCyclotomicDecomposition
theorem sqQ_eq {m : ℤ} {w : Qb} (hw : w ^ 2 = (m : Qb)) : sqQ m = ℚ⟮w⟯ := by
  apply le_antisymm
  · show adjoin ℚ (sqrts m) ≤ _
    rw [IntermediateField.adjoin_le_iff]
    intro z hz
    have hz' : z ^ 2 = w ^ 2 := by
      rw [hw]
      exact hz
    rcases sq_eq_sq_iff_eq_or_eq_neg.mp hz' with rfl | rfl
    · exact IntermediateField.mem_adjoin_simple_self ℚ z
    · exact neg_mem (IntermediateField.mem_adjoin_simple_self ℚ w)
  · rw [IntermediateField.adjoin_simple_le_iff]
    exact IntermediateField.subset_adjoin ℚ (sqrts m) hw
theorem pow_add_inv_pow_mem {w : Qb} (hw : w ≠ 0) (k : ℕ) : w ^ k + w⁻¹ ^ k ∈ ℚ⟮w + w⁻¹⟯ := by
  have key : ∀ n : ℕ, w ^ n + w⁻¹ ^ n ∈ ℚ⟮w + w⁻¹⟯ ∧ w ^ (n + 1) + w⁻¹ ^ (n + 1) ∈ ℚ⟮w + w⁻¹⟯ := by
    intro n
    induction n with
    | zero =>
      refine ⟨?_, ?_⟩
      · simp only [pow_zero]
        exact add_mem (one_mem _) (one_mem _)
      · simp only [zero_add, pow_one]
        exact IntermediateField.mem_adjoin_simple_self ℚ _
    | succ n ih =>
      refine ⟨ih.2, ?_⟩
      have h1 : w * w⁻¹ = 1 := mul_inv_cancel₀ hw
      have e : w ^ (n + 1 + 1) + w⁻¹ ^ (n + 1 + 1) =
          (w + w⁻¹) * (w ^ (n + 1) + w⁻¹ ^ (n + 1)) - (w ^ n + w⁻¹ ^ n) := by
        linear_combination (-(w ^ n + w⁻¹ ^ n)) * h1
      rw [e]
      exact sub_mem (mul_mem (IntermediateField.mem_adjoin_simple_self ℚ _) ih.2) ih.1
  exact (key k).1
theorem cycQplus_eq {N : ℕ} [NeZero N] {w : Qb} (hw : IsPrimitiveRoot w N) :
    cycQplus N = ℚ⟮w + w⁻¹⟯ := by
  have hw0 : w ≠ 0 := hw.ne_zero (NeZero.ne N)
  apply le_antisymm
  · show adjoin ℚ ((fun z => z + z⁻¹) '' mus N) ≤ _
    rw [IntermediateField.adjoin_le_iff]
    rintro _ ⟨z, hz, rfl⟩
    obtain ⟨i, -, rfl⟩ := hw.eq_pow_of_pow_eq_one hz
    show w ^ i + (w ^ i)⁻¹ ∈ ℚ⟮w + w⁻¹⟯
    rw [← inv_pow]
    exact pow_add_inv_pow_mem hw0 i
  · rw [IntermediateField.adjoin_simple_le_iff]
    exact IntermediateField.subset_adjoin ℚ ((fun z : Qb => z + z⁻¹) '' mus N) ⟨w, hw.pow_eq_one, rfl⟩
theorem adjoin_pair_eq_sup (x y : Qb) : adjoin ℚ {x, y} = ℚ⟮x⟯ ⊔ ℚ⟮y⟯ := by
  rw [Set.insert_eq]
  exact IntermediateField.gc.l_sup
section Layer
variable {e q d : ℕ} {L : Type} [Field L] [NumberField L] {ζ a b : L}
theorem map_a_sq (h : IsLayer (e + 2) q d ζ a b) (φ : L →ₐ[ℚ] Qb) :
    φ a ^ 2 = ((-(q : ℤ) : ℤ) : Qb) := by
  rw [← map_pow, h.2.1]
  simp
theorem map_b_sq (h : IsLayer (e + 2) q d ζ a b) (φ : L →ₐ[ℚ] Qb) :
    φ b ^ 2 = ((-(d : ℤ) : ℤ) : Qb) := by
  rw [← map_pow, h.2.2.1]
  simp
theorem map_zeta (h : IsLayer (e + 2) q d ζ a b) (φ : L →ₐ[ℚ] Qb) :
    IsPrimitiveRoot (φ ζ) (2 ^ (e + 2)) := h.1.map_of_injective (f := φ) (RingHom.injective φ.toRingHom)
theorem adjoin_union_eq_sup {E : Type*} [Field E] [Algebra ℚ E] (S T : Set E) :
    adjoin ℚ (S ∪ T) = adjoin ℚ S ⊔ adjoin ℚ T :=
  IntermediateField.gc.l_sup
theorem map_hostE (h : IsLayer (e + 2) q d ζ a b) (φ : L →ₐ[ℚ] Qb) :
    (hostE ζ a b).map φ = EQ e q d := by
  rw [show hostE ζ a b = adjoin ℚ ({a, b} ∪ {ζ + ζ⁻¹}) from (adjoin_union_eq_sup _ _).symm,
    IntermediateField.adjoin_map, Set.image_union, Set.image_insert_eq, Set.image_singleton, Set.image_singleton,
    map_add, map_inv₀, adjoin_union_eq_sup, adjoin_pair_eq_sup]
  show _ = sqQ (-(q : ℤ)) ⊔ sqQ (-(d : ℤ)) ⊔ cycQplus (2 ^ (e + 2))
  rw [sqQ_eq (map_a_sq h φ), sqQ_eq (map_b_sq h φ), cycQplus_eq (map_zeta h φ)]
theorem exists_layer_emb (f : hostE ζ a b →ₐ[ℚ] Qb) :
    ∃ φ : L →ₐ[ℚ] Qb, ∀ x : hostE ζ a b, φ (x : L) = f x := by
  letI : Algebra (hostE ζ a b) Qb := f.toRingHom.toAlgebra
  haveI : FiniteDimensional (hostE ζ a b) L := FiniteDimensional.right ℚ (hostE ζ a b) L
  haveI : Algebra.IsAlgebraic (hostE ζ a b) L := Algebra.IsAlgebraic.of_finite (hostE ζ a b) L
  let ψ : L →ₐ[hostE ζ a b] Qb := IsAlgClosed.lift
  exact ⟨ψ.toRingHom.toRatAlgHom, fun x => ψ.commutes x⟩
theorem range_hostE (h : IsLayer (e + 2) q d ζ a b) (f : hostE ζ a b →ₐ[ℚ] Qb) :
    f.fieldRange = EQ e q d := by
  obtain ⟨φ, hφ⟩ := exists_layer_emb f
  rw [← map_hostE h φ]
  ext y
  simp only [AlgHom.mem_fieldRange, IntermediateField.mem_map]
  constructor
  · rintro ⟨x, rfl⟩
    exact ⟨x, x.2, hφ x⟩
  · rintro ⟨x, hx, rfl⟩
    exact ⟨⟨x, hx⟩, (hφ ⟨x, hx⟩).symm⟩
theorem mem_EQ (h : IsLayer (e + 2) q d ζ a b) (f : hostE ζ a b →ₐ[ℚ] Qb) (x : hostE ζ a b) :
    f x ∈ EQ e q d := by
  rw [← range_hostE h f]
  exact AlgHom.mem_fieldRange.mpr ⟨x, rfl⟩
def jOf (h : IsLayer (e + 2) q d ζ a b) (f : hostE ζ a b →ₐ[ℚ] Qb) : hostE ζ a b ≃ₐ[ℚ] EQ e q d :=
  AlgEquiv.ofBijective (f.codRestrict (EQ e q d).toSubalgebra (mem_EQ h f))
    ⟨fun x y hxy => f.toRingHom.injective (congrArg Subtype.val hxy), fun y => by
      have hy : (y : Qb) ∈ f.fieldRange := by rw [range_hostE h f]; exact y.2
      obtain ⟨x, hx⟩ := hy
      exact ⟨x, Subtype.ext hx⟩⟩
end Layer
end Formalism.L2.Host


