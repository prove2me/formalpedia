-- Prove2me | Definitions.Def_CSL_Shared_Indexing_LexBlocks
-- name    : CSL_Shared_Indexing_LexBlocks
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-24T14:08:04.882857+00:00
-- url     : https://prove2.me/theorems/54668158-52c7-429a-aaed-17fc9c15fe5f
-- title:
--   Coded sorting library: Shared / Indexing / LexBlocks
-- statement:
--   Module `CodedSorting.Shared.Indexing.LexBlocks` of the Lean development accompanying B. Li, Z. Li, S. Liu, *Undirected Multiple-Unicast Network Coding and Faster External-Memory Integer Sorting*, arXiv:2610.20079, ported to Lean v4.33.1 and Mathlib `0df444a` (namespace `CodedSorting` renamed to `CSL`).
--
--   All coordinate passes use one layout. Exposing a coordinate as a
--   prefix/field/suffix triple is only reassociation of the same lexicographic
--   file; it is not an uncharged permutation of spectator coordinates.
--
--   This module is part of the machine-checked proof of Theorem 3.1 (external-memory integer sorting) and is imported by the later modules of that development.
-- source:
--   B. Li, Z. Li, S. Liu, *Undirected Multiple-Unicast Network Coding and Faster External-Memory Integer Sorting*, arXiv:2610.20079 (Theorem 3.1, p.4, and Appendix D); Lean development https://github.com/rtyu-1/coded-sorting-lean, module CodedSorting.Shared.Indexing.LexBlocks

import Definitions.Def_CSL_Compat
import Definitions.Def_CSL_Circuit_Framework_TriangularStreams
import Definitions.Def_CSL_Interchange_Framework_Fields_FieldReflection
import Definitions.Def_CSL_Interchange_Framework_Fields_BinaryPaddingScan
import Mathlib.Order.Hom.Set

/-! All coordinate passes use one layout. Exposing a coordinate as a
prefix/field/suffix triple is only reassociation of the same lexicographic
file; it is not an uncharged permutation of spectator coordinates. -/

namespace CSL.LexBlocks

open TriangularStreams SingleCoordinate

variable {m Q : ℕ}

noncomputable def subvectorEncode {J : Type*} [Fintype J] [LinearOrder J]
    [WellFoundedLT J] : (J → Fin Q) ≃ Fin (Q ^ Fintype.card J) :=
  toLex.trans (Fintype.orderIsoFinOfCardEq (Lex (J → Fin Q)) (by simp)).symm.toEquiv

@[simp] theorem subvectorEncode_lt {J : Type*} [Fintype J] [LinearOrder J]
    [WellFoundedLT J] (x y : J → Fin Q) :
    subvectorEncode x < subvectorEncode y ↔ Pi.Lex (· < ·) (· < ·) x y := by
  exact (Fintype.orderIsoFinOfCardEq (Lex (J → Fin Q)) (by simp)).symm.lt_iff_lt

abbrev PrefixCount (Q : ℕ) (i : Fin m) := Q ^ Fintype.card (Before i)
abbrev SuffixCount (Q : ℕ) (i : Fin m) := Q ^ Fintype.card (After i)

noncomputable def splitEncoded (i : Fin m) : (Fin m → Fin Q) ≃
    TripleAddress (PrefixCount Q i) Q (SuffixCount Q i) :=
  (splitVector (R := Fin Q) i).trans
    (Equiv.prodCongr (subvectorEncode (J := Before i) (Q := Q))
      (Equiv.prodCongr (Equiv.refl (Fin Q)) (subvectorEncode (J := After i) (Q := Q))))

noncomputable def blockEncode (i : Fin m) : (Fin m → Fin Q) ≃
    Fin (PrefixCount Q i * (Q * SuffixCount Q i)) :=
  (splitEncoded i).trans tripleEncode

@[simp] theorem blockEncode_apply (i : Fin m) (x : Fin m → Fin Q) :
    blockEncode i x = tripleEncode
      (subvectorEncode (fun j : Before i => x j.val), x i,
        subvectorEncode (fun j : After i => x j.val)) := rfl

theorem blockCard (i : Fin m) : PrefixCount Q i * (Q * SuffixCount Q i) = Q ^ m := by
  have h := Fintype.card_congr (blockEncode (Q := Q) i)
  simpa only [Fintype.card_fin, Fintype.card_fun] using h.symm

/-- Exposing a coordinate preserves the ordinary lexicographic address order. -/
theorem blockEncode_increasing (i : Fin m) (x y : Fin m → Fin Q)
    (hxy : Pi.Lex (· < ·) (· < ·) x y) : blockEncode i x < blockEncode i y := by
  rw [blockEncode_apply, blockEncode_apply, tripleEncode_lt_iff]
  rcases hxy with ⟨j,hpre,hj⟩
  rcases lt_trichotomy j i with hji | hji | hij
  · left
    apply subvectorEncode_lt _ _ |>.mpr
    exact ⟨⟨j,hji⟩, fun k hk => hpre k.val hk, hj⟩
  · subst j
    right
    refine ⟨?_, Or.inl hj⟩
    apply congrArg subvectorEncode
    funext k
    exact hpre k.val k.property
  · right
    refine ⟨?_, Or.inr ⟨hpre i hij, ?_⟩⟩
    · apply congrArg subvectorEncode
      funext k
      exact hpre k.val (k.property.trans hij)
    · apply subvectorEncode_lt _ _ |>.mpr
      exact ⟨⟨j,hij⟩, fun k hk => hpre k.val hk, hj⟩

noncomputable def blockPhysical (i : Fin m) : (Fin m → Fin Q) ≃ Fin (Q ^ m) :=
  (blockEncode i).trans (finCongr (blockCard i))

/-- The coordinate-specific triple is literally the same physical layout. -/
theorem blockPhysical_eq_lexLayout (i : Fin m) :
    blockPhysical (Q := Q) i = lexLayout := by
  let e : Equiv.Perm (Fin (Q ^ m)) := lexLayout.symm.trans (blockPhysical i)
  have hemono : StrictMono e := by
    intro a b hab
    change blockPhysical i (lexLayout.symm a) < blockPhysical i (lexLayout.symm b)
    change blockEncode i (lexLayout.symm a) < blockEncode i (lexLayout.symm b)
    apply blockEncode_increasing
    apply (lexLayout_lt _ _).mp
    simpa only [Equiv.apply_symm_apply] using hab
  have he : (e : Fin (Q ^ m) → Fin (Q ^ m)) = id :=
    (hemono.range_inj strictMono_id).mp (by simp only [Equiv.range_eq_univ, Set.range_id])
  apply Equiv.ext
  intro x
  have h := congrFun he (lexLayout x)
  simpa only [e, Equiv.trans_apply, Equiv.symm_apply_apply, id_eq] using h

/-- Field maps in the triple representation and in the full-vector program agree. -/
theorem field_update_encoded (i : Fin m) (x : Fin m → Fin Q) (a : Fin Q) :
    lexLayout (Function.update x i a) =
      finCongr (blockCard i) (tripleEncode
        (subvectorEncode (fun j : Before i => x j.val), a,
          subvectorEncode (fun j : After i => x j.val))) := by
  rw [← blockPhysical_eq_lexLayout i]
  change finCongr (blockCard i) (blockEncode i (Function.update x i a)) = _
  rw [blockEncode_apply]
  congr 2
  apply Prod.ext
  · apply congrArg subvectorEncode
    funext j
    exact Function.update_of_ne (ne_of_lt j.property) _ _
  · apply Prod.ext
    · exact Function.update_self _ _ _
    · apply congrArg subvectorEncode
      funext j
      exact Function.update_of_ne (ne_of_gt j.property) _ _

/-- No physical move is needed to expose the selected field. -/
theorem blockFieldPermutation (i : Fin m) (e : Equiv.Perm (Fin Q)) (y : Fin (Q ^ m)) :
    finCongr (blockCard i)
      (globalFieldEquiv (S := SuffixCount Q i) (fun (_ : Fin (PrefixCount Q i)) => e)
        ((finCongr (blockCard i)).symm y)) =
      coordinatePermutation i (fun _ => e) (fun _ _ _ => rfl) y := by
  obtain ⟨x,rfl⟩ := lexLayout.surjective y
  have hx : finCongr (blockCard i) (blockEncode i x) = lexLayout x :=
    congrArg (fun e : (Fin m → Fin Q) ≃ Fin (Q ^ m) => e x)
      (blockPhysical_eq_lexLayout i)
  rw [coordinatePermutation_encoded i (fun _ => e) (fun _ _ _ => rfl)]
  rw [field_update_encoded]
  rw [← hx,Equiv.symm_apply_apply,blockEncode_apply,globalFieldEquiv_encoded]

/-- Actual two-pass reflection of any coordinate in the one common layout. -/
theorem coordinate_field_reversal {Value : Type*}
    (source target : BlockReflection.Disk Value) (i : Fin m) (B : ℕ)
    (hB : 0 < B) (hQ : 0 < Q) :
    let result := FieldReflection.execute source target B
      (PrefixCount Q i) Q (SuffixCount Q i) hB
    (∀ y : Fin (Q ^ m), result.disk y.val =
      source ((coordinatePermutation i (fun _ => Fin.revPerm)
        (fun _ _ _ => rfl)) y).val) ∧
      result.trace.length = 10 * ((Q ^ m + B - 1) / B) := by
  obtain ⟨hvalue,hcost⟩ := FieldReflection.global_field_reversal source target B
    (PrefixCount Q i) Q (SuffixCount Q i) hB hQ (pow_pos hQ _)
  constructor
  · intro y
    have h := hvalue ((finCongr (blockCard i)).symm y)
    have he := congrArg Fin.val (blockFieldPermutation i Fin.revPerm y)
    exact h.trans (congrArg source he)
  · simpa only [blockCard] using hcost

end CSL.LexBlocks


