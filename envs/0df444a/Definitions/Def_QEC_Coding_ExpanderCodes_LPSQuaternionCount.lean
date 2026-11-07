-- Prove2me | Definitions.Def_QEC_Coding_ExpanderCodes_LPSQuaternionCount
-- name    : QEC_Coding_ExpanderCodes_LPSQuaternionCount
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-06T21:34:14.651109+00:00
-- url     : https://prove2.me/theorems/e8ab54bd-df9e-4d27-b6c8-8f9c34f2b4bc
-- title:
--   LPSQuaternion Count
-- statement:
--   Definitions and structural lemmas for LPSQuaternion Count, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSQuaternionCount.lean

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSQuaternionShell
import Mathlib.NumberTheory.Multiplicity
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsResiduePrimeAt_q
attribute [local simp] QEC.Coding.TannerLiftedProduct.lpsResiduePrimeAt_q


set_option autoImplicit false
namespace QEC.Coding.TannerLiftedProduct
variable {p : ℕ}
noncomputable def lpsQuaternionFullShell (p : ℕ) : Finset LPSQuaternion :=
  (lpsQuaternionBox p).filter fun t => t.norm = p
theorem mem_lpsQuaternionFullShell_iff
    (hp : 0 < p) (t : LPSQuaternion) :
    t ∈ lpsQuaternionFullShell p ↔ t.norm = p := by
  rw [lpsQuaternionFullShell, Finset.mem_filter]
  exact and_iff_right_of_imp fun ht =>
    (mem_lpsQuaternionBox_iff p t).mpr
      (coordinate_bounds_of_norm hp t ht)
theorem sq_mod_four_eq_zero_of_even
    {x : ℤ} (hx : Even x) : x ^ 2 % 4 = 0 := by
  rcases hx with ⟨y, rfl⟩
  ring_nf
  simp
theorem sq_mod_four_eq_ite_odd (x : ℤ) :
    x ^ 2 % 4 = if Odd x then 1 else 0 := by
  by_cases hx : Odd x
  · simpa [hx] using Int.sq_mod_four_eq_one_of_odd hx
  · have hxEven : Even x := Int.not_odd_iff_even.mp hx
    simpa [hx] using sq_mod_four_eq_zero_of_even hxEven
theorem exactly_one_odd_coordinate
    (hp4 : p % 4 = 1) (t : LPSQuaternion) (ht : t.norm = p) :
    (Odd t.a ∧ ¬ Odd t.b ∧ ¬ Odd t.c ∧ ¬ Odd t.d) ∨
      (¬ Odd t.a ∧ Odd t.b ∧ ¬ Odd t.c ∧ ¬ Odd t.d) ∨
      (¬ Odd t.a ∧ ¬ Odd t.b ∧ Odd t.c ∧ ¬ Odd t.d) ∨
      (¬ Odd t.a ∧ ¬ Odd t.b ∧ ¬ Odd t.c ∧ Odd t.d) := by
  let oa : ℤ := if Odd t.a then 1 else 0
  let ob : ℤ := if Odd t.b then 1 else 0
  let oc : ℤ := if Odd t.c then 1 else 0
  let od : ℤ := if Odd t.d then 1 else 0
  have haMod : t.a ^ 2 % 4 = oa := sq_mod_four_eq_ite_odd t.a
  have hbMod : t.b ^ 2 % 4 = ob := sq_mod_four_eq_ite_odd t.b
  have hcMod : t.c ^ 2 % 4 = oc := sq_mod_four_eq_ite_odd t.c
  have hdMod : t.d ^ 2 % 4 = od := sq_mod_four_eq_ite_odd t.d
  have hpMod : ((p : ℤ) % 4) = 1 := by exact_mod_cast hp4
  have hnorm : t.a ^ 2 + t.b ^ 2 + t.c ^ 2 + t.d ^ 2 = (p : ℤ) := ht
  have hcount : oa + ob + oc + od = 1 := by
    by_cases ha : Odd t.a <;>
      by_cases hb : Odd t.b <;>
      by_cases hc : Odd t.c <;>
      by_cases hd : Odd t.d <;>
      simp [oa, ob, oc, od, ha, hb, hc, hd] at haMod hbMod hcMod hdMod ⊢ <;>
      omega
  by_cases ha : Odd t.a <;>
    by_cases hb : Odd t.b <;>
    by_cases hc : Odd t.c <;>
    by_cases hd : Odd t.d <;>
    simp_all [oa, ob, oc, od]
def signedFirstCoordinate (negative : Bool) (a : ℤ) : ℤ :=
  match negative with
  | false => a
  | true => -a
def placeNormalizedQuaternion
    (i : Fin 4) (negative : Bool) (t : LPSQuaternion) : LPSQuaternion :=
  let sa := signedFirstCoordinate negative t.a
  if i = 0 then
    ⟨sa, t.b, t.c, t.d⟩
  else if i = 1 then
    ⟨t.b, sa, t.c, t.d⟩
  else if i = 2 then
    ⟨t.b, t.c, sa, t.d⟩
  else
    ⟨t.b, t.c, t.d, sa⟩
def unplaceNormalizedQuaternion
    (i : Fin 4) (negative : Bool) (t : LPSQuaternion) : LPSQuaternion :=
  if i = 0 then
    ⟨signedFirstCoordinate negative t.a, t.b, t.c, t.d⟩
  else if i = 1 then
    ⟨signedFirstCoordinate negative t.b, t.a, t.c, t.d⟩
  else if i = 2 then
    ⟨signedFirstCoordinate negative t.c, t.a, t.b, t.d⟩
  else
    ⟨signedFirstCoordinate negative t.d, t.a, t.b, t.c⟩
@[simp] theorem norm_placeNormalizedQuaternion
    (i : Fin 4) (negative : Bool) (t : LPSQuaternion) :
    (placeNormalizedQuaternion i negative t).norm = t.norm := by
  fin_cases i <;> cases negative <;>
    simp [placeNormalizedQuaternion, signedFirstCoordinate,
      LPSQuaternion.norm] <;> ring
@[simp] theorem norm_unplaceNormalizedQuaternion
    (i : Fin 4) (negative : Bool) (t : LPSQuaternion) :
    (unplaceNormalizedQuaternion i negative t).norm = t.norm := by
  fin_cases i <;> cases negative <;>
    simp [unplaceNormalizedQuaternion, signedFirstCoordinate,
      LPSQuaternion.norm] <;> ring
@[simp] theorem place_unplaceNormalizedQuaternion
    (i : Fin 4) (negative : Bool) (t : LPSQuaternion) :
    placeNormalizedQuaternion i negative
      (unplaceNormalizedQuaternion i negative t) = t := by
  fin_cases i <;> cases negative <;>
    simp [placeNormalizedQuaternion, unplaceNormalizedQuaternion,
      signedFirstCoordinate]
@[simp] theorem unplace_placeNormalizedQuaternion
    (i : Fin 4) (negative : Bool) (t : LPSQuaternion) :
    unplaceNormalizedQuaternion i negative
      (placeNormalizedQuaternion i negative t) = t := by
  fin_cases i <;> cases negative <;>
    simp [placeNormalizedQuaternion, unplaceNormalizedQuaternion,
      signedFirstCoordinate]
theorem placeNormalizedQuaternion_injective
    (i : Fin 4) (negative : Bool) :
    Function.Injective (placeNormalizedQuaternion i negative) := by
  intro t u h
  have h' := congrArg (unplaceNormalizedQuaternion i negative) h
  simpa using h'
noncomputable def normalizedQuaternionPlacement
    (hp : 0 < p) :
    Fin 4 × (Bool × {t // t ∈ lpsQuaternionShell p}) →
      {t // t ∈ lpsQuaternionFullShell p} :=
  fun x => ⟨placeNormalizedQuaternion x.1 x.2.1 x.2.2.1,
    (mem_lpsQuaternionFullShell_iff hp _).mpr <| by
      rw [norm_placeNormalizedQuaternion]
      exact norm_eq_of_mem_lpsQuaternionShell hp x.2.2.2⟩
theorem odd_ne_zero {x : ℤ} (hx : Odd x) : x ≠ 0 := by
  intro hzero
  subst x
  simp at hx
theorem normalizedQuaternionPlacement_surjective
    (hp : 0 < p) (hp4 : p % 4 = 1) :
    Function.Surjective (normalizedQuaternionPlacement (p := p) hp) := by
  intro t
  have htNorm : t.1.norm = p :=
    (mem_lpsQuaternionFullShell_iff hp t.1).mp t.2
  rcases exactly_one_odd_coordinate hp4 t.1 htNorm with ha | hb | hc | hd
  · by_cases hpos : 0 < t.1.a
    · let u := unplaceNormalizedQuaternion (0 : Fin 4) false t.1
      have hu : u ∈ lpsQuaternionShell p :=
        (mem_lpsQuaternionShell_iff hp u).mpr ⟨by simpa [u] using htNorm,
          by simpa [u, unplaceNormalizedQuaternion,
            signedFirstCoordinate] using hpos,
          by simpa [u, unplaceNormalizedQuaternion,
            signedFirstCoordinate] using ha.1⟩
      refine ⟨⟨0, false, ⟨u, hu⟩⟩, ?_⟩
      apply Subtype.ext
      exact place_unplaceNormalizedQuaternion 0 false t.1
    · have hneg : 0 < -t.1.a := by
        have hne := odd_ne_zero ha.1
        omega
      let u := unplaceNormalizedQuaternion (0 : Fin 4) true t.1
      have hu : u ∈ lpsQuaternionShell p :=
        (mem_lpsQuaternionShell_iff hp u).mpr ⟨by simpa [u] using htNorm,
          by simpa [u, unplaceNormalizedQuaternion,
            signedFirstCoordinate] using hneg,
          by simpa [u, unplaceNormalizedQuaternion,
            signedFirstCoordinate] using ha.1.neg⟩
      refine ⟨⟨0, true, ⟨u, hu⟩⟩, ?_⟩
      apply Subtype.ext
      exact place_unplaceNormalizedQuaternion 0 true t.1
  · by_cases hpos : 0 < t.1.b
    · let u := unplaceNormalizedQuaternion (1 : Fin 4) false t.1
      have hu : u ∈ lpsQuaternionShell p :=
        (mem_lpsQuaternionShell_iff hp u).mpr ⟨by simpa [u] using htNorm,
          by simpa [u, unplaceNormalizedQuaternion,
            signedFirstCoordinate] using hpos,
          by simpa [u, unplaceNormalizedQuaternion,
            signedFirstCoordinate] using hb.2.1⟩
      refine ⟨⟨1, false, ⟨u, hu⟩⟩, ?_⟩
      apply Subtype.ext
      exact place_unplaceNormalizedQuaternion 1 false t.1
    · have hneg : 0 < -t.1.b := by
        have hne := odd_ne_zero hb.2.1
        omega
      let u := unplaceNormalizedQuaternion (1 : Fin 4) true t.1
      have hu : u ∈ lpsQuaternionShell p :=
        (mem_lpsQuaternionShell_iff hp u).mpr ⟨by simpa [u] using htNorm,
          by simpa [u, unplaceNormalizedQuaternion,
            signedFirstCoordinate] using hneg,
          by simpa [u, unplaceNormalizedQuaternion,
            signedFirstCoordinate] using hb.2.1.neg⟩
      refine ⟨⟨1, true, ⟨u, hu⟩⟩, ?_⟩
      apply Subtype.ext
      exact place_unplaceNormalizedQuaternion 1 true t.1
  · by_cases hpos : 0 < t.1.c
    · let u := unplaceNormalizedQuaternion (2 : Fin 4) false t.1
      have hu : u ∈ lpsQuaternionShell p :=
        (mem_lpsQuaternionShell_iff hp u).mpr ⟨by simpa [u] using htNorm,
          by simpa [u, unplaceNormalizedQuaternion,
            signedFirstCoordinate] using hpos,
          by simpa [u, unplaceNormalizedQuaternion,
            signedFirstCoordinate] using hc.2.2.1⟩
      refine ⟨⟨2, false, ⟨u, hu⟩⟩, ?_⟩
      apply Subtype.ext
      exact place_unplaceNormalizedQuaternion 2 false t.1
    · have hneg : 0 < -t.1.c := by
        have hne := odd_ne_zero hc.2.2.1
        omega
      let u := unplaceNormalizedQuaternion (2 : Fin 4) true t.1
      have hu : u ∈ lpsQuaternionShell p :=
        (mem_lpsQuaternionShell_iff hp u).mpr ⟨by simpa [u] using htNorm,
          by simpa [u, unplaceNormalizedQuaternion,
            signedFirstCoordinate] using hneg,
          by simpa [u, unplaceNormalizedQuaternion,
            signedFirstCoordinate] using hc.2.2.1.neg⟩
      refine ⟨⟨2, true, ⟨u, hu⟩⟩, ?_⟩
      apply Subtype.ext
      exact place_unplaceNormalizedQuaternion 2 true t.1
  · by_cases hpos : 0 < t.1.d
    · let u := unplaceNormalizedQuaternion (3 : Fin 4) false t.1
      have hu : u ∈ lpsQuaternionShell p :=
        (mem_lpsQuaternionShell_iff hp u).mpr ⟨by simpa [u] using htNorm,
          by simpa [u, unplaceNormalizedQuaternion,
            signedFirstCoordinate] using hpos,
          by simpa [u, unplaceNormalizedQuaternion,
            signedFirstCoordinate] using hd.2.2.2⟩
      refine ⟨⟨3, false, ⟨u, hu⟩⟩, ?_⟩
      apply Subtype.ext
      exact place_unplaceNormalizedQuaternion 3 false t.1
    · have hneg : 0 < -t.1.d := by
        have hne := odd_ne_zero hd.2.2.2
        omega
      let u := unplaceNormalizedQuaternion (3 : Fin 4) true t.1
      have hu : u ∈ lpsQuaternionShell p :=
        (mem_lpsQuaternionShell_iff hp u).mpr ⟨by simpa [u] using htNorm,
          by simpa [u, unplaceNormalizedQuaternion,
            signedFirstCoordinate] using hneg,
          by simpa [u, unplaceNormalizedQuaternion,
            signedFirstCoordinate] using hd.2.2.2.neg⟩
      refine ⟨⟨3, true, ⟨u, hu⟩⟩, ?_⟩
      apply Subtype.ext
      exact place_unplaceNormalizedQuaternion 3 true t.1
theorem placement_parameters_eq
    {i j : Fin 4} {negative negative' : Bool} {t u : LPSQuaternion}
    (ht : t.IsNormalizedAt p) (hu : u.IsNormalizedAt p)
    (htOthers : ¬ Odd t.b ∧ ¬ Odd t.c ∧ ¬ Odd t.d)
    (huOthers : ¬ Odd u.b ∧ ¬ Odd u.c ∧ ¬ Odd u.d)
    (h : placeNormalizedQuaternion i negative t =
      placeNormalizedQuaternion j negative' u) :
    i = j ∧ negative = negative' := by
  have htPos := ht.2.1
  have huPos := hu.2.1
  have htOdd := ht.2.2
  have huOdd := hu.2.2
  fin_cases i <;> fin_cases j <;> cases negative <;> cases negative' <;>
    simp [placeNormalizedQuaternion, signedFirstCoordinate,
      LPSQuaternion.mk.injEq] at h ⊢ <;> first | omega | aesop
theorem normalizedQuaternionPlacement_injective
    (hp : 0 < p) (hp4 : p % 4 = 1) :
    Function.Injective (normalizedQuaternionPlacement (p := p) hp) := by
  rintro ⟨i, negative, t⟩ ⟨j, negative', u⟩ h
  have hval := congrArg Subtype.val h
  have htNormalized := (mem_lpsQuaternionShell_iff hp t.1).mp t.2
  have huNormalized := (mem_lpsQuaternionShell_iff hp u.1).mp u.2
  have htOdd : Odd t.1.a := htNormalized.2.2
  have huOdd : Odd u.1.a := huNormalized.2.2
  have htOthers : ¬ Odd t.1.b ∧ ¬ Odd t.1.c ∧ ¬ Odd t.1.d := by
    rcases exactly_one_odd_coordinate hp4 t.1 htNormalized.1 with
      ht | ht | ht | ht
    · exact ht.2
    · exact False.elim (ht.1 htOdd)
    · exact False.elim (ht.1 htOdd)
    · exact False.elim (ht.1 htOdd)
  have huOthers : ¬ Odd u.1.b ∧ ¬ Odd u.1.c ∧ ¬ Odd u.1.d := by
    rcases exactly_one_odd_coordinate hp4 u.1 huNormalized.1 with
      hu | hu | hu | hu
    · exact hu.2
    · exact False.elim (hu.1 huOdd)
    · exact False.elim (hu.1 huOdd)
    · exact False.elim (hu.1 huOdd)
  change placeNormalizedQuaternion i negative t.1 =
    placeNormalizedQuaternion j negative' u.1 at hval
  obtain ⟨rfl, rfl⟩ := placement_parameters_eq
    htNormalized huNormalized htOthers huOthers hval
  have htu : t.1 = u.1 :=
    placeNormalizedQuaternion_injective i negative hval
  have htu' : t = u := Subtype.ext htu
  rw [htu']
noncomputable def normalizedQuaternionPlacementEquiv
    (hp : 0 < p) (hp4 : p % 4 = 1) :
    Fin 4 × (Bool × {t // t ∈ lpsQuaternionShell p}) ≃
      {t // t ∈ lpsQuaternionFullShell p} :=
  Equiv.ofBijective (normalizedQuaternionPlacement (p := p) hp)
    ⟨normalizedQuaternionPlacement_injective hp hp4,
      normalizedQuaternionPlacement_surjective hp hp4⟩
end QEC.Coding.TannerLiftedProduct


