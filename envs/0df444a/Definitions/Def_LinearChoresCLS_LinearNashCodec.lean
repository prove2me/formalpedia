-- Prove2me | Definitions.Def_LinearChoresCLS_LinearNashCodec
-- name    : LinearChoresCLS_LinearNashCodec
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-26T23:18:53.354528+00:00
-- url     : https://prove2.me/theorems/f65692ad-7ed9-4019-a04b-af132d99e85a
-- title:
--   Polynomial-time parsing and printing of the LinearNash binary codes
-- statement:
--   Polynomial-time parsers and printers for the self-delimiting binary codes of `NetworkEquilibriumCLS.LinearNash` (the encoders used by the CLS search problems on the platform).
--
--   A natural number $n$ is coded as $1^{|b(n)|}\,0\,b(n)$, where $b(n)$ is its little-endian binary expansion; an integer as a sign bit followed by the code of $|z|$; a rational $q$ in lowest terms as the code of its numerator followed by the code of its denominator; a list as the code of its length followed by the codes of its entries.
--
--   The file defines total functions on bit strings that read such a code off the front of a string and return the decoded value and the unread suffix:
--
--   1. `natVal`, `natRest` for a natural number;
--   2. `ratVal`, `ratRest` for a rational number;
--   3. `parseN`, which applies an item parser $k$ times, and `listOf`, which reads a length prefix and then that many items;
--   4. `ratsOf` for a vector of rationals and `rowsOf` for a matrix of rationals.
--
--   Each parser is certified polynomial-time in the multitape-machine calculus of complexitylib (`Turing.MultiTapeTM.ComputableTidilyInPolyTime`), and each has a correctness lemma: on a well-formed code followed by an arbitrary suffix, it returns the encoded value and the suffix. The printers `lnNat_poly`, `lnInt_poly`, `lnRat_poly`, `lnRatList_poly`, `lnRatRows_poly` certify that producing the codes from the corresponding data (rationals in the lowest-terms encoding of `Background.PolyTime.Rat`) is polynomial-time.
--
--   These are the building blocks for showing that maps between encoded instances, such as the instance and answer maps of search reductions, are polynomial-time computable: one parses the input code, computes on the decoded data with the certified arithmetic of `Background.PolyTime.Rat`, and prints the output code.
--
--   **Formalization Note** Polynomial time here is complexitylib's `Turing.MultiTapeTM.ComputableInPolyTime`; on raw bit strings it transfers to Cook's one-tape machines (`CookPvsNP.PolyTimeComputable`) through the proved theorems `CookLevin.isPolyTimeComputable_of_multitape` and `TetrisHard.Rows.cookLevin_to_cookPvsNP`.
-- source:
--   Encodings of NetworkEquilibriumCLS.LinearNash (platform definition NetworkEquilibriumCLS_LinearNash_Encoding); polynomial-time calculus of complexitylib 0ebd467 and Background.PolyTime.Rat (platform definitions). Used for the polynomial-time reduction of Liu–Ma–Tao–Yang–Zheng, arXiv:2611.06589, Section 7.1 (Figure 1).

import Definitions.Def_BuhaiPapers_Background_PolyTime_Rat
import Definitions.Def_BuhaiPapers_Background_PolyTime_Lists
import Definitions.Def_NetworkEquilibriumCLS_LinearNash_Encoding

/-!
# Polynomial-time parsing and printing of the LinearNash binary codes

The public encoders of `NetworkEquilibriumCLS.LinearNash` (`encNat`, `encInt`, `encRat`, `encList`,
`encVector`) write self-delimiting binary codes. This file gives total parsers and printers for these
codes and certifies them with the polynomial-time calculus of complexitylib
(`Turing.MultiTapeTM.ComputableTidilyInPolyTime` / `ComputableInPolyTime`), so that maps between
encoded instances can be shown polynomial-time computable compositionally.

* Parsers: `natVal`/`natRest` (an `encNat` prefix), `ratVal`/`ratRest` (an `encRat` prefix),
  `parseN` (k items), `listOf` (an `encList` with a length prefix), `ratsOf` (a vector of
  rationals), `rowsOf` (a matrix of rationals). Each comes with a polynomial-time certificate and a
  correctness lemma on well-formed codes (`*_spec`).
* Printers: `lnNat_poly`, `lnInt_poly`, `lnRat_poly`, `lnRatList_poly`, `lnRatRows_poly`.

Rationals are carried in the complexitylib/Background encoding `Encoding.encRat` (numerator and
denominator in lowest terms), so the rational arithmetic of `Background.PolyTime.Rat` applies.
-/

set_option autoImplicit false

namespace LinearChoresCLS.Codec
open Turing.MultiTapeTM

/-- number of leading `true`s (the unary length prefix of an LN natural). -/
def lead (w : List Bool) : ℕ := w.idxOf false

def natVal (w : List Bool) : ℕ := ofBits ((w.drop (lead w + 1)).take (lead w))

def natRest (w : List Bool) : List Bool := w.drop (2 * lead w + 1)

theorem lead_spec (n : ℕ) (r : List Bool) :
    lead (NetworkEquilibriumCLS.LinearNash.encNat n ++ r) = n.bits.length := by
  unfold lead NetworkEquilibriumCLS.LinearNash.encNat
  rw [List.append_assoc, List.idxOf_append_of_notMem]
  · simp
  · simp [List.mem_replicate]

theorem ofBits_bits (n : ℕ) : ofBits n.bits = n := Nat.foldr_bit_bits n

theorem natVal_spec (n : ℕ) (r : List Bool) :
    natVal (NetworkEquilibriumCLS.LinearNash.encNat n ++ r) = n := by
  unfold natVal
  rw [lead_spec]
  simp [NetworkEquilibriumCLS.LinearNash.encNat, List.drop_append, ofBits_bits]

theorem natRest_spec (n : ℕ) (r : List Bool) :
    natRest (NetworkEquilibriumCLS.LinearNash.encNat n ++ r) = r := by
  unfold natRest
  rw [lead_spec]
  have : NetworkEquilibriumCLS.LinearNash.encNat n ++ r =
      (List.replicate n.bits.length true ++ false :: n.bits) ++ r := rfl
  rw [this, List.drop_left']
  simp; omega

theorem lead_poly : ComputableTidilyInPolyTime lead encBits encUnary := by
  unfold lead
  exact ComputableTidilyInPolyTime.idxOfWithInput ComputableTidilyInPolyTime.bitsToList
    (ComputableTidilyInPolyTime.const false)


theorem natVal_poly : ComputableTidilyInPolyTime natVal encBits encNat := by
  unfold natVal
  have h1 : ComputableTidilyInPolyTime (fun w : List Bool => w.drop (lead w + 1)) encBits encBits :=
    ComputableTidilyInPolyTime.bitsDropWithInput ComputableTidilyInPolyTime.id'
      (ComputableTidilyInPolyTime.unary_add.comp (lead_poly.prod (ComputableTidilyInPolyTime.const 1)))
  have h2 := ComputableTidilyInPolyTime.bitsTakeWithInput h1 lead_poly
  exact ComputableTidilyInPolyTime.bitsToNat.comp h2

theorem natRest_poly : ComputableTidilyInPolyTime natRest encBits encBits := by
  unfold natRest
  exact ComputableTidilyInPolyTime.bitsDropWithInput ComputableTidilyInPolyTime.id'
    (ComputableTidilyInPolyTime.unary_add.comp
      ((ComputableTidilyInPolyTime.unary_add.comp (lead_poly.prod lead_poly)).prod
        (ComputableTidilyInPolyTime.const 1)) |>.of_enc_eq (fun w => by simp; ring_nf))


def intRest (w : List Bool) : List Bool := natRest w.tail
def ratRest (w : List Bool) : List Bool := natRest (intRest w)
def ratVal (w : List Bool) : ℚ :=
  if w.headD false then -((natVal w.tail : ℚ) / (natVal (intRest w) : ℚ))
  else (natVal w.tail : ℚ) / (natVal (intRest w) : ℚ)

theorem ratVal_spec (q : ℚ) (r : List Bool) : ratVal (NetworkEquilibriumCLS.LinearNash.encRat q ++ r) = q := by
  unfold ratVal intRest
  simp only [NetworkEquilibriumCLS.LinearNash.encRat, NetworkEquilibriumCLS.LinearNash.encInt, List.append_assoc, List.cons_append, List.headD_cons, List.tail_cons,
    natVal_spec, natRest_spec]
  by_cases h : q.num < 0
  · simp only [h, decide_true, if_true]
    have : ((q.num.natAbs : ℕ) : ℚ) = -(q.num : ℚ) := by
      have h2 : ((q.num.natAbs : ℕ) : ℤ) = -q.num := by omega
      rw [show ((q.num.natAbs : ℕ) : ℚ) = (((q.num.natAbs : ℕ) : ℤ) : ℚ) by rw [Int.cast_natCast], h2]
      push_cast; ring
    rw [this, neg_div, neg_neg, Rat.num_div_den]
  · simp only [h, decide_false]
    have : ((q.num.natAbs : ℕ) : ℚ) = (q.num : ℚ) := by
      have h2 : ((q.num.natAbs : ℕ) : ℤ) = q.num := by omega
      rw [show ((q.num.natAbs : ℕ) : ℚ) = (((q.num.natAbs : ℕ) : ℤ) : ℚ) by rw [Int.cast_natCast], h2]
    simp only [Bool.false_eq_true, if_false]
    rw [this, Rat.num_div_den]

theorem ratRest_spec (q : ℚ) (r : List Bool) : ratRest (NetworkEquilibriumCLS.LinearNash.encRat q ++ r) = r := by
  unfold ratRest intRest
  simp only [NetworkEquilibriumCLS.LinearNash.encRat, NetworkEquilibriumCLS.LinearNash.encInt, List.append_assoc, List.cons_append, List.tail_cons, natRest_spec]

attribute [fun_prop] natVal_poly natRest_poly lead_poly

theorem intRest_poly : ComputableTidilyInPolyTime intRest encBits encBits := by
  unfold intRest
  exact natRest_poly.comp ComputableTidilyInPolyTime.bitsTail

theorem ratRest_poly : ComputableTidilyInPolyTime ratRest encBits encBits := by
  unfold ratRest
  exact natRest_poly.comp intRest_poly

open Encoding (encRat) in
theorem ratVal_poly : ComputableInPolyTime ratVal encBits encRat := by
  unfold ratVal
  have ha : ComputableInPolyTime (fun w : List Bool => natVal w.tail) encBits encNat :=
    .of_tidy (natVal_poly.comp ComputableTidilyInPolyTime.bitsTail)
  have hd : ComputableInPolyTime (fun w : List Bool => natVal (intRest w)) encBits encNat :=
    .of_tidy (natVal_poly.comp intRest_poly)
  have hs : ComputableInPolyTime (fun w : List Bool => w.headD false) encBits encBool :=
    .of_tidy (ComputableTidilyInPolyTime.headD (encA := encBool) false)
  have hq := ComputableInPolyTime.rat_div' (ComputableInPolyTime.rat_natCast' ha)
    (ComputableInPolyTime.rat_natCast' hd)
  exact .of_tidy (ComputableTidilyInPolyTime.cond hs.tidy
    (ComputableInPolyTime.rat_neg' hq).tidy hq.tidy)


section Parse
variable {β : Type} {encB : β ↪ List Bool}

def pstep (val : List Bool → β) (rest : List Bool → List Bool) (s : List β × List Bool) :
    List β × List Bool :=
  (s.1 ++ [val s.2], rest s.2)

def parseN (val : List Bool → β) (rest : List Bool → List Bool) (k : ℕ) (w : List Bool) :
    List β × List Bool :=
  (pstep val rest)^[k] ([], w)

theorem pstep_poly (val : List Bool → β) (rest : List Bool → List Bool)
    (hval : ComputableTidilyInPolyTime val encBits encB)
    (hrest : ComputableTidilyInPolyTime rest encBits encBits) :
    ComputableTidilyInPolyTime (pstep val rest) (encPair (encList encB) encBits)
      (encPair (encList encB) encBits) := by
  unfold pstep
  refine ComputableTidilyInPolyTime.prod ?_ (hrest.comp (ComputableTidilyInPolyTime.snd _ _))
  exact ComputableTidilyInPolyTime.listAppend' (ComputableTidilyInPolyTime.fst _ _)
    (ComputableTidilyInPolyTime.cons' (hval.comp (ComputableTidilyInPolyTime.snd _ _))
      (ComputableTidilyInPolyTime.const []))

theorem parseN_poly {α : Type} {encIn : α ↪ List Bool} (val : List Bool → β)
    (rest : List Bool → List Bool)
    (hval : ComputableTidilyInPolyTime val encBits encB)
    (hrest : ComputableTidilyInPolyTime rest encBits encBits)
    (hshrink : ∀ w, (rest w).length ≤ w.length)
    {count : α → ℕ} {word : α → List Bool}
    (hcount : ComputableTidilyInPolyTime count encIn encUnary)
    (hword : ComputableTidilyInPolyTime word encIn encBits) :
    ComputableTidilyInPolyTime (fun x => parseN val rest (count x) (word x)) encIn
      (encPair (encList encB) encBits) := by
  obtain ⟨c, d, hcd⟩ := hval.polyBounded_length.exists_le
  set B : α → ℕ := fun x => 2 * (c * ((word x).length + 1) ^ d) + 1 with hB
  have key := ComputableTidilyInPolyTime.iterate_spec (encState := encPair (encList encB) encBits)
    hcount (init := fun x => (([] : List β), word x))
    (ComputableTidilyInPolyTime.prod (ComputableTidilyInPolyTime.const []) hword)
    (pstep_poly val rest hval hrest)
    (fun x i s => s.2.length ≤ (word x).length ∧ (encList encB s.1).length ≤ i * B x)
    (fun x => by simp)
    (fun x i s _ hs => by
      refine ⟨(hshrink _).trans hs.1, ?_⟩
      simp only [pstep, length_encList, List.map_append, List.sum_append, List.map_cons,
        List.map_nil, List.sum_cons, List.sum_nil] at hs ⊢
      have h1 := hcd s.2
      have h2 : c * ((encBits s.2).length + 1) ^ d ≤ c * ((word x).length + 1) ^ d :=
        Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by simpa [encBits] using hs.1) _)
      have h3 : (List.map (fun a => 2 * (encB a).length + 1) s.1).sum ≤
          i * (2 * (c * ((word x).length + 1) ^ d) + 1) := hs.2
      have h4 : (i + 1) * (2 * (c * ((word x).length + 1) ^ d) + 1) =
          i * (2 * (c * ((word x).length + 1) ^ d) + 1) +
            (2 * (c * ((word x).length + 1) ^ d) + 1) := by ring
      show _ ≤ (i + 1) * (2 * (c * ((word x).length + 1) ^ d) + 1)
      rw [h4]; linarith)
    (size := fun x => 2 * (count x * B x) + 1 + (word x).length)
    ?hsize
    (fun x i s hi hs => by
      simp only [length_encPair]
      have := hs.2
      have : i * B x ≤ count x * B x := Nat.mul_le_mul_right _ hi
      simp [encBits] at *
      omega)
  · exact key.1
  case hsize =>
    have hw := hword.polyBounded_length
    have hc := hcount.polyBounded
    have hwB : PolyBounded (fun x => (encIn x).length) B := by
      simp only [hB]
      refine ((PolyBounded.const 2).mul ((PolyBounded.const c).mul ?_)).add (PolyBounded.const 1)
      exact ((hw.add (PolyBounded.const 1)).pow d).mono (fun x => by simp [encBits])
    exact (((PolyBounded.const 2).mul (hc.mul hwB)).add (PolyBounded.const 1)).add
      (hw.mono (fun x => by simp [encBits]))

theorem parseN_spec (val : List Bool → β) (rest : List Bool → List Bool) (enc : β → List Bool)
    (hval : ∀ b r, val (enc b ++ r) = b) (hrest : ∀ b r, rest (enc b ++ r) = r)
    (xs acc : List β) (r : List Bool) :
    (pstep val rest)^[xs.length] (acc, xs.flatMap enc ++ r) = (acc ++ xs, r) := by
  induction xs generalizing acc with
  | nil => simp
  | cons b xs ih =>
    rw [List.length_cons, Function.iterate_succ_apply]
    simp only [List.flatMap_cons, List.append_assoc, pstep, hval, hrest]
    rw [ih]; simp

end Parse


/-! ### Printers -/

open ComputableTidilyInPolyTime in
theorem lnNat_poly :
    ComputableTidilyInPolyTime NetworkEquilibriumCLS.LinearNash.encNat encNat encBits := by
  unfold NetworkEquilibriumCLS.LinearNash.encNat
  have hb : ComputableTidilyInPolyTime (fun n : ℕ => n.bits) encNat encBits := natBits
  exact bitsAppend ((bitsReplicate true).comp (length_bits.comp hb))
    (bitsCons (const false) hb)

open ComputableTidilyInPolyTime in
theorem lnNat_poly' {α : Type} {encIn : α ↪ List Bool} {f : α → ℕ}
    (hf : ComputableTidilyInPolyTime f encIn encNat) :
    ComputableTidilyInPolyTime (fun x => NetworkEquilibriumCLS.LinearNash.encNat (f x)) encIn
      encBits := lnNat_poly.comp hf

open ComputableTidilyInPolyTime in
theorem lnInt_poly :
    ComputableTidilyInPolyTime NetworkEquilibriumCLS.LinearNash.encInt encIntBin encBits := by
  unfold NetworkEquilibriumCLS.LinearNash.encInt
  exact bitsCons intBin_isNeg (lnNat_poly.comp intBin_natAbs)

open Encoding (encRat) in
theorem lnRat_poly :
    ComputableTidilyInPolyTime NetworkEquilibriumCLS.LinearNash.encRat encRat encBits := by
  unfold NetworkEquilibriumCLS.LinearNash.encRat
  exact ComputableTidilyInPolyTime.bitsAppend
    (lnInt_poly.comp (ComputableInPolyTime.rat_num' ComputableInPolyTime.id').tidy)
    (lnNat_poly.comp (ComputableInPolyTime.rat_den' ComputableInPolyTime.id').tidy)

open Encoding (encRat) in
theorem lnRats_poly :
    ComputableTidilyInPolyTime (fun l : List ℚ => l.flatMap NetworkEquilibriumCLS.LinearNash.encRat)
      (encList encRat) encBits :=
  ComputableTidilyInPolyTime.flatMapToBitsWithInput ComputableTidilyInPolyTime.id'
    (lnRat_poly.comp (ComputableTidilyInPolyTime.snd _ _))

open Encoding (encRat) in
/-- `encList encRat` of LinearNash (length prefix, then the rationals) from a list of rationals. -/
theorem lnRatList_poly :
    ComputableTidilyInPolyTime
      (fun l : List ℚ => NetworkEquilibriumCLS.LinearNash.encList
        NetworkEquilibriumCLS.LinearNash.encRat l) (encList encRat) encBits := by
  unfold NetworkEquilibriumCLS.LinearNash.encList
  exact ComputableTidilyInPolyTime.bitsAppend
    (lnNat_poly.comp (ComputableTidilyInPolyTime.unary_to_binary.comp
      (ComputableTidilyInPolyTime.length_list encRat)))
    lnRats_poly


open Encoding (encRat) in
/-- LinearNash code of a matrix (list of rows) of rationals. -/
theorem lnRatRows_poly :
    ComputableTidilyInPolyTime
      (fun l : List (List ℚ) => NetworkEquilibriumCLS.LinearNash.encList
        (NetworkEquilibriumCLS.LinearNash.encList NetworkEquilibriumCLS.LinearNash.encRat) l)
      (encList (encList encRat)) encBits := by
  unfold NetworkEquilibriumCLS.LinearNash.encList
  exact ComputableTidilyInPolyTime.bitsAppend
    (lnNat_poly.comp (ComputableTidilyInPolyTime.unary_to_binary.comp
      (ComputableTidilyInPolyTime.length_list (encList encRat))))
    (ComputableTidilyInPolyTime.flatMapToBitsWithInput ComputableTidilyInPolyTime.id'
      (lnRatList_poly.comp (ComputableTidilyInPolyTime.snd _ _)))

/-! ### Lists, vectors, matrices -/

theorem natRest_le (w : List Bool) : (natRest w).length ≤ w.length := by
  unfold natRest; simp
theorem intRest_le (w : List Bool) : (intRest w).length ≤ w.length := by
  unfold intRest; exact (natRest_le _).trans (by simp)
theorem ratRest_le (w : List Bool) : (ratRest w).length ≤ w.length := by
  unfold ratRest; exact (natRest_le _).trans (intRest_le _)

theorem parseN_rest_le {β : Type} (val : List Bool → β) (rest : List Bool → List Bool)
    (hshrink : ∀ w, (rest w).length ≤ w.length) (k : ℕ) (w : List Bool) :
    (parseN val rest k w).2.length ≤ w.length := by
  unfold parseN
  suffices ∀ (k : ℕ) (s : List β × List Bool), ((pstep val rest)^[k] s).2.length ≤ s.2.length from
    this k ([], w)
  intro k
  induction k with
  | zero => intro s; simp
  | succ k ih =>
    intro s
    rw [Function.iterate_succ_apply]
    exact (ih _).trans (hshrink _)

/-- Parse a LinearNash list (length prefix, then items) with an item parser. -/
def listOf {β : Type} (val : List Bool → β) (rest : List Bool → List Bool) (u : List Bool) :
    List β × List Bool :=
  parseN val rest (min (natRest u).length (natVal u)) (natRest u)

theorem listOf_poly {β : Type} {encB : β ↪ List Bool} (val : List Bool → β)
    (rest : List Bool → List Bool)
    (hval : ComputableTidilyInPolyTime val encBits encB)
    (hrest : ComputableTidilyInPolyTime rest encBits encBits)
    (hshrink : ∀ w, (rest w).length ≤ w.length) :
    ComputableTidilyInPolyTime (listOf val rest) encBits (encPair (encList encB) encBits) := by
  unfold listOf
  refine parseN_poly val rest hval hrest hshrink ?_ natRest_poly
  exact (ComputableInPolyTime.binary_min_unary' (.of_tidy (ComputableTidilyInPolyTime.length_bits.comp
    natRest_poly)) (.of_tidy natVal_poly)).tidy

theorem listOf_spec {β : Type} (val : List Bool → β) (rest : List Bool → List Bool)
    (enc : β → List Bool) (hne : ∀ b, enc b ≠ [])
    (hval : ∀ b r, val (enc b ++ r) = b) (hrest : ∀ b r, rest (enc b ++ r) = r)
    (xs : List β) (r : List Bool) :
    listOf val rest (NetworkEquilibriumCLS.LinearNash.encList enc xs ++ r) = (xs, r) := by
  unfold listOf
  simp only [NetworkEquilibriumCLS.LinearNash.encList, List.append_assoc, natRest_spec,
    natVal_spec]
  have hlen : xs.length ≤ (xs.flatMap enc ++ r).length := by
    simp only [List.length_append, List.length_flatMap]
    have : ∀ l : List β, l.length ≤ (l.map fun b => (enc b).length).sum := by
      intro l; induction l with
      | nil => simp
      | cons b l ih =>
        simp only [List.length_cons, List.map_cons, List.sum_cons]
        have := List.length_pos_of_ne_nil (hne b); omega
    have := this xs; omega
  rw [min_eq_right hlen]
  unfold parseN
  rw [parseN_spec val rest enc hval hrest xs [] r]; simp

theorem lnRat_ne (q : ℚ) : NetworkEquilibriumCLS.LinearNash.encRat q ≠ [] := by
  simp [NetworkEquilibriumCLS.LinearNash.encRat, NetworkEquilibriumCLS.LinearNash.encInt]

theorem lnList_ne {β : Type} (enc : β → List Bool) (xs : List β) :
    NetworkEquilibriumCLS.LinearNash.encList enc xs ≠ [] := by
  simp [NetworkEquilibriumCLS.LinearNash.encList, NetworkEquilibriumCLS.LinearNash.encNat]

/-- Parse a LinearNash vector of rationals. -/
def ratsOf : List Bool → List ℚ × List Bool := listOf ratVal ratRest

open Encoding (encRat) in
theorem ratsOf_poly : ComputableTidilyInPolyTime ratsOf encBits (encPair (encList encRat) encBits) :=
  listOf_poly ratVal ratRest ratVal_poly.tidy ratRest_poly ratRest_le

theorem ratsOf_spec (xs : List ℚ) (r : List Bool) :
    ratsOf (NetworkEquilibriumCLS.LinearNash.encList NetworkEquilibriumCLS.LinearNash.encRat xs
      ++ r) = (xs, r) :=
  listOf_spec ratVal ratRest _ lnRat_ne ratVal_spec ratRest_spec xs r

theorem ratsOf_le (w : List Bool) : (ratsOf w).2.length ≤ w.length :=
  (parseN_rest_le _ _ ratRest_le _ _).trans (natRest_le _)

/-- Parse a LinearNash matrix (list of lists) of rationals. -/
def rowsOf : List Bool → List (List ℚ) × List Bool :=
  listOf (fun u => (ratsOf u).1) (fun u => (ratsOf u).2)

open Encoding (encRat) in
theorem rowsOf_poly :
    ComputableTidilyInPolyTime rowsOf encBits (encPair (encList (encList encRat)) encBits) :=
  listOf_poly _ _ (ratsOf_poly.fst') (ratsOf_poly.snd') ratsOf_le

theorem rowsOf_spec (xs : List (List ℚ)) (r : List Bool) :
    rowsOf (NetworkEquilibriumCLS.LinearNash.encList (NetworkEquilibriumCLS.LinearNash.encList
      NetworkEquilibriumCLS.LinearNash.encRat) xs ++ r) = (xs, r) :=
  listOf_spec _ _ _ (lnList_ne _) (fun b r => by simp [ratsOf_spec])
    (fun b r => by simp [ratsOf_spec]) xs r

end LinearChoresCLS.Codec


