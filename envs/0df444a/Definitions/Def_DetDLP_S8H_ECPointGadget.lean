-- Prove2me | Definitions.Def_DetDLP_S8H_ECPointGadget
-- name    : DetDLP_S8H_ECPointGadget
-- status  : Definition
-- author  : @Bingsheng
-- created : 2026-11-24T04:26:38.49893+00:00
-- url     : https://prove2.me/theorems/903064a9-7dcf-4b9d-be86-a3dd89e048d4
-- title:
--   Canonical elliptic-curve point words and their parsimonious reference tensor
-- statement:
--   The infinity bit and two fixed-width big-endian coordinates canonically represent a point on a general elliptic Weierstrass curve. The decoder checks canonical residues and the curve equation. A two-vertex reference tensor accepts exactly the words of points satisfying a chosen pin. Its accepting assignments count the curve order or the selected affine hash block with a prescribed prefix. The reference graph is unsplit and does not claim the sublinear degree bound.
-- source:
--   S. Liu, B. Zhang, and K. Ren, "A Deterministic Subexponential-time Algorithm for the Discrete Logarithm Problem", Zhejiang University Preprint, 23 November 2026, Section 2.4 & Section 3.1–3.2, Lemma 2.4 & Theorem 3.1 (pp. 9–13)

import Definitions.Def_DetDLP_M89_S1_Queries

set_option autoImplicit false
namespace DetDLP.S8H.ECPointGadget
open DetDLP.M89S1

/-- Decode fixed-width, most-significant-bit-first coordinates. -/
def unsigned (w : List Bool) : ℕ := (BitVec.ofBoolListBE w).toNat

theorem unsigned_digitWord {b n : ℕ} (h : n < 2^b) : unsigned (digitWord b n) = n := by
  apply Nat.eq_of_testBit_eq
  intro i
  change (BitVec.ofBoolListBE (digitWord b n)).getLsbD i = _
  by_cases hi : i < b
  · simp [digitWord, hi, Fin.rev, show b - (b - 1 - i + 1) = i by omega]
  · simp [BitVec.getLsbD_ofBoolListBE, digitWord, hi, Nat.testBit_lt_two_pow (lt_of_lt_of_le h (Nat.pow_le_pow_right (by decide) (by omega : b ≤ i)))]

/-- A failed range or curve test never produces a point. Infinity has one encoding. -/
noncomputable def parse {p : ℕ} [Fact p.Prime] (E : WeierstrassCurve (ZMod p)) [E.IsElliptic]
    (b : ℕ) : List Bool → Option E.toAffine.Point
  | [] => none
  | true :: w => if w = digitWord b 0 ++ digitWord b 0 then some .zero else none
  | false :: w =>
    let x : ZMod p := unsigned (w.take b)
    let y : ZMod p := unsigned (w.drop b)
    if w = digitWord b x.val ++ digitWord b y.val then
      if h : y^2 + E.a₁*x*y + E.a₃*y = x^3 + E.a₂*x^2 + E.a₄*x + E.a₆ then
        some (.some x y (E.toAffine.equation_iff_nonsingular.mp ((E.toAffine.equation_iff x y).mpr h)))
      else none
    else none

private theorem take_digits (b x y : ℕ) :
    (digitWord b x ++ digitWord b y).take b = digitWord b x := by
  simpa [digitWord] using (List.take_left (l₁ := digitWord b x) (l₂ := digitWord b y))

private theorem drop_digits (b x y : ℕ) :
    (digitWord b x ++ digitWord b y).drop b = digitWord b y := by
  simpa [digitWord] using (List.drop_left (l₁ := digitWord b x) (l₂ := digitWord b y))

variable {p : ℕ} [Fact p.Prime] {E : WeierstrassCurve (ZMod p)} [E.IsElliptic]

theorem parse_word {b : ℕ} (h : p ≤ 2^b) (P : E.toAffine.Point) :
    parse E b (ecWord b P) = some P := by
  cases P with
  | zero => simp [parse, ecWord]
  | some x y hxy =>
    have eqn := (E.toAffine.equation_iff x y).mp hxy.1
    simp [ecWord, parse, take_digits, drop_digits, unsigned_digitWord (x.val_lt.trans_le h),
      unsigned_digitWord (y.val_lt.trans_le h), eqn]

theorem word_parse {b : ℕ} {w : List Bool} {P : E.toAffine.Point}
    (ok : parse E b w = some P) : ecWord b P = w := by
  cases w with
  | nil => simp [parse] at ok
  | cons tag tail =>
    cases tag <;> simp only [parse] at ok
    · split at ok <;> try contradiction
      rename_i hw
      split at ok <;> try contradiction
      cases ok
      exact congrArg (List.cons false) hw.symm
    · split at ok <;> try contradiction
      rename_i hw
      cases ok
      exact congrArg (List.cons true) hw.symm

/-- General point-word tensor; `pin` can include parity-selected affine hash and prefix tests. -/
noncomputable def relation (E : WeierstrassCurve (ZMod p)) [E.IsElliptic] (b : ℕ)
    (pin : E.toAffine.Point → Bool) (w : List Bool) : Bool :=
  (parse E b w).any pin

def elemPin {m : ℕ} (b T : ℕ) (S : ECSeed p m) (i : Fin m) (η : List Bool)
    (P : E.toAffine.Point) : Bool := ecFactorMem T S i P && decide ((ecWord b P).take η.length = η)

/-- Two-vertex reference BTN. Its interface is the entire point word; this unsplit
    graph records semantics, not a sublinear maximum-degree bound. -/
abbrev graph (k : ℕ) : BipartiteMultigraph where
  nV := 2
  nE := k
  endpoints _ := (0,1)
  side v := decide (v = 0)
  bipartite _ := by decide

@[simp] theorem ports (k : ℕ) (v : Fin 2) : (graph k).ports v = List.finRange k := by
  fin_cases v <;> simp [BipartiteMultigraph.ports, graph]

noncomputable def tensor {k : ℕ} (R : List Bool → Bool) :
    (v : Fin (graph k).nV) → (Fin ((graph k).deg v) → Bool) → Bool :=
  fun v a => if v = 0 then R (List.ofFn a) else true

theorem read_ports {k : ℕ} (v : Fin 2) (a : Fin k → Bool) :
    List.ofFn (fun j => a (((graph k).ports v).get j)) = List.ofFn a := by
  rw [ports]
  simp [List.get_finRange]

theorem parsimonious (k : ℕ) (R : List Bool → Bool) :
    IsParsimonious (graph k) (tensor R) id (fun a => R (List.ofFn a) = true) := by
  refine ⟨Function.injective_id, fun a => ⟨?_, ?_⟩⟩
  · intro ha
    refine ⟨a, ⟨fun _ => rfl, fun v => ?_⟩, fun x hx => funext hx.1⟩
    unfold tensor
    split
    · exact (congrArg R (read_ports v a)).trans ha
    · rfl
  · rintro hn ⟨x,hx,hv⟩
    have he : x = a := funext hx
    subst x
    have hh := hv (0 : Fin 2)
    simp only [tensor, if_pos rfl] at hh
    exact hn ((congrArg R (read_ports 0 a)).symm.trans hh)

theorem word_length (b : ℕ) (P : E.toAffine.Point) : (ecWord b P).length = 2*b+1 := by
  cases P <;> simp [ecWord, digitWord] <;> omega

/-- External assignment in the order `infinity :: (x ++ y)`. -/
def bus (b : ℕ) (P : E.toAffine.Point) : Fin (2*b+1) → Bool :=
  fun j => (ecWord b P).get (j.cast (word_length b P).symm)

@[simp] theorem bus_list (b : ℕ) (P : E.toAffine.Point) : List.ofFn (bus b P) = ecWord b P := by
  apply List.ext_getElem
  · simp only [List.length_ofFn, word_length]
  · intro i hi hj
    rw [List.getElem_ofFn]
    rfl

/-- The number of accepting external assignments for any point pin is exactly its
    cardinality as a predicate on mathematical curve points. -/
theorem count {b : ℕ} (h : p ≤ 2^b) (pin : E.toAffine.Point → Bool) :
    (Finset.univ.filter (fun a : Fin (2*b+1) → Bool => relation E b pin (List.ofFn a) = true)).card =
      (letI := ecPointFintype E; Finset.univ.filter (fun P => pin P = true)).card := by
  classical
  letI := ecPointFintype E
  let A := Finset.univ.filter (fun P => pin P = true)
  have inj : Function.Injective (@bus p _ E _ b) := by
    intro P Q he
    have hw := congrArg (fun a : Fin (2*b+1) → Bool => parse E b (List.ofFn a)) he
    change parse E b (List.ofFn (bus b P)) = parse E b (List.ofFn (bus b Q)) at hw
    rw [bus_list, bus_list, parse_word h, parse_word h] at hw
    exact Option.some.inj hw
  rw [← Finset.card_image_of_injective A inj]
  congr 1
  ext a
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image, A]
  constructor
  · intro hr
    unfold relation at hr
    cases he : parse E b (List.ofFn a) with
    | none => rw [he] at hr; contradiction
    | some P => rw [he] at hr; exact ⟨P, hr, List.ofFn_injective ((bus_list b P).trans (word_parse he))⟩
  · rintro ⟨P,hp,rfl⟩
    unfold relation
    rw [bus_list, parse_word h]
    exact hp

theorem order_count (E : WeierstrassCurve (ZMod p)) [E.IsElliptic] :
    (Finset.univ.filter (fun a : Fin (2*bitLen p+1) → Bool =>
      relation E (bitLen p) (fun _ => true) (List.ofFn a) = true)).card =
      @Fintype.card _ (ecPointFintype E) := by
  trans (letI := ecPointFintype E; Finset.univ.filter (fun _ : E.toAffine.Point => true = true)).card
  · exact count (b := bitLen p) (Nat.le_pow_clog (by decide) p) _
  · simp

theorem elem_count (E : WeierstrassCurve (ZMod p)) [E.IsElliptic] {m : ℕ}
    (T : ℕ) (S : ECSeed p m) (i : Fin m) (η : List Bool) :
    (Finset.univ.filter (fun a : Fin (2*bitLen p+1) → Bool =>
      relation E (bitLen p) (elemPin (bitLen p) T S i η) (List.ofFn a) = true)).card =
      elemCount (ecFactorBlock E T S i) (ecWord (bitLen p)) η := by
  trans (letI := ecPointFintype E; Finset.univ.filter (fun P : E.toAffine.Point =>
    elemPin (bitLen p) T S i η P = true)).card
  · exact count (b := bitLen p) (Nat.le_pow_clog (by decide) p) _
  · simp [elemCount, ecFactorBlock, elemPin, Finset.filter_filter]

end DetDLP.S8H.ECPointGadget


