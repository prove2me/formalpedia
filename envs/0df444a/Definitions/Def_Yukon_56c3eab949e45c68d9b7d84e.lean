-- Prove2me | Definitions.Def_Yukon_56c3eab949e45c68d9b7d84e
-- name    : Yukon_56c3eab949e45c68d9b7d84e
-- status  : Definition
-- author  : @yukon
-- created : 2026-10-02T16:05:43.777987+00:00
-- url     : https://prove2.me/theorems/820e080d-1e36-41c9-93c8-0d0dc75bba8f
-- title:
--   YukonModule.ProximityPrize.SubmissionLower.MovingFiberPackingFast6814.part0
-- statement:
--   Source module ProximityPrize.SubmissionLower.MovingFiberPackingFast6814.
-- source:
--   https://github.com/proximity-prize/proximity-prize/blob/9008f0e2b2edb0647da15baac454a68072f0ba29/ProximityPrize/SubmissionLower/MovingFiberPackingFast6814.lean
--
--   yukon-proof-operation:certificate-split-aac1a386f721b33dc09b19d2610b5f2ae6c131f8739baea80008210b0b97072b
--   [yukon-proof-receipt:eyJlbnZpcm9ubWVudCI6eyJtYXRobGliUmV2IjoiMGRmNDQ0YTM2MGVhYTYwYWI4YzExZGNhNTFhODZhZjY5Mjk1NTQ3NCIsInRvb2xjaGFpbiI6ImxlYW5wcm92ZXIvbGVhbjQ6djQuMzMuMSJ9LCJoYXNoIjoiNjBmY2NjMjIwN2Q3ZmU0MzkwMGJmNGZlMzg0MjNiYjgyZmUzZTdlYmY5ZDQ5ZjAwMDQ1YjExMDRmMzVkNDc2ZCIsImtpbmQiOiJkZWZpbml0aW9uIiwibWFya2VyIjoieXVrb24tcHJvb2Ytb3BlcmF0aW9uOmNlcnRpZmljYXRlLXNwbGl0LWFhYzFhMzg2ZjcyMWIzM2RjMDliMTlkMjYxMGI1ZjJhZTZjMTMxZjg3MzliYWVhODAwMDgyMTBiMGI5NzA3MmIiLCJ0YWciOiJiZXR0ZXItY29kZXMiLCJ0YXJnZXQiOiJZdWtvbl81NmMzZWFiOTQ5ZTQ1YzY4ZDliN2Q4NGUiLCJ2IjoyfQ]

import Definitions.Def_Yukon_223642192d853991eed59b0f








































































































































































































































































































































































set_option backward.isDefEq.respectTransparency.types false
namespace ProximityPrize.SubmissionLower.MovingFiberPackingCheck6814
set_option Elab.async false
set_option maxHeartbeats 0

theorem shifted_complete (a : Nat) (xs ys : List Nat)
    (h : ∀ i, i < xs.length → i < ys.length →
      a + (xs[i]?).getD 0 ≤ (ys[i]?).getD 0) : shifted a xs ys = true := by
  induction xs generalizing ys with
  | nil => rfl
  | cons x xs ih =>
    cases ys with
    | nil => rfl
    | cons y ys =>
      simp only [shifted, Bool.and_eq_true, decide_eq_true_eq]
      constructor
      · simpa using h 0 (by simp) (by simp)
      · apply ih
        intro i hi hj
        simpa using h (i+1) (by simpa using hi) (by simpa using hj)

theorem convolution_complete (xs ys zs : List Nat)
    (h : ∀ i j, i < xs.length → j < ys.length → i+j < zs.length →
      (xs[i]?).getD 0 + (ys[j]?).getD 0 ≤ (zs[i+j]?).getD 0) :
    convolution xs ys zs = true := by
  induction xs generalizing zs with
  | nil => rfl
  | cons x xs ih =>
    cases zs with
    | nil => rfl
    | cons z zs =>
      simp only [convolution, Bool.and_eq_true]
      constructor
      · apply shifted_complete
        intro j hj hk
        simpa using h 0 j (by simp) hj (by simpa using hk)
      · apply ih
        intro i j hi hj hk
        simpa [Nat.succ_add] using h (i+1) j (by simpa using hi) hj
          (by simpa [Nat.succ_add] using hk)

theorem monotone_getD_of_shifted (ys : List Nat)
    (h : shifted 0 ys ys.tail = true) (i j : Nat)
    (hij : i ≤ j) (hj : j < ys.length) :
    (ys[i]?).getD 0 ≤ (ys[j]?).getD 0 := by
  induction j with
  | zero =>
    have heq : i = 0 := by omega
    subst i
    rfl
  | succ j ih =>
    by_cases heq : i = j+1
    · subst i; rfl
    · have hprev := ih (by omega) (by omega)
      have hs := shifted_sound 0 ys ys.tail h j (by omega)
        (by simp only [List.length_tail]; omega)
      simp only [Nat.zero_add, List.getElem?_tail] at hs
      exact hprev.trans hs

theorem convolution_zero (n : Nat) (ys : List Nat)
    (h : shifted 0 ys ys.tail = true) :
    convolution (List.replicate n 0) ys ys = true := by
  apply convolution_complete
  intro i j hi hj hk
  have hz : ((List.replicate n 0)[i]?).getD 0 = 0 := by simp
  rw [hz, Nat.zero_add]
  exact monotone_getD_of_shifted ys h j (i+j) (by omega) hk





/-! ## Lane-parallel checks

A list of naturals below `2^64` is packed into one natural with 64-bit lanes (`enc`), so
that `a + ys[j] ≤ zs[j]` for all `j` becomes a few big-number operations the kernel runs
natively: add `2^63` to every lane of `zs`, subtract `a` and `ys` lane by lane (no borrow
crosses a lane when the entries are below `2^62`), and test every lane's top bit with one
`&&&`. A convolution check is one such test per entry of the first list. -/

/-- `2^64`. -/
abbrev W64 : ℕ := 18446744073709551616

/-- Little-endian 64-bit lanes. -/
def enc (l : List ℕ) : ℕ := List.rec (motive := fun _ => ℕ) 0 (fun a _ ih => Nat.add a (Nat.mul W64 ih)) l

@[simp] theorem enc_nil : enc [] = 0 := rfl
@[simp] theorem enc_cons (a : ℕ) (l : List ℕ) : enc (a :: l) = a + W64 * enc l := rfl

/-- Every entry below `b`. -/
def allLt (b : ℕ) (l : List ℕ) : Bool :=
  List.rec (motive := fun _ => Bool) true (fun a _ ih => Bool.rec false ih (Nat.blt a b)) l

theorem allLt_sound (b : ℕ) (l : List ℕ) (h : allLt b l = true) : ∀ a ∈ l, a < b := by
  induction l with
  | nil => simp
  | cons a l ih =>
    change Bool.rec false (allLt b l) (Nat.blt a b) = true at h
    cases hb : Nat.blt a b with
    | false => rw [hb] at h; exact absurd h Bool.false_ne_true
    | true =>
      rw [hb] at h
      intro x hx
      rcases List.mem_cons.mp hx with rfl | hx
      · simpa using hb
      · exact ih h x hx

theorem pow_succ64 (m : ℕ) : 2^(64*(m+1)) = W64 * 2^(64*m) := by
  rw [Nat.mul_succ, Nat.pow_add, Nat.mul_comm]

theorem enc_replicate_mul (m x : ℕ) : x * enc (List.replicate m 1) = enc (List.replicate m x) := by
  induction m with
  | zero => simp
  | succ m ih => simp only [List.replicate_succ, enc_cons]; rw [← ih]; ring

theorem enc_ones (m : ℕ) : (W64 - 1) * enc (List.replicate m 1) = 2^(64*m) - 1 := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [pow_succ64]
    simp only [List.replicate_succ, enc_cons, Nat.mul_add, Nat.mul_one]
    have h1 : 1 ≤ 2^(64*m) := Nat.one_le_two_pow
    rw [Nat.mul_left_comm, ih, Nat.mul_sub, Nat.mul_one]
    have : W64 ≤ W64 * 2^(64*m) := Nat.le_mul_of_pos_right _ h1
    unfold W64 at *
    omega

theorem ones_eq (m : ℕ) : (2^(64*m) - 1) / (W64 - 1) = enc (List.replicate m 1) := by
  rw [← enc_ones, Nat.mul_div_cancel_left _ (by decide)]

theorem lane_mod (a x N : ℕ) (ha : a < W64) (hN : 0 < N) :
    (a + W64 * x) % (W64 * N) = a + W64 * (x % N) := by
  obtain ⟨q, r, hr, rfl⟩ : ∃ q r, r < N ∧ x = N*q + r := ⟨x/N, x%N, Nat.mod_lt _ hN, (Nat.div_add_mod x N).symm⟩
  have e : a + W64 * (N*q + r) = (a + W64 * r) + (W64*N) * q := by ring
  have hm : (N*q + r) % N = r := by rw [Nat.add_comm, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hr]
  rw [e, Nat.add_mul_mod_self_left, hm, Nat.mod_eq_of_lt]
  have : W64 * r + W64 ≤ W64 * N := by rw [← Nat.mul_succ]; exact Nat.mul_le_mul_left _ hr
  omega

theorem enc_mod (l : List ℕ) (h : ∀ a ∈ l, a < W64) (m : ℕ) : enc l % 2^(64*m) = enc (l.take m) := by
  induction l generalizing m with
  | nil => simp
  | cons a l ih =>
    cases m with
    | zero => simp [Nat.mod_one]
    | succ m =>
      have ha := h a (List.mem_cons_self ..)
      have hl := ih (fun x hx => h x (List.mem_cons_of_mem _ hx)) m
      simp only [enc_cons, List.take_succ_cons]
      rw [pow_succ64, lane_mod _ _ _ ha (Nat.two_pow_pos _), hl]

theorem enc_shift (z : ℕ) (l : List ℕ) (hz : z < W64) : enc (z :: l) >>> 64 = enc l := by
  rw [Nat.shiftRight_eq_div_pow, enc_cons]
  change (z + W64 * enc l) / W64 = enc l
  rw [Nat.add_mul_div_left _ _ (by decide), Nat.div_eq_of_lt hz, Nat.zero_add]

/-- The lane test: every lane of `D` has its top bit, given lanes below `2^64`. -/
theorem land_lanes (es : List ℕ) (hes : ∀ e ∈ es, e < W64)
    (h : enc es &&& enc (List.replicate es.length (2^63)) = enc (List.replicate es.length (2^63))) :
    ∀ e ∈ es, 2^63 ≤ e := by
  induction es with
  | nil => simp
  | cons e es ih =>
    have he := hes e (List.mem_cons_self ..)
    have hes' : ∀ x ∈ es, x < W64 := fun x hx => hes x (List.mem_cons_of_mem _ hx)
    simp only [List.length_cons, List.replicate_succ, enc_cons] at h
    -- split the conjunction lane 0 / higher lanes
    have hsplit : (e + W64 * enc es) &&& (2^63 + W64 * enc (List.replicate es.length (2^63))) =
        (e &&& 2^63) + W64 * (enc es &&& enc (List.replicate es.length (2^63))) := by
      apply Nat.eq_of_testBit_eq
      intro j
      have hl1 : e &&& 2^63 < 2^64 := Nat.lt_of_le_of_lt Nat.and_le_left he
      have r1 : ∀ (x b : ℕ), b < 2^64 → (b + W64 * x).testBit j =
          if j < 64 then b.testBit j else x.testBit (j - 64) := by
        intro x b hb
        rw [Nat.add_comm]
        exact Nat.testBit_two_pow_mul_add x hb j
      rw [Nat.testBit_and, r1 _ _ he, r1 _ _ (by decide), r1 _ _ hl1]
      split <;> simp [Nat.testBit_and]
    rw [hsplit] at h
    have hl1 : e &&& 2^63 < W64 := Nat.lt_of_le_of_lt Nat.and_le_left he
    have h63 : (2:ℕ)^63 < W64 := by decide
    -- compare the two base-W64 decompositions
    have hlow : e &&& 2^63 = 2^63 := by
      have := congrArg (· % W64) h
      simp only [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hl1, Nat.mod_eq_of_lt h63] at this
      exact this
    have hhigh : enc es &&& enc (List.replicate es.length (2^63)) = enc (List.replicate es.length (2^63)) := by
      rw [hlow] at h
      exact Nat.eq_of_mul_eq_mul_left (by decide) (Nat.add_left_cancel h)
    intro x hx
    rcases List.mem_cons.mp hx with rfl | hx
    · have hb : x.testBit 63 = true := by
        have h2 : (2^63 : ℕ).testBit 63 = true := Nat.testBit_two_pow_self
        have := congrArg (fun y => y.testBit 63) hlow
        simp only [Nat.testBit_and, h2, Bool.and_true] at this
        exact this
      exact Nat.ge_two_pow_of_testBit hb
    · exact ih hes' hhigh x hx


theorem lanes_identity (a : ℕ) (u w : List ℕ) (h : u.length = w.length)
    (hw : ∀ y ∈ w, a + y ≤ 2^63) :
    enc u + enc (List.replicate u.length (2^63)) =
      enc (List.replicate u.length a) + enc w + enc (List.zipWith (fun z y => z + 2^63 - (a + y)) u w) := by
  induction u generalizing w with
  | nil => cases w <;> simp_all
  | cons z u ih =>
    cases w with
    | nil => simp at h
    | cons y w =>
      simp only [List.length_cons, Nat.add_right_cancel_iff] at h
      have hy := hw y (List.mem_cons_self ..)
      have e := ih w h (fun x hx => hw x (List.mem_cons_of_mem _ hx))
      simp only [List.length_cons, List.replicate_succ, enc_cons, List.zipWith_cons_cons]
      unfold W64 at *
      omega

/-- One row of a convolution check, all lanes at once: with `Y = enc ys`, `Z = enc zs`,
`a + ys[j] ≤ zs[j]` for every `j < min ny nz`. -/
def laneCheck (a yv ny zv nz : ℕ) : Bool :=
  let m := cond (Nat.ble ny nz) ny nz
  let mm := Nat.pow 2 (Nat.mul 64 m)
  let oo := Nat.div (Nat.sub mm 1) (W64 - 1)
  let hh := Nat.mul 9223372036854775808 oo
  Nat.beq (Nat.land (Nat.sub (Nat.add (Nat.mod zv mm) hh) (Nat.add (Nat.mul a oo) (Nat.mod yv mm))) hh) hh

theorem laneCheck_sound (a : ℕ) (ys zs : List ℕ) (ha : a < 2^62) (hys : ∀ y ∈ ys, y < 2^62)
    (hzs : ∀ z ∈ zs, z < 2^63) (h : laneCheck a (enc ys) ys.length (enc zs) zs.length = true) :
    ∀ j, j < ys.length → j < zs.length → a + (ys[j]?).getD 0 ≤ (zs[j]?).getD 0 := by
  intro j hjy hjz
  have hmc : cond (Nat.ble ys.length zs.length) ys.length zs.length = min ys.length zs.length := by
    by_cases hl : ys.length ≤ zs.length
    · rw [Nat.ble_eq_true_of_le hl, min_eq_left hl]; rfl
    · rw [show Nat.ble ys.length zs.length = false from
        Bool.eq_false_iff.mpr (fun hb => hl (Nat.le_of_ble_eq_true hb)), min_eq_right (by omega)]; rfl
  set m := min ys.length zs.length with hm
  have hyL : ∀ y ∈ ys, y < W64 := fun y hy => (hys y hy).trans (by decide)
  have hzL : ∀ z ∈ zs, z < W64 := fun z hz => (hzs z hz).trans (by decide)
  set u := zs.take m
  set w := ys.take m
  have hu : u.length = m := by simp [u, m]
  have hw : w.length = m := by simp [w, m]
  have hZ : enc zs % 2^(64*m) = enc u := enc_mod zs hzL m
  have hY : enc ys % 2^(64*m) = enc w := enc_mod ys hyL m
  have hO : (2^(64*m) - 1) / (W64 - 1) = enc (List.replicate m 1) := ones_eq m
  have hwb : ∀ y ∈ w, a + y ≤ 2^63 := by
    intro y hy
    have := hys y (List.mem_of_mem_take hy)
    have : (2:ℕ)^62 + 2^62 = 2^63 := by decide
    omega
  have hid := lanes_identity a u w (by rw [hu, hw]) hwb
  rw [hu] at hid
  set lanes := List.zipWith (fun z y => z + 2^63 - (a + y)) u w
  have hD : enc u + enc (List.replicate m (2^63)) - (enc (List.replicate m a) + enc w) = enc lanes := by
    omega
  have hlanesLen : lanes.length = m := by simp [lanes, hu, hw]
  have hlanesL : ∀ e ∈ lanes, e < W64 := by
    intro e he
    obtain ⟨k, hk, rfl⟩ := List.mem_iff_getElem.mp he
    have hku : k < u.length := by rw [hu]; omega
    have hkw : k < w.length := by rw [hw]; omega
    have hz := hzs _ (List.mem_of_mem_take (List.getElem_mem hku))
    simp only [lanes, List.getElem_zipWith]
    unfold W64; omega
  dsimp only [laneCheck] at h
  rw [hmc] at h
  have h2 : (enc zs % 2^(64*m) + 9223372036854775808 * ((2^(64*m) - 1) / (W64 - 1)) -
      (a * ((2^(64*m) - 1) / (W64 - 1)) + enc ys % 2^(64*m))) &&& (9223372036854775808 * ((2^(64*m) - 1) / (W64 - 1))) =
      9223372036854775808 * ((2^(64*m) - 1) / (W64 - 1)) := Nat.eq_of_beq_eq_true h
  have hH : 9223372036854775808 * enc (List.replicate m 1) = enc (List.replicate m (2^63)) :=
    enc_replicate_mul m _
  have hA : a * enc (List.replicate m 1) = enc (List.replicate m a) := enc_replicate_mul m a
  rw [hO, hZ, hY, hH, hA, hD, ← hlanesLen] at h2
  have hall := land_lanes lanes hlanesL h2
  have hjm : j < m := by omega
  have hjl : j < lanes.length := by omega
  have he := hall (lanes[j]) (List.getElem_mem hjl)
  have hlj : lanes[j] = u[j]'(by omega) + 2^63 - (a + w[j]'(by omega)) := by
    simp [lanes, List.getElem_zipWith]
  have huj : u[j]'(by omega) = zs[j] := by simp [u, List.getElem_take]
  have hwj : w[j]'(by omega) = ys[j] := by simp [w, List.getElem_take]
  rw [List.getElem?_eq_getElem hjy, List.getElem?_eq_getElem hjz, Option.getD_some, Option.getD_some]
  rw [hlj, huj, hwj] at he
  have := hzs (zs[j]) (List.getElem_mem hjz)
  omega


/-- The rows of a convolution check: row `i` compares `x_i + ys` with `zs` shifted by `i`. -/
def rowsCheck (yv ny : ℕ) (xs : List ℕ) : ℕ → ℕ → Bool :=
  List.rec (motive := fun _ => ℕ → ℕ → Bool) (fun _ _ => true)
    (fun a _ ih zv nz => Bool.rec false (ih (Nat.shiftRight zv 64) (Nat.sub nz 1)) (laneCheck a yv ny zv nz)) xs

theorem rowsCheck_sound (ys : List ℕ) (hys : ∀ y ∈ ys, y < 2^62) (xs : List ℕ) (hxs : ∀ x ∈ xs, x < 2^62)
    (zs : List ℕ) (hzs : ∀ z ∈ zs, z < 2^63)
    (h : rowsCheck (enc ys) ys.length xs (enc zs) zs.length = true) :
    ∀ i j, i < xs.length → j < ys.length → i+j < zs.length →
      (xs[i]?).getD 0 + (ys[j]?).getD 0 ≤ (zs[i+j]?).getD 0 := by
  induction xs generalizing zs with
  | nil => intro i j hi; simp at hi
  | cons a xs ih =>
    change Bool.rec false (rowsCheck (enc ys) ys.length xs (Nat.shiftRight (enc zs) 64) (Nat.sub zs.length 1))
      (laneCheck a (enc ys) ys.length (enc zs) zs.length) = true at h
    cases hb : laneCheck a (enc ys) ys.length (enc zs) zs.length with
    | false => rw [hb] at h; exact absurd h Bool.false_ne_true
    | true =>
      rw [hb] at h
      have ha := hxs a (List.mem_cons_self ..)
      have hrow := laneCheck_sound a ys zs ha hys hzs hb
      intro i j hi hj hij
      cases i with
      | zero => simpa using hrow j hj (by omega)
      | succ i =>
        cases zs with
        | nil => simp at hij
        | cons z zs =>
          have hz : z < W64 := (hzs z (List.mem_cons_self ..)).trans (by decide)
          have hshift : Nat.shiftRight (enc (z :: zs)) 64 = enc zs := enc_shift z zs hz
          rw [hshift, show Nat.sub (z :: zs).length 1 = zs.length by simp] at h
          have := ih (fun x hx => hxs x (List.mem_cons_of_mem _ hx)) zs
            (fun x hx => hzs x (List.mem_cons_of_mem _ hx)) h i j (by simpa using hi) hj
            (by simp at hij; omega)
          simpa [show i + 1 + j = (i + j) + 1 by omega] using this

/-- `convolution` by lane-parallel rows: `O(|xs|)` kernel steps on big numbers instead of
`O(|xs|·|ys|)` comparisons. The entries must lie below `2^62` (`zs` below `2^63`). -/
def convolutionS (xs ys zs : List ℕ) : Bool :=
  Bool.rec false (rowsCheck (enc ys) ys.length xs (enc zs) zs.length)
    (allLt 4611686018427387904 xs && allLt 4611686018427387904 ys && allLt 9223372036854775808 zs)

theorem convolutionS_sound (xs ys zs : List ℕ) (h : convolutionS xs ys zs = true) :
    convolution xs ys zs = true := by
  unfold convolutionS at h
  cases hb : (allLt 4611686018427387904 xs && allLt 4611686018427387904 ys && allLt 9223372036854775808 zs) with
  | false => rw [hb] at h; exact absurd h Bool.false_ne_true
  | true =>
    rw [hb] at h
    simp only [Bool.and_eq_true] at hb
    exact convolution_complete xs ys zs (rowsCheck_sound ys (allLt_sound _ _ hb.1.2) xs
      (allLt_sound _ _ hb.1.1) zs (allLt_sound _ _ hb.2) h)

/-- `shifted` by one lane-parallel row. -/
def shiftedS (a : ℕ) (xs ys : List ℕ) : Bool :=
  Bool.rec false (laneCheck a (enc xs) xs.length (enc ys) ys.length)
    (Nat.blt a 4611686018427387904 && allLt 4611686018427387904 xs && allLt 9223372036854775808 ys)

theorem shiftedS_sound (a : ℕ) (xs ys : List ℕ) (h : shiftedS a xs ys = true) : shifted a xs ys = true := by
  unfold shiftedS at h
  cases hb : (Nat.blt a 4611686018427387904 && allLt 4611686018427387904 xs && allLt 9223372036854775808 ys) with
  | false => rw [hb] at h; exact absurd h Bool.false_ne_true
  | true =>
    rw [hb] at h
    simp only [Bool.and_eq_true, Nat.blt_eq] at hb
    exact shifted_complete a xs ys (laneCheck_sound a xs ys hb.1.1 (allLt_sound _ _ hb.1.2)
      (allLt_sound _ _ hb.2) h)

end ProximityPrize.SubmissionLower.MovingFiberPackingCheck6814


