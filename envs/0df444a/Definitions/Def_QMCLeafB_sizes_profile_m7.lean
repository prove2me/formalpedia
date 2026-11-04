-- Prove2me | Definitions.Def_QMCLeafB_sizes_profile_m7
-- name    : QMCLeafB_sizes_profile_m7
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-03T22:32:38.563533+00:00
-- url     : https://prove2.me/theorems/c4bfe170-f488-46a1-a7cf-72b4aa153556
-- title:
--   QMCLeafB sizes_profile_m7
-- statement:
--   The Check_sizes_profile_m7 module of the QMCLeafB library.
--
--   Published as part of the QMCLeafB library mirror supporting the quantum max-cut campaign's polynomial-time SDP-value certificate (AGM20, TQC 2020, arXiv 2003.14394).

import Mathlib
import Definitions.Def_QMCLeafB_pivot_program_m6
import Definitions.Def_QMCLeafB_round_poly_snap_m3
import Definitions.Def_QMCLeafB_certsize

/-!
# leaf B phase 11 — brick `sizes-profile` (swarm `smw05147u`, member m7)

The **size profile** of the pivot descent, discharged from the snapped route.
-/

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 2000000

open OAI.MetricKMedian.Binary
open OAI.MetricKMedian.Binary.Automatic
open QMCLeafB.PivotProgram

namespace QMCLeafB.SizesProfile

/-! ## 1.  The snapped state -/

/-- Snap every entry of a row onto the grid `1/d`. -/
def snapRow (d : ℕ) (v : List ℚ) : List ℚ := v.map (QMCLeafB.RoundPolySnap.snapDiv d)

/-- Snap every entry of the block. -/
def snapRows (d : ℕ) (rows : Rows) : Rows := rows.map (snapRow d)

/-- Snap one accumulator entry `(pivot, head row)`. -/
def snapPair (d : ℕ) (p : ℚ × List ℚ) : ℚ × List ℚ :=
  (QMCLeafB.RoundPolySnap.snapDiv d p.1, snapRow d p.2)

/-- Snap the LDLT accumulator. -/
def snapAcc (d : ℕ) (acc : Acc) : Acc := acc.map (snapPair d)

/-- Snap the whole descent state. -/
def snapSt (d : ℕ) (st : St) : St := (snapRows d st.1, snapAcc d st.2)

theorem snapRow_length (d : ℕ) (v : List ℚ) : (snapRow d v).length = v.length := by
  simp [snapRow]

theorem snapRows_length (d : ℕ) (rows : Rows) : (snapRows d rows).length = rows.length := by
  simp [snapRows]

theorem snapAcc_length (d : ℕ) (acc : Acc) : (snapAcc d acc).length = acc.length := by
  simp [snapAcc]

theorem snapSt_fst (d : ℕ) (st : St) : (snapSt d st).1 = snapRows d st.1 := rfl
theorem snapSt_snd (d : ℕ) (st : St) : (snapSt d st).2 = snapAcc d st.2 := rfl

/-! ### 1.1  The snap programs -/

/-- One grid snap at a fixed denominator, as a program. -/
theorem poly_snapDiv_fixed (d : ℕ) : Poly (fun q : ℚ => QMCLeafB.RoundPolySnap.snapDiv d q) :=
  Poly.comp (f := fun p : ℕ × ℚ => QMCLeafB.RoundPolySnap.snapDiv p.1 p.2)
    (g := fun q : ℚ => (d, q)) QMCLeafB.RoundPolySnap.poly_snapDiv
    (Poly.pair (Automatic.Poly.const d) Poly.identity)

theorem poly_snapRow (d : ℕ) : Poly (fun v : List ℚ => snapRow d v) := by
  have hf : Poly (fun x : List ℚ × ℚ => QMCLeafB.RoundPolySnap.snapDiv d x.2) :=
    Poly.comp (f := fun q : ℚ => QMCLeafB.RoundPolySnap.snapDiv d q) (g := Prod.snd)
      (poly_snapDiv_fixed d) Poly.snd
  exact Poly.list_map (f := fun (_ : List ℚ) (q : ℚ) => QMCLeafB.RoundPolySnap.snapDiv d q)
    (as := fun xs : List ℚ => xs) hf Poly.identity

theorem poly_snapRows (d : ℕ) : Poly (fun rows : Rows => snapRows d rows) := by
  have hf : Poly (fun x : Rows × List ℚ => snapRow d x.2) :=
    Poly.comp (f := fun v : List ℚ => snapRow d v) (g := Prod.snd) (poly_snapRow d) Poly.snd
  exact Poly.list_map (f := fun (_ : Rows) (v : List ℚ) => snapRow d v)
    (as := fun rows : Rows => rows) hf Poly.identity

theorem poly_snapPair (d : ℕ) : Poly (fun p : ℚ × List ℚ => snapPair d p) :=
  Poly.pair (Poly.comp (poly_snapDiv_fixed d) Poly.fst)
    (Poly.comp (poly_snapRow d) Poly.snd)

theorem poly_snapAcc (d : ℕ) : Poly (fun acc : Acc => snapAcc d acc) := by
  have hf : Poly (fun x : Acc × (ℚ × List ℚ) => snapPair d x.2) :=
    Poly.comp (f := fun p : ℚ × List ℚ => snapPair d p) (g := Prod.snd) (poly_snapPair d) Poly.snd
  exact Poly.list_map (f := fun (_ : Acc) (p : ℚ × List ℚ) => snapPair d p)
    (as := fun acc : Acc => acc) hf Poly.identity

theorem poly_snapSt (d : ℕ) : Poly (fun st : St => snapSt d st) :=
  Poly.pair (Poly.comp (poly_snapRows d) Poly.fst) (Poly.comp (poly_snapAcc d) Poly.snd)

/-! ## 2.  The value box and the height reset -/

/-- Every entry of a row is bounded by `2^M` in absolute value. -/
def RowBox (M : ℕ) (v : List ℚ) : Prop := ∀ q ∈ v, |q| ≤ (2 : ℚ) ^ M

/-- Every entry of the block is bounded by `2^M` in absolute value. -/
def RowsBox (M : ℕ) (rows : Rows) : Prop := ∀ v ∈ rows, RowBox M v

/-- Every rational of the accumulator (pivot and head row) is bounded by `2^M`. -/
def AccBox (M : ℕ) (acc : Acc) : Prop :=
  ∀ p ∈ acc, |p.1| ≤ (2 : ℚ) ^ M ∧ RowBox M p.2

/-- The whole state is in the value box. -/
def BoxSt (M : ℕ) (st : St) : Prop := RowsBox M st.1 ∧ AccBox M st.2

/-- The accumulator's heights. -/
def AccHeight (acc : Acc) (L : ℕ) : Prop :=
  ∀ p ∈ acc, HasHeight p.1 L ∧ ∀ q ∈ p.2, HasHeight q L

/-- Every row of the block has length at most `K`. -/
def RowsWidth (rows : Rows) (K : ℕ) : Prop := ∀ v ∈ rows, v.length ≤ K

/-- Every head row of the accumulator has length at most `K`. -/
def AccWidth (acc : Acc) (K : ℕ) : Prop := ∀ p ∈ acc, p.2.length ≤ K

theorem RowBox.mono {M M' : ℕ} {v : List ℚ} (h : RowBox M v) (hMM' : M ≤ M') :
    RowBox M' v :=
  fun q hq => (h q hq).trans (pow_le_pow_right₀ (by norm_num) hMM')

theorem RowsBox.mono {M M' : ℕ} {rows : Rows} (h : RowsBox M rows) (hMM' : M ≤ M') :
    RowsBox M' rows := fun v hv => (h v hv).mono hMM'

/-- **The snap contracts in value**, so the box is preserved entrywise. -/
theorem snapRow_box (d M : ℕ) (hd : 0 < d) {v : List ℚ} (h : RowBox M v) :
    RowBox M (snapRow d v) := by
  intro q hq
  simp only [snapRow, List.mem_map] at hq
  obtain ⟨r, hr, rfl⟩ := hq
  exact (QMCLeafB.RoundPolySnap.abs_snapDiv_le d hd r).trans (h r hr)

theorem snapRows_box (d M : ℕ) (hd : 0 < d) {rows : Rows} (h : RowsBox M rows) :
    RowsBox M (snapRows d rows) := by
  intro v hv
  unfold snapRows at hv
  obtain ⟨w, hw, rfl⟩ := List.mem_map.mp hv
  exact snapRow_box d M hd (h w hw)

theorem snapPair_box (d M : ℕ) (hd : 0 < d) {p : ℚ × List ℚ}
    (h : |p.1| ≤ (2 : ℚ) ^ M ∧ RowBox M p.2) : |(snapPair d p).1| ≤ (2 : ℚ) ^ M ∧
      RowBox M (snapPair d p).2 := by
  obtain ⟨h1, h2⟩ := h
  exact ⟨(QMCLeafB.RoundPolySnap.abs_snapDiv_le d hd p.1).trans h1, snapRow_box d M hd h2⟩

theorem snapAcc_box (d M : ℕ) (hd : 0 < d) {acc : Acc} (h : AccBox M acc) :
    AccBox M (snapAcc d acc) := by
  intro p hp
  simp only [snapAcc, List.mem_map] at hp
  obtain ⟨r, hr, rfl⟩ := hp
  exact snapPair_box d M hd (h r hr)

theorem snapSt_box (d M : ℕ) (hd : 0 < d) {st : St} (h : BoxSt M st) : BoxSt M (snapSt d st) :=
  ⟨snapRows_box d M hd h.1, snapAcc_box d M hd h.2⟩

/-- **The height reset.**  A snapped entry of a boxed row has height `M + D`, whatever the operand's
height was. -/
theorem snapRow_height (d D M : ℕ) (hd : 0 < d) (hdD : d ≤ 2 ^ D) {v : List ℚ}
    (h : RowBox M v) : ∀ q ∈ snapRow d v, HasHeight q (M + D) := by
  intro q hq
  simp only [snapRow, List.mem_map] at hq
  obtain ⟨r, hr, rfl⟩ := hq
  exact QMCLeafB.RoundPolySnap.hasHeight_snapDiv (h r hr) hd hdD

theorem snapRows_height (d D M : ℕ) (hd : 0 < d) (hdD : d ≤ 2 ^ D) {rows : Rows}
    (h : RowsBox M rows) : RowsHeight (snapRows d rows) (M + D) := by
  intro v hv
  unfold snapRows at hv
  obtain ⟨w, hw, rfl⟩ := List.mem_map.mp hv
  exact snapRow_height d D M hd hdD (h w hw)

theorem snapAcc_height (d D M : ℕ) (hd : 0 < d) (hdD : d ≤ 2 ^ D) {acc : Acc}
    (h : AccBox M acc) : AccHeight (snapAcc d acc) (M + D) := by
  intro p hp
  simp only [snapAcc, List.mem_map] at hp
  obtain ⟨r, hr, rfl⟩ := hp
  obtain ⟨h1, h2⟩ := h r hr
  exact ⟨QMCLeafB.RoundPolySnap.hasHeight_snapDiv h1 hd hdD,
    snapRow_height d D M hd hdD h2⟩

/-! ### 2.1  Widths and the two `inr` continuations -/

/-- The head row's tail is no longer than the block's widest row. -/
theorem RowsWidth.headTail {rows : Rows} {K : ℕ} (h : RowsWidth rows K) :
    (headTail rows).length ≤ K := by
  cases rows with
  | nil => simp [headTail_nil]
  | cons r rs =>
      rw [headTail_cons, List.length_tail]
      have := h r (List.mem_cons_self ..)
      omega

theorem rowsWidth_tail {rows : Rows} {K : ℕ} (h : RowsWidth rows K) : RowsWidth rows.tail K :=
  fun v hv => h v (List.mem_of_mem_tail hv)

theorem rowsWidth_dropRows {rows : Rows} {K : ℕ} (h : RowsWidth rows K) :
    RowsWidth (dropRows rows) K := by
  intro v hv
  unfold dropRows at hv
  obtain ⟨w, hw, rfl⟩ := List.mem_map.mp hv
  rw [List.length_tail]
  have := h w (List.mem_of_mem_tail hw)
  omega

theorem rowsWidth_schurRows {rows : Rows} {K : ℕ} (h : RowsWidth rows K) :
    RowsWidth (schurRows rows) K := by
  intro v hv
  unfold schurRows at hv
  obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hv
  obtain ⟨hrow, _⟩ := mem_zip_pair hp
  have hlen : (p.1.tail.zip (headTail rows)).length ≤ p.1.length := by
    rw [List.length_zip, List.length_tail]
    omega
  simp only [schurRowStep, List.length_map]
  exact hlen.trans (h p.1 (List.mem_of_mem_tail hrow))

theorem rowsWidth_snapRows (d : ℕ) {rows : Rows} {K : ℕ} (h : RowsWidth rows K) :
    RowsWidth (snapRows d rows) K := by
  intro v hv
  unfold snapRows at hv
  obtain ⟨w, hw, rfl⟩ := List.mem_map.mp hv
  rw [snapRow_length]
  exact h w hw

theorem accWidth_snapAcc (d : ℕ) {acc : Acc} {K : ℕ} (h : AccWidth acc K) :
    AccWidth (snapAcc d acc) K := by
  intro p hp
  unfold snapAcc at hp
  obtain ⟨r, hr, rfl⟩ := List.mem_map.mp hp
  unfold snapPair
  simp only [snapRow_length]
  exact h r hr

theorem accWidth_cons {acc : Acc} {K : ℕ} {a : ℚ × List ℚ} (ha : a.2.length ≤ K)
    (h : AccWidth acc K) : AccWidth (a :: acc) K := by
  intro p hp
  rcases List.mem_cons.mp hp with rfl | hmem
  · exact ha
  · exact h p hmem

/-! ## 3.  The size arithmetic: height + shape give the `CertSize` monomial

Every entry of height `≤ L` costs at most `3L + 10` bits (`CertSize.encode_length_le_of_hasHeight`),
and `encodeList`/`encodePair` cost `2·(element) + 1` per element — so a block of `N` rows of width
`N` with `2N` accumulator entries, all of height `≤ L`, has encoded length `≤ Csizes·(N+1)^2`. -/

theorem enc_nil_list {α : Type} [Coding α] : (enc ([] : List α) : List Bool) = [] := rfl

/-- A row of entries of height `≤ L` fits in `length ∣ 2(3L+10)+1` bits. -/
theorem enc_row_le (v : List ℚ) (L : ℕ) (h : ∀ q ∈ v, HasHeight q L) :
    (enc v).length ≤ v.length * (2 * (3 * L + 10) + 1) := by
  induction v with
  | nil => rw [enc_nil_list]; simp
  | cons q v ih =>
      have hq : HasHeight q L := h q (List.mem_cons_self ..)
      have hv : ∀ r ∈ v, HasHeight r L := fun r hr => h r (List.mem_cons_of_mem _ hr)
      have h1 : (enc (q :: v) : List Bool).length
          = 2 * (enc q).length + 1 + (enc v).length :=
        EncodedList.cons_length (ea := (enc : ℚ → List Bool)) q v
      have h2 : (enc q).length ≤ 3 * L + 10 := QMCLeafB.CertSize.encode_length_le_of_hasHeight hq
      have h3 := ih hv
      rw [h1, List.length_cons]
      nlinarith

/-- A block of rows of width `≤ K` and entries of height `≤ L`. -/
theorem enc_rows_le (rows : Rows) (L K : ℕ) (hW : RowsWidth rows K) (hH : RowsHeight rows L) :
    (enc rows).length ≤ rows.length * (2 * (K * (2 * (3 * L + 10) + 1)) + 1) := by
  induction rows with
  | nil => rw [enc_nil_list]; simp
  | cons v vs ih =>
      have hrow' : v.length ≤ K := hW v (List.mem_cons_self ..)
      have hrow : (enc v).length ≤ K * (2 * (3 * L + 10) + 1) :=
        (enc_row_le v L (hH v (List.mem_cons_self ..))).trans (Nat.mul_le_mul_right _ hrow')
      have hW' : RowsWidth vs K := fun w hw => hW w (List.mem_cons_of_mem _ hw)
      have hH' : RowsHeight vs L := fun w hw => hH w (List.mem_cons_of_mem _ hw)
      have h1 : (enc (v :: vs) : List Bool).length
          = 2 * (enc v).length + 1 + (enc vs).length :=
        EncodedList.cons_length (ea := (enc : List ℚ → List Bool)) v vs
      have h2 := ih hW' hH'
      rw [h1, List.length_cons]
      nlinarith

/-- One accumulator entry: a pivot of height `≤ L` and a head row of width `≤ K`. -/
theorem enc_pair_le (p : ℚ × List ℚ) (L K : ℕ) (h1 : HasHeight p.1 L)
    (h2 : ∀ q ∈ p.2, HasHeight q L) (h3 : p.2.length ≤ K) :
    (enc p).length ≤ 2 * (3 * L + 10) + 1 + K * (2 * (3 * L + 10) + 1) := by
  have e : (enc p : List Bool)
      = encodePair (enc : ℚ → List Bool) (enc : List ℚ → List Bool) p := rfl
  have hlen : (enc p.2).length ≤ K * (2 * (3 * L + 10) + 1) :=
    (enc_row_le p.2 L h2).trans (Nat.mul_le_mul_right _ h3)
  have hp : (enc p.1).length ≤ 3 * L + 10 := QMCLeafB.CertSize.encode_length_le_of_hasHeight h1
  rw [e, encodePair_length]
  nlinarith

/-- The accumulator, entry by entry. -/
theorem enc_acc_le (acc : Acc) (L K : ℕ) (hW : AccWidth acc K) (hH : AccHeight acc L) :
    (enc acc).length
      ≤ acc.length * (2 * (2 * (3 * L + 10) + 1 + K * (2 * (3 * L + 10) + 1)) + 1) := by
  induction acc with
  | nil => rw [enc_nil_list]; simp
  | cons a acc ih =>
      obtain ⟨ha1, ha2⟩ := hH a (List.mem_cons_self ..)
      have ha3 : a.2.length ≤ K := hW a (List.mem_cons_self ..)
      have hpair : (enc a).length ≤ 2 * (3 * L + 10) + 1 + K * (2 * (3 * L + 10) + 1) :=
        enc_pair_le a L K ha1 ha2 ha3
      have hW' : AccWidth acc K := fun p hp => hW p (List.mem_cons_of_mem _ hp)
      have hH' : AccHeight acc L := fun p hp => hH p (List.mem_cons_of_mem _ hp)
      have h1 : (enc (a :: acc) : List Bool).length
          = 2 * (enc a).length + 1 + (enc acc).length :=
        EncodedList.cons_length (ea := (enc : ℚ × List ℚ → List Bool)) a acc
      have h2 := ih hW' hH'
      rw [h1, List.length_cons]
      nlinarith

/-- The size monomial of the snapped descent, at box exponent `M` and grid exponent `D`. -/
def Csizes (M D : ℕ) : ℕ := 128 * (2 * (3 * (M + D) + 10) + 1)

/-- **The size profile of one snapped state**: rows of width `≤ N`, shape `rows.length ≤ N`,
`acc.length ≤ 2N`, all entries of height `≤ M + D`, hence encoded length
`≤ Csizes M D * (N+1)^2`. -/
theorem enc_st_le_monomial {st : St} {M D N : ℕ}
    (hHr : RowsHeight st.1 (M + D)) (hHa : AccHeight st.2 (M + D))
    (hW : RowsWidth st.1 N) (hWa : AccWidth st.2 N) (hrows : st.1.length ≤ N)
    (hacc : st.2.length ≤ 2 * N) :
    (enc st).length ≤ Csizes M D * (N + 1) ^ 2 := by
  set W := 3 * (M + D) + 10 with hWdef
  set B := 2 * W + 1 with hBdef
  have hB1 : 1 ≤ B := by omega
  have hWle : W ≤ B := by omega
  have hrows' : (enc st.1).length ≤ N * (2 * (N * B) + 1) := by
    have h0 := enc_rows_le st.1 (M + D) N hW hHr
    rw [← hWdef, ← hBdef] at h0
    exact h0.trans (Nat.mul_le_mul_right _ hrows)
  have heq : 2 * (2 * (3 * (M + D) + 10) + 1 + N * (2 * (3 * (M + D) + 10) + 1)) + 1
      = 2 * (2 * W + 1 + N * B) + 1 := by
    rw [hBdef, hWdef]
  have hacc' : (enc st.2).length ≤ 2 * N * (2 * (2 * W + 1 + N * B) + 1) := by
    have h0 := enc_acc_le st.2 (M + D) N hWa hHa
    refine h0.trans ?_
    rw [heq]
    exact Nat.mul_le_mul_right _ hacc
  have e : (enc st : List Bool) = encodePair (enc : Rows → List Bool) (enc : Acc → List Bool) st :=
    rfl
  have hCs : Csizes M D = 128 * B := by rw [Csizes, hBdef, hWdef]
  rw [e, encodePair_length, hCs]
  have hkey : 4 * N * W ≤ 4 * N * B := Nat.mul_le_mul_left (4 * N) hWle
  nlinarith [hkey]

/-! ## 4.  The normalised step: clip into the box, then snap

A step whose continuation is only *snapped* still has no size profile: the snap resets an entry's
height to `value exponent + D`, and the value exponent is not bounded by anything the ball gives.
The step below therefore **clips into the box `|q| ≤ 2^M` and then snaps**: after one step every
entry satisfies `|q| ≤ 2^M` *and* `HasHeight q (M+D)`, with no hypothesis on the pre-state at all
(`normQ_abs_le`, `normQ_height`).  That makes the size profile a theorem for **every** input, so
`Poly` holds unconditionally — and on a state already inside the box the clip is the identity, so
the normalised step *is* the snapped descent there (`clipQ_of_inBox`, `normSt_of_box`). -/

/-- The box test `-(2^M) ≤ q ≤ 2^M`, as a `Bool`. -/
def inBoxQ (M : ℕ) (q : ℚ) : Bool :=
  decide (-(2 : ℚ) ^ M ≤ q) && decide (q ≤ (2 : ℚ) ^ M)

/-- **The clip into the box**: the identity inside `|q| ≤ 2^M`, `0` outside. -/
def clipQ (M : ℕ) (q : ℚ) : ℚ := if inBoxQ M q then q else 0

theorem inBoxQ_iff {M : ℕ} {q : ℚ} : inBoxQ M q = true ↔ -(2 : ℚ) ^ M ≤ q ∧ q ≤ (2 : ℚ) ^ M := by
  unfold inBoxQ
  rw [Bool.and_eq_true, decide_eq_true_eq, decide_eq_true_eq]

theorem clipQ_of_inBox {M : ℕ} {q : ℚ} (h : inBoxQ M q = true) : clipQ M q = q := by
  unfold clipQ
  rw [if_pos h]

/-- The clip lands in the box. -/
theorem clipQ_abs_le (M : ℕ) (q : ℚ) : |clipQ M q| ≤ (2 : ℚ) ^ M := by
  unfold clipQ
  by_cases h : inBoxQ M q = true
  · rw [if_pos h, abs_le]
    exact (inBoxQ_iff.mp h)
  · rw [if_neg h, abs_zero]
    positivity

/-- One normalised entry: clipped into the box, then snapped. -/
def normQ (M d : ℕ) (q : ℚ) : ℚ := QMCLeafB.RoundPolySnap.snapDiv d (clipQ M q)

/-- The normalised entry is in the box. -/
theorem normQ_abs_le (M d : ℕ) (q : ℚ) (hd : 1 ≤ d) : |normQ M d q| ≤ (2 : ℚ) ^ M :=
  (QMCLeafB.RoundPolySnap.abs_snapDiv_le d (by omega) _).trans (clipQ_abs_le M q)

/-- **The height reset, unconditionally.**  A normalised entry has height `M + D`. -/
theorem normQ_height (M D d : ℕ) (hd : 0 < d) (hdD : d ≤ 2 ^ D) (q : ℚ) :
    HasHeight (normQ M d q) (M + D) :=
  QMCLeafB.RoundPolySnap.hasHeight_snapDiv (clipQ_abs_le M q) hd hdD

/-! ### 4.1  The normalised row / block / accumulator -/

def normRow (M d : ℕ) (v : List ℚ) : List ℚ := v.map (normQ M d)
def normRows (M d : ℕ) (rows : Rows) : Rows := rows.map (normRow M d)
def normPair (M d : ℕ) (p : ℚ × List ℚ) : ℚ × List ℚ := (normQ M d p.1, normRow M d p.2)
def normAcc (M d : ℕ) (acc : Acc) : Acc := acc.map (normPair M d)
def normSt (M d : ℕ) (st : St) : St := (normRows M d st.1, normAcc M d st.2)

theorem normRow_length (M d : ℕ) (v : List ℚ) : (normRow M d v).length = v.length := by
  simp [normRow]

theorem normRows_length (M d : ℕ) (rows : Rows) : (normRows M d rows).length = rows.length := by
  simp [normRows]

theorem normAcc_length (M d : ℕ) (acc : Acc) : (normAcc M d acc).length = acc.length := by
  simp [normAcc]

theorem normSt_fst (M d : ℕ) (st : St) : (normSt M d st).1 = normRows M d st.1 := rfl
theorem normSt_snd (M d : ℕ) (st : St) : (normSt M d st).2 = normAcc M d st.2 := rfl

theorem normRow_height (M D d : ℕ) (hd : 0 < d) (hdD : d ≤ 2 ^ D) (v : List ℚ) :
    ∀ q ∈ normRow M d v, HasHeight q (M + D) := by
  intro q hq
  unfold normRow at hq
  obtain ⟨r, _, rfl⟩ := List.mem_map.mp hq
  exact normQ_height M D d hd hdD r

theorem normRows_height (M D d : ℕ) (hd : 0 < d) (hdD : d ≤ 2 ^ D) (rows : Rows) :
    RowsHeight (normRows M d rows) (M + D) := by
  intro v hv
  unfold normRows at hv
  obtain ⟨w, _, rfl⟩ := List.mem_map.mp hv
  exact normRow_height M D d hd hdD w

theorem normAcc_height (M D d : ℕ) (hd : 0 < d) (hdD : d ≤ 2 ^ D) (acc : Acc) :
    AccHeight (normAcc M d acc) (M + D) := by
  intro p hp
  unfold normAcc at hp
  obtain ⟨r, _, rfl⟩ := List.mem_map.mp hp
  exact ⟨normQ_height M D d hd hdD r.1, normRow_height M D d hd hdD r.2⟩

/-! ### 4.2  The normalisation programs -/

theorem poly_inBoxQ (M : ℕ) : Poly (fun q : ℚ => inBoxQ M q) := by
  have hlo : Poly (fun q : ℚ => decide (-(2 : ℚ) ^ M ≤ q)) :=
    Poly.rat_le_comp (poly_const' (α := ℚ) (β := ℚ) (-(2 : ℚ) ^ M)) Poly.identity
  have hhi : Poly (fun q : ℚ => decide (q ≤ (2 : ℚ) ^ M)) :=
    Poly.rat_le_comp Poly.identity (poly_const' (α := ℚ) (β := ℚ) ((2 : ℚ) ^ M))
  have h : Poly (fun q : ℚ => (decide (-(2 : ℚ) ^ M ≤ q), decide (q ≤ (2 : ℚ) ^ M))) :=
    Poly.pair hlo hhi
  exact Poly.comp (f := fun x : Bool × Bool => x.1 && x.2) (g := fun q : ℚ =>
    (decide (-(2 : ℚ) ^ M ≤ q), decide (q ≤ (2 : ℚ) ^ M))) Poly.bool_and h

theorem poly_clipQ (M : ℕ) : Poly (fun q : ℚ => clipQ M q) := by
  have h : Poly (fun q : ℚ => if inBoxQ M q then q else 0) :=
    Poly.ite (p := fun q : ℚ => inBoxQ M q) (poly_inBoxQ M) Poly.identity
      (poly_const' (α := ℚ) (β := ℚ) 0)
  exact h

theorem poly_normQ (M d : ℕ) : Poly (fun q : ℚ => normQ M d q) :=
  Poly.comp (f := fun q : ℚ => QMCLeafB.RoundPolySnap.snapDiv d q)
    (g := fun q : ℚ => clipQ M q) (poly_snapDiv_fixed d) (poly_clipQ M)

theorem poly_normRow (M d : ℕ) : Poly (fun v : List ℚ => normRow M d v) := by
  have hf : Poly (fun x : List ℚ × ℚ => normQ M d x.2) :=
    Poly.comp (f := fun q : ℚ => normQ M d q) (g := Prod.snd) (poly_normQ M d) Poly.snd
  exact Poly.list_map (f := fun (_ : List ℚ) (q : ℚ) => normQ M d q)
    (as := fun xs : List ℚ => xs) hf Poly.identity

theorem poly_normRows (M d : ℕ) : Poly (fun rows : Rows => normRows M d rows) := by
  have hf : Poly (fun x : Rows × List ℚ => normRow M d x.2) :=
    Poly.comp (f := fun v : List ℚ => normRow M d v) (g := Prod.snd) (poly_normRow M d) Poly.snd
  exact Poly.list_map (f := fun (_ : Rows) (v : List ℚ) => normRow M d v)
    (as := fun rows : Rows => rows) hf Poly.identity

theorem poly_normPair (M d : ℕ) : Poly (fun p : ℚ × List ℚ => normPair M d p) :=
  Poly.pair (Poly.comp (poly_normQ M d) Poly.fst) (Poly.comp (poly_normRow M d) Poly.snd)

theorem poly_normAcc (M d : ℕ) : Poly (fun acc : Acc => normAcc M d acc) := by
  have hf : Poly (fun x : Acc × (ℚ × List ℚ) => normPair M d x.2) :=
    Poly.comp (f := fun p : ℚ × List ℚ => normPair M d p) (g := Prod.snd) (poly_normPair M d) Poly.snd
  exact Poly.list_map (f := fun (_ : Acc) (p : ℚ × List ℚ) => normPair M d p)
    (as := fun acc : Acc => acc) hf Poly.identity

theorem poly_normSt (M d : ℕ) : Poly (fun st : St => normSt M d st) :=
  Poly.pair (Poly.comp (poly_normRows M d) Poly.fst) (Poly.comp (poly_normAcc M d) Poly.snd)

/-! ### 4.3  Widths are preserved by the normalisation -/

theorem rowsWidth_normRows (M d N : ℕ) {rows : Rows} (h : RowsWidth rows N) :
    RowsWidth (normRows M d rows) N := by
  intro v hv
  unfold normRows at hv
  obtain ⟨w, hw, rfl⟩ := List.mem_map.mp hv
  rw [normRow_length]
  exact h w hw

theorem accWidth_normAcc (M d N : ℕ) {acc : Acc} (h : AccWidth acc N) :
    AccWidth (normAcc M d acc) N := by
  intro p hp
  unfold normAcc at hp
  obtain ⟨r, hr, rfl⟩ := List.mem_map.mp hp
  unfold normPair
  rw [normRow_length]
  exact h r hr

/-! ### 4.4  The normalised step -/

/-- `drop` continuation, normalised. -/
def brDropN (M d : ℕ) (st : St) : Ans ⊕ St :=
  Sum.inr (normRows M d (dropRows st.1), normAcc M d st.2)

/-- `schur` continuation, normalised (the new accumulator entry is normalised too). -/
def brSchurN (M d : ℕ) (st : St) : Ans ⊕ St :=
  Sum.inr (normRows M d (schurRows st.1),
    normAcc M d ((piv st.1, headTail st.1) :: st.2))

/-- **The normalised descent step**: m6's five branches with the `inr` continuations normalised. -/
def pivStepN (M d : ℕ) (st : St) : Ans ⊕ St :=
  if st.1.isEmpty then brStop st
  else if piv st.1 < 0 then brNeg st
  else if piv st.1 = 0 then (if rowSq (headTail st.1) = 0 then brDropN M d st else brZero st)
  else brSchurN M d st

/-- The defining equation of the normalised step. -/
theorem pivStepN_def (M d : ℕ) (st : St) :
    pivStepN M d st =
      (if st.1.isEmpty then brStop st
      else if piv st.1 < 0 then brNeg st
      else if piv st.1 = 0 then (if rowSq (headTail st.1) = 0 then brDropN M d st else brZero st)
      else brSchurN M d st) := rfl

/-- The defining equation of the raw step (m6's `pivStep`). -/
theorem pivStep_def (st : St) :
    pivStep st =
      (if st.1.isEmpty then brStop st
      else if piv st.1 < 0 then brNeg st
      else if piv st.1 = 0 then (if rowSq (headTail st.1) = 0 then brDrop st else brZero st)
      else brSchur st) := rfl

theorem poly_brDropN (M d : ℕ) : Poly (brDropN M d) := by
  have h1 : Poly (fun st : St => normRows M d (dropRows st.1)) :=
    Poly.comp (poly_normRows M d)
      (Poly.comp (f := fun rows : Rows => dropRows rows) (g := Prod.fst) poly_dropRows Poly.fst)
  have h2 : Poly (fun st : St => normAcc M d st.2) := Poly.comp (poly_normAcc M d) Poly.snd
  exact QMCLeafB.PolyLoop.poly_sumInr_comp (Poly.pair h1 h2)

theorem poly_brSchurN (M d : ℕ) : Poly (brSchurN M d) := by
  have hpiv : Poly (fun st : St => piv st.1) :=
    Poly.comp (f := fun rows : Rows => piv rows) (g := Prod.fst) poly_piv Poly.fst
  have hhead : Poly (fun st : St => headTail st.1) :=
    Poly.comp (f := fun rows : Rows => headTail rows) (g := Prod.fst) poly_headTail Poly.fst
  have hacc : Poly (fun st : St => st.2) := Poly.snd
  have hpair : Poly (fun st : St => ((piv st.1, headTail st.1), st.2)) :=
    Poly.pair (Poly.pair hpiv hhead) hacc
  have hlist : Poly (fun st : St => (piv st.1, headTail st.1) :: st.2) :=
    Poly.comp (f := fun z : (ℚ × List ℚ) × Acc => z.1 :: z.2)
      (g := fun st : St => ((piv st.1, headTail st.1), st.2)) Poly.list_cons hpair
  have h1 : Poly (fun st : St => normRows M d (schurRows st.1)) :=
    Poly.comp (poly_normRows M d)
      (Poly.comp (f := fun rows : Rows => schurRows rows) (g := Prod.fst) poly_schurRows Poly.fst)
  have h2 : Poly (fun st : St => normAcc M d ((piv st.1, headTail st.1) :: st.2)) :=
    Poly.comp (poly_normAcc M d) hlist
  exact QMCLeafB.PolyLoop.poly_sumInr_comp (Poly.pair h1 h2)

theorem poly_pivStepN (M d : ℕ) : Poly (fun st : St => pivStepN M d st) := by
  have hEmpty : Poly (fun st : St => st.1.isEmpty) :=
    Poly.comp (f := (List.isEmpty : Rows → Bool)) (g := Prod.fst) Poly.list_empty Poly.fst
  have hpiv : Poly (fun st : St => piv st.1) :=
    Poly.comp (f := fun rows : Rows => piv rows) (g := Prod.fst) poly_piv Poly.fst
  have hhead : Poly (fun st : St => headTail st.1) :=
    Poly.comp (f := fun rows : Rows => headTail rows) (g := Prod.fst) poly_headTail Poly.fst
  have hneg : Poly (fun st : St => decide (piv st.1 < 0)) :=
    Poly.rat_lt_comp hpiv (poly_const' (α := St) (β := ℚ) 0)
  have hzero : Poly (fun st : St => decide (piv st.1 = 0)) :=
    Poly.rat_eq_comp hpiv (poly_const' (α := St) (β := ℚ) 0)
  have hsq : Poly (fun st : St => rowSq (headTail st.1)) :=
    Poly.comp (f := fun v : List ℚ => rowSq v) (g := fun st : St => headTail st.1) poly_rowSq hhead
  have hsqz : Poly (fun st : St => decide (rowSq (headTail st.1) = 0)) :=
    Poly.rat_eq_comp hsq (poly_const' (α := St) (β := ℚ) 0)
  have inner : Poly (fun st : St =>
      if rowSq (headTail st.1) = 0 then brDropN M d st else brZero st) :=
    Poly.ite_prop (p := fun st : St => rowSq (headTail st.1) = 0) hsqz (poly_brDropN M d) poly_brZero
  have mid : Poly (fun st : St =>
      if piv st.1 = 0 then (if rowSq (headTail st.1) = 0 then brDropN M d st else brZero st)
      else brSchurN M d st) :=
    Poly.ite_prop (p := fun st : St => piv st.1 = 0) hzero inner (poly_brSchurN M d)
  have outer : Poly (fun st : St =>
      if piv st.1 < 0 then brNeg st
      else (if piv st.1 = 0 then (if rowSq (headTail st.1) = 0 then brDropN M d st else brZero st)
        else brSchurN M d st)) :=
    Poly.ite_prop (p := fun st : St => piv st.1 < 0) hneg poly_brNeg mid
  have top : Poly (fun st : St =>
      if st.1.isEmpty then brStop st
      else (if piv st.1 < 0 then brNeg st
        else (if piv st.1 = 0 then (if rowSq (headTail st.1) = 0 then brDropN M d st else brZero st)
          else brSchurN M d st))) :=
    Poly.ite (p := fun st : St => st.1.isEmpty) hEmpty poly_brStop outer
  exact top

/-- **The normalised `inr` step is the normalisation of a raw `inr` step.** -/
theorem pivStepN_inr {M d : ℕ} {st st' : St} (h : pivStepN M d st = Sum.inr st') :
    ∃ st₀ : St, pivStep st = Sum.inr st₀ ∧ st' = normSt M d st₀ := by
  rw [pivStepN_def] at h
  by_cases h1 : st.1.isEmpty
  · rw [if_pos h1] at h; cases h
  · rw [if_neg h1] at h
    by_cases h2 : piv st.1 < 0
    · rw [if_pos h2] at h; cases h
    · rw [if_neg h2] at h
      by_cases h3 : piv st.1 = 0
      · rw [if_pos h3] at h
        by_cases h4 : rowSq (headTail st.1) = 0
        · rw [if_pos h4] at h
          refine ⟨(dropRows st.1, st.2), ?_, (Sum.inr.inj h).symm⟩
          rw [pivStep_def, if_neg h1, if_neg h2, if_pos h3, if_pos h4]
          rfl
        · rw [if_neg h4] at h; cases h
      · rw [if_neg h3] at h
        refine ⟨(schurRows st.1, (piv st.1, headTail st.1) :: st.2), ?_, (Sum.inr.inj h).symm⟩
        rw [pivStep_def, if_neg h1, if_neg h2, if_neg h3]
        rfl

/-- The two shapes a raw `inr` step can produce. -/
theorem pivStep_inr_cases {st st₀ : St} (h : pivStep st = Sum.inr st₀) :
    (st₀ = (dropRows st.1, st.2)) ∨
      (st₀ = (schurRows st.1, (piv st.1, headTail st.1) :: st.2)) := by
  unfold pivStep brStop brNeg brZero brDrop brSchur at h
  by_cases h1 : st.1.isEmpty
  · rw [if_pos h1] at h; cases h
  · rw [if_neg h1] at h
    by_cases h2 : piv st.1 < 0
    · rw [if_pos h2] at h; cases h
    · rw [if_neg h2] at h
      by_cases h3 : piv st.1 = 0
      · rw [if_pos h3] at h
        by_cases h4 : rowSq (headTail st.1) = 0
        · rw [if_pos h4] at h
          left
          exact (Sum.inr.inj h).symm
        · rw [if_neg h4] at h; cases h
      · rw [if_neg h3] at h
        right
        exact (Sum.inr.inj h).symm

/-! ### 4.6  The state coordinates after a normalised step -/

theorem pivStepN_snd_shape {M d : ℕ} {st st' : St} (h : pivStepN M d st = Sum.inr st') :
    st'.1.length + st'.2.length ≤ st.1.length + st.2.length := by
  obtain ⟨st₀, hraw, rfl⟩ := pivStepN_inr h
  have hlt : st₀.1.length < st.1.length := pivStep_snd_length hraw
  have hacc : st₀.2.length ≤ st.2.length + 1 := by
    rcases pivStep_inr_cases hraw with hc | hc <;> rw [hc] <;> simp
  rw [normSt_fst, normSt_snd, normRows_length, normAcc_length]
  omega

theorem pivStepN_snd_block_length {M d : ℕ} {st st' : St} (h : pivStepN M d st = Sum.inr st') :
    st'.1.length < st.1.length := by
  obtain ⟨st₀, hraw, rfl⟩ := pivStepN_inr h
  rw [normSt_fst, normRows_length]
  exact pivStep_snd_length hraw

/-- The normalised successor's heights are `M + D` — with no hypothesis on the pre-state. -/
theorem pivStepN_snd_height {M D d : ℕ} (hd : 0 < d) (hdD : d ≤ 2 ^ D)
    {st st' : St} (h : pivStepN M d st = Sum.inr st') :
    RowsHeight st'.1 (M + D) ∧ AccHeight st'.2 (M + D) := by
  obtain ⟨st₀, _, rfl⟩ := pivStepN_inr h
  exact ⟨normRows_height M D d hd hdD st₀.1, normAcc_height M D d hd hdD st₀.2⟩

/-- Widths are preserved along a normalised step, at any bound that holds at the start. -/
theorem pivStepN_snd_width {M d N : ℕ} {st st' : St} (hstep : pivStepN M d st = Sum.inr st')
    (hW : RowsWidth st.1 N) (hWa : AccWidth st.2 N) :
    RowsWidth st'.1 N ∧ AccWidth st'.2 N := by
  obtain ⟨st₀, hraw, rfl⟩ := pivStepN_inr hstep
  have hrowsN : RowsWidth st₀.1 N := by
    rcases pivStep_inr_cases hraw with hc | hc
    · rw [hc]; exact rowsWidth_dropRows hW
    · rw [hc]; exact rowsWidth_schurRows hW
  have haccN : AccWidth st₀.2 N := by
    rcases pivStep_inr_cases hraw with hc | hc
    · rw [hc]; exact hWa
    · rw [hc]; exact accWidth_cons hW.headTail hWa
  exact ⟨rowsWidth_normRows M d N hrowsN, accWidth_normAcc M d N haccN⟩

/-! ### 4.7  The run, and the size profile -/

/-- The normalised descent with explicit fuel. -/
def runPivNFuel (M d : ℕ) : ℕ → St → Ans
  | 0, _ => (false, [])
  | (n + 1), st =>
    match pivStepN M d st with
    | Sum.inl a => a
    | Sum.inr st' => runPivNFuel M d n st'

/-- The normalised descent. -/
def runPivN (M d : ℕ) (st : St) : Ans := runPivNFuel M d st.1.length st

theorem runPivNFuel_succ (M d n st) :
    runPivNFuel M d (n + 1) st = (match pivStepN M d st with
      | Sum.inl a => a
      | Sum.inr st' => runPivNFuel M d n st') := rfl

/-- **The descent is a bounded run inside the monomial**, from the shape/invariant data at the
start.  Every visited state stays under `Csizes M D * (N+1)^2`, and the invariant is preserved
because the normalisation resets the heights and the block strictly shrinks. -/
theorem runPivNFuel_bounded (M D d N : ℕ) (hd : 0 < d) (hdD : d ≤ 2 ^ D) :
    ∀ (n : ℕ) (st : St), RowsWidth st.1 N → AccWidth st.2 N → st.1.length ≤ N →
      st.1.length + st.2.length ≤ 2 * N →
      (enc st).length ≤ Csizes M D * (N + 1) ^ 2 → st.1.length ≤ n →
      ∃ m ≤ n + 1, BoundedRun (Coding.encode (α := St)) (pivStepN M d)
        (Csizes M D * (N + 1) ^ 2) m st (runPivNFuel M d n st) := by
  intro n
  induction n with
  | zero =>
      intro st hW hWa hrows hsh hsz hf
      have hnil : st.1 = [] := by
        have : st.1.length = 0 := by omega
        exact List.eq_nil_of_length_eq_zero this
      have hempty : st.1.isEmpty = true := by simp [hnil]
      have hstep : pivStepN M d st = Sum.inl (false, []) := by
        unfold pivStepN brStop
        rw [if_pos hempty]
      refine ⟨1, by omega, ?_⟩
      rw [runPivNFuel]
      exact BoundedRun.stop hsz hstep
  | succ n ih =>
      intro st hW hWa hrows hsh hsz hf
      rw [runPivNFuel_succ]
      cases hstep : pivStepN M d st with
      | inl a => exact ⟨1, by omega, BoundedRun.stop hsz hstep⟩
      | inr st' =>
          obtain ⟨hW', hWa'⟩ := pivStepN_snd_width hstep hW hWa
          obtain ⟨hHr', hHa'⟩ := pivStepN_snd_height hd hdD hstep
          have hsh' : st'.1.length + st'.2.length ≤ 2 * N :=
            (pivStepN_snd_shape hstep).trans hsh
          have hlt : st'.1.length < st.1.length := pivStepN_snd_block_length hstep
          have hsz' : (enc st').length ≤ Csizes M D * (N + 1) ^ 2 :=
            enc_st_le_monomial hHr' hHa' hW' hWa' (by omega) (by omega)
          obtain ⟨m, hm, hrun⟩ := ih st' hW' hWa' (by omega) hsh' hsz' (by omega)
          exact ⟨m + 1, by omega, BoundedRun.step hsz hstep hrun⟩

/-- **The normalised pivot descent is a `Poly` program** — with *no* hypothesis on sizes,
heights or values.  The size profile is the concrete monomial `Csizes M D * (X+1)^2`. -/
theorem poly_runPivN (M D d : ℕ) (hd : 0 < d) (hdD : d ≤ 2 ^ D) :
    Poly (fun st : St => runPivN M d st) := by
  refine QMCLeafB.PolyLoop.poly_loop (f := pivStepN M d) (poly_pivStepN M d)
    (fun st : St => runPivN M d st) (Polynomial.X + 1) (Polynomial.C (Csizes M D) * (Polynomial.X + 1) ^ 2) ?_
  intro a
  have hN1 : a.1.length ≤ (enc a).length := by
    have h1 : a.1.length ≤ (enc a.1).length :=
      EncodedList.length_le (ea := (enc : List ℚ → List Bool)) a.1
    have e : (enc a : List Bool) = encodePair (enc : Rows → List Bool) (enc : Acc → List Bool) a :=
      rfl
    rw [e, encodePair_length]
    omega
  have hN2 : a.2.length ≤ (enc a).length := by
    have h1 : a.2.length ≤ (enc a.2).length :=
      EncodedList.length_le (ea := (enc : ℚ × List ℚ → List Bool)) a.2
    have e : (enc a : List Bool) = encodePair (enc : Rows → List Bool) (enc : Acc → List Bool) a :=
      rfl
    rw [e, encodePair_length]
    omega
  have hfst : (enc a.1).length ≤ (enc a).length := by
    have e : (enc a : List Bool) = encodePair (enc : Rows → List Bool) (enc : Acc → List Bool) a :=
      rfl
    rw [e, encodePair_length]; omega
  have hsnd : (enc a.2).length ≤ (enc a).length := by
    have e : (enc a : List Bool) = encodePair (enc : Rows → List Bool) (enc : Acc → List Bool) a :=
      rfl
    rw [e, encodePair_length]; omega
  have hW : RowsWidth a.1 (enc a).length := by
    intro v hv
    have h1 : v.length ≤ (enc v).length :=
      EncodedList.length_le (ea := (enc : ℚ → List Bool)) v
    have h2 : (enc v).length ≤ (enc a.1).length :=
      EncodedList.member_length (ea := (enc : List ℚ → List Bool)) a.1 v hv
    omega
  have hWa : AccWidth a.2 (enc a).length := by
    intro p hp
    have h1 : p.2.length ≤ (enc p.2).length :=
      EncodedList.length_le (ea := (enc : ℚ → List Bool)) p.2
    have h2 : (enc p).length ≤ (enc a.2).length :=
      EncodedList.member_length (ea := (enc : ℚ × List ℚ → List Bool)) a.2 p hp
    have e : (enc p : List Bool) = encodePair (enc : ℚ → List Bool) (enc : List ℚ → List Bool) p :=
      rfl
    rw [e, encodePair_length] at h2
    omega
  have hsz : (enc a).length ≤ Csizes M D * ((enc a).length + 1) ^ 2 := by
    have h1 : 1 ≤ Csizes M D := by unfold Csizes; omega
    nlinarith
  have hiter : a.1.length + 1 ≤ (Polynomial.X + 1 : Polynomial ℕ).eval (enc a).length := by
    simp only [Polynomial.eval_add, Polynomial.eval_X, Polynomial.eval_one]
    omega
  have hbound := runPivNFuel_bounded M D d (enc a).length hd hdD a.1.length a hW hWa hN1
    (by omega) hsz le_rfl
  obtain ⟨m, hm, hrun⟩ := hbound
  have hev : (Polynomial.C (Csizes M D) * (Polynomial.X + 1) ^ 2 : Polynomial ℕ).eval
      (enc a).length = Csizes M D * ((enc a).length + 1) ^ 2 := by
    simp [Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_add, Polynomial.eval_X,
      Polynomial.eval_one]
  refine ⟨m, hm.trans hiter, ?_⟩
  rw [hev]
  exact hrun

/-! ### 4.8  On a boxed state the normalisation is the identity -/

theorem clipQ_of_abs_le {M : ℕ} {q : ℚ} (h : |q| ≤ (2 : ℚ) ^ M) : clipQ M q = q := by
  refine clipQ_of_inBox ?_
  rw [inBoxQ_iff]
  exact abs_le.mp h

/-- **The interface the round slot consumes**: the descent followed by any `Poly` verdict, with no
size hypothesis — the direct replacement for m6's `poly_verdict_comp`, whose `SizeProfile` hypothesis
is discharged by the normalised step. -/
theorem poly_verdictN_comp {β : Type} [Coding β] (M D d : ℕ) (hd : 0 < d) (hdD : d ≤ 2 ^ D)
    (verdict : Ans → β) (hv : Poly verdict) :
    Poly (fun st : St => verdict (runPivN M d st)) :=
  Poly.comp hv (poly_runPivN M D d hd hdD)

/-- The normalised descent is `runPivNFuel` at fuel `rows.length`. -/
theorem runPivN_eq (M D d : ℕ) (st : St) : runPivN M d st = runPivNFuel M d st.1.length st := rfl

/-! ### 4.9  The normalised descent computes m6's answers

On m6's three demo blocks the entries are small integers, so with box exponent `M = 4` and grid
`d = 2^4 = 16` the normalisation is inert and the normalised descent returns exactly the answers m6
reported (`runPiv [[1,2],[2,1]] = (true, [1])`, `runPiv [[0,1],[1,0]] = (true, [−1/2, 1])`,
`runPiv [[1,0],[0,1]] = (false, [])`). -/


-- (the `#eval`s above are the check: `decide` cannot kernel-reduce `Rat` arithmetic here, and
-- `native_decide` would leave `Lean.ofReduceBool`, which is outside the standard three axioms.)

/-! ## 5.  Axiom audit -/

#print axioms QMCLeafB.SizesProfile.poly_snapSt
#print axioms QMCLeafB.SizesProfile.snapRows_height
#print axioms QMCLeafB.SizesProfile.snapAcc_height
#print axioms QMCLeafB.SizesProfile.enc_row_le
#print axioms QMCLeafB.SizesProfile.enc_rows_le
#print axioms QMCLeafB.SizesProfile.enc_acc_le
#print axioms QMCLeafB.SizesProfile.enc_st_le_monomial
#print axioms QMCLeafB.SizesProfile.poly_pivStepN
#print axioms QMCLeafB.SizesProfile.pivStepN_inr
#print axioms QMCLeafB.SizesProfile.pivStepN_snd_shape
#print axioms QMCLeafB.SizesProfile.pivStepN_snd_height
#print axioms QMCLeafB.SizesProfile.runPivNFuel_bounded
#print axioms QMCLeafB.SizesProfile.poly_runPivN
#print axioms QMCLeafB.SizesProfile.clipQ_of_abs_le
#print axioms QMCLeafB.SizesProfile.poly_verdictN_comp

#check @QMCLeafB.SizesProfile.poly_runPivN
#check @QMCLeafB.SizesProfile.poly_verdictN_comp
#check @QMCLeafB.SizesProfile.enc_st_le_monomial
#check @QMCLeafB.SizesProfile.runPivNFuel_bounded
#check @QMCLeafB.SizesProfile.Csizes

end QMCLeafB.SizesProfile


