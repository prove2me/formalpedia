-- Prove2me | Definitions.Def_QMCLeafB_roundsize_m6
-- name    : QMCLeafB_roundsize_m6
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-04T00:22:51.41585+00:00
-- url     : https://prove2.me/theorems/e49f3e7f-3557-41d5-a8cd-f8c39e8d0f19
-- title:
--   QMCLeafB roundsize_m6
-- statement:
--   # leaf B phase 14 — brick `round-size` (swarm `smw1a99tp`, member m6, direction d5, part 2)
--
--   Published as part of the QMCLeafB library mirror supporting the quantum max-cut campaign's polynomial-time SDP-value certificate (AGM20, TQC 2020, arXiv 2003.14394).

import Mathlib
import Definitions.Def_QMCLeafB_integration_m6
import Definitions.Def_QMCLeafB_round_program_m3
/-
# leaf B phase 14 — brick `round-size` (swarm `smw1a99tp`, member m6, direction d5, part 2)

The **round-size ledger** for m3's `RoundProgram.round`, in the shape m6's
`Check_integration_m6.lean` consumes (`IntegrateM6.endgame_RSt_ledger`'s `hMinv`, `hstep`, `hM`).

The design (see `.ultramath/smw1a99tp/m6/round-ledger-plan.md`) is the **max form**: since every
round appends one `ok` flag, the loop state's own encoding grows linearly in the round index, and the
declining term is the fuel tail.  So the ledger proves, for a cap `M` that is *frozen* except for the
flag list,

    (enc (round s)).length ≤ max ((enc s).length + 6) (M s),        M (round s) ≤ M s + 6

which is exactly what `IntegrateM6.iterate_length_le` / `orbit_envelope` turn into the closing
stroke's orbit envelope.

§1 height arithmetic for lists of rationals (`HasHeight`-based, via the library's
`HasHeight.foldAdd`/`foldMul`, which bound a fold by the *encoded length* of the list).
§2 the witnesses of the pivot descent (`negWitness`, `zeroWitness`) have bounded height.
§3 the descent's answer (`runPivL`) has bounded height, by induction on the fuel.
§4 the oracle's output (`oracleR`) has bounded encoded length.
§5 the `X`-side cap and the assembled `M`, `hMinv`, `hstep`, `hM`.

No `sorry`, no `axiom`.  Audit at the end.
-/

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option linter.unusedVariables false

open scoped BigOperators
open OAI.MetricKMedian.Binary
open OAI.MetricKMedian.Binary.Automatic

namespace QMCLeafB.RoundSizeM6

open QMCLeafB.PivotProgram
open QMCLeafB.SizesProfile
open QMCLeafB.RoundProgram

/-! ## 1.  Height arithmetic for lists of rationals -/

/-- Membership in a `zip`, in the form needed for height bounds. -/
theorem forall_mem_zip {α β : Type} {p : α × β → Prop} (x : List α) :
    ∀ (y : List β), (∀ a ∈ x, ∀ b ∈ y, p (a, b)) → ∀ c ∈ x.zip y, p c := by
  induction x with
  | nil =>
    intro y _ c hc
    simp at hc
  | cons a as ih =>
    intro y h c hc
    cases y with
    | nil => simp at hc
    | cons b bs =>
      rw [List.zip_cons_cons] at hc
      rcases List.mem_cons.mp hc with rfl | hc'
      · exact h a (by simp) b (by simp)
      · exact ih bs (fun a' ha' b' hb' =>
          h a' (List.mem_cons_of_mem _ ha') b' (by simp [hb'])) c hc'

/-- A `zip` is no longer than its first argument. -/
theorem zip_length_le {α β : Type} : ∀ (x : List α) (y : List β), (x.zip y).length ≤ x.length := by
  intro x
  induction x with
  | nil => intro y; simp
  | cons a as ih =>
    intro y
    cases y with
    | nil => simp
    | cons b bs => simpa using ih bs

/-- A list of height-`H` rationals costs at most `6H+21` bits per entry (each entry is quoted once
more inside `encodeList`). -/
theorem encodeList_length_le (l : List ℚ) (H : ℕ) (h : ∀ q ∈ l, HasHeight q H) :
    (encodeList (enc : ℚ → List Bool) l).length ≤ l.length * (6 * H + 21) := by
  induction l with
  | nil =>
    rw [EncodedList.nil]
    simp
  | cons a as ih =>
    rw [EncodedList.cons_length, List.length_cons]
    have ha : (enc a : List Bool).length ≤ 3 * H + 10 := Ratio.length_height (h a (by simp))
    have hs : (encodeList (enc : ℚ → List Bool) as).length ≤ as.length * (6 * H + 21) :=
      ih (fun q hq => h q (List.mem_cons_of_mem a hq))
    nlinarith

/-- A sum of height-`H` rationals has height at most the encoded length of the list. -/
theorem listSum_height (l : List ℚ) :
    HasHeight l.sum ((encodeList (enc : ℚ → List Bool) l).length) := by
  have h := HasHeight.foldAdd l 0 0 (HasHeight.zero 0)
  rw [ListAlgorithms.foldAdd, zero_add, zero_add] at h
  exact h

/-- A product of height-`H` rationals has height at most the encoded length of the list. -/
theorem listProd_height (l : List ℚ) :
    HasHeight l.prod ((encodeList (enc : ℚ → List Bool) l).length) := by
  have h := HasHeight.foldMul l 1 0 (HasHeight.one 0)
  rw [ListAlgorithms.foldMul, one_mul, zero_add] at h
  exact h

/-- **`rowSq`**: a sum of squares of height-`H` entries. -/
theorem rowSq_height {v : List ℚ} {H : ℕ} (h : ∀ q ∈ v, HasHeight q H) :
    HasHeight (rowSq v) (v.length * (6 * (2 * H) + 21)) := by
  have hsq : ∀ q ∈ v.map (fun q : ℚ => q * q), HasHeight q (2 * H) := by
    intro q hq
    obtain ⟨r, hr, rfl⟩ := List.mem_map.mp hq
    have hm := (h r hr).mul (h r hr)
    simpa [two_mul] using hm
  have hsum := listSum_height (v.map (fun q : ℚ => q * q))
  have hlen : (encodeList (enc : ℚ → List Bool) (v.map (fun q : ℚ => q * q))).length
      ≤ v.length * (6 * (2 * H) + 21) := by
    have := encodeList_length_le (v.map (fun q : ℚ => q * q)) (2 * H) hsq
    simpa using this
  have hmain : HasHeight (rowSq v)
      ((encodeList (enc : ℚ → List Bool) (v.map (fun q : ℚ => q * q))).length) := by
    simpa [rowSq, List.sum] using hsum
  exact hmain.mono hlen

/-- **`dotL`**: a sum of pairwise products. -/
theorem dotL_height {x y : List ℚ} {H : ℕ}
    (hx : ∀ q ∈ x, HasHeight q H) (hy : ∀ q ∈ y, HasHeight q H) :
    HasHeight (dotL x y) (x.length * (6 * (2 * H) + 21)) := by
  have hprod : ∀ q ∈ (x.zip y).map (fun p : ℚ × ℚ => p.1 * p.2), HasHeight q (2 * H) := by
    intro q hq
    obtain ⟨r, hr, rfl⟩ := List.mem_map.mp hq
    have hm : HasHeight (r.1 * r.2) (H + H) :=
      forall_mem_zip (p := fun c : ℚ × ℚ => HasHeight (c.1 * c.2) (H + H)) x y
        (fun a ha b hb => (hx a ha).mul (hy b hb)) r hr
    simpa [two_mul] using hm
  have hsum := listSum_height ((x.zip y).map (fun p : ℚ × ℚ => p.1 * p.2))
  have hlen : (encodeList (enc : ℚ → List Bool)
      ((x.zip y).map (fun p : ℚ × ℚ => p.1 * p.2))).length
      ≤ x.length * (6 * (2 * H) + 21) := by
    have h1 := encodeList_length_le ((x.zip y).map (fun p : ℚ × ℚ => p.1 * p.2)) (2 * H) hprod
    have h2' : ((x.zip y).map (fun p : ℚ × ℚ => p.1 * p.2)).length ≤ x.length := by
      rw [List.length_map]
      exact zip_length_le x y
    have h3 := Nat.mul_le_mul_right (6 * (2 * H) + 21) h2'
    exact le_trans h1 h3
  have hmain : HasHeight (dotL x y)
      ((encodeList (enc : ℚ → List Bool) ((x.zip y).map (fun p : ℚ × ℚ => p.1 * p.2))).length) := by
    simpa [dotL, List.sum] using hsum
  exact hmain.mono hlen

/-! ## 2.  The witnesses of the pivot descent

`negWitness rows = 1 :: rows.tail.map (fun _ => 0)` (entries `0, 1`) and
`zeroWitness rows = (-(qformRows (dropRows rows) (headTail rows) + 1) / (2*rowSq (headTail rows)))
:: headTail rows`.  Both stay at a height that is an explicit polynomial in the entry height `H` and
the row width / row count `N`. -/

/-- The height of `qformRows` at entry height `H` and width `N`. -/
def qfH (H N : ℕ) : ℕ := N * (6 * (H + N * (6 * (2 * H) + 21)) + 21)

/-- The height bound for the witnesses at entry height `H` and width `N`. -/
def kapH (H N : ℕ) : ℕ := qfH H N + N * (6 * (2 * H) + 21) + 2 + H

theorem hasHeight_two : HasHeight (2 : ℚ) 1 := by
  constructor <;> norm_num [HasHeight]

theorem mem_zip_fst {α β : Type} {x : List α} {y : List β} {c : α × β} (h : c ∈ x.zip y) :
    c.1 ∈ x :=
  forall_mem_zip (p := fun z : α × β => z.1 ∈ x) x y (fun a ha _ _ => ha) c h

theorem mem_zip_snd {α β : Type} {x : List α} {y : List β} {c : α × β} (h : c ∈ x.zip y) :
    c.2 ∈ y :=
  forall_mem_zip (p := fun z : α × β => z.2 ∈ y) x y (fun _ _ b hb => hb) c h

/-- **`qformRows`**: a sum over the rows of `bᵢ · (rowᵢ ⬝ b)`. -/
theorem qformRows_height {rows : Rows} {b : List ℚ} {H N : ℕ}
    (hr : RowsHeight rows H) (hb : ∀ q ∈ b, HasHeight q H)
    (hRn : rows.length ≤ N) (hWr : RowsWidth rows N) (hWb : b.length ≤ N) :
    HasHeight (qformRows rows b) (qfH H N) := by
  set Kl : ℕ := N * (6 * (2 * H) + 21) with hKl
  have hmem : ∀ c ∈ rows.zip b, c.1 ∈ rows ∧ c.2 ∈ b :=
    fun c hc => ⟨mem_zip_fst hc, mem_zip_snd hc⟩
  have hterm : ∀ c ∈ (rows.zip b).map (fun p : List ℚ × ℚ => p.2 * dotL p.1 b),
      HasHeight c (H + Kl) := by
    intro c hc
    obtain ⟨r, hr', rfl⟩ := List.mem_map.mp hc
    obtain ⟨hr1, hr2⟩ := hmem r hr'
    have h1 : HasHeight r.2 H := hb r.2 hr2
    have h2 : HasHeight (dotL r.1 b) Kl := by
      have hd := dotL_height (x := r.1) (y := b) (H := H)
        (fun q hq => hr r.1 hr1 q hq) hb
      have hlen : r.1.length ≤ N := hWr r.1 hr1
      exact hd.mono (Nat.mul_le_mul_right _ hlen)
    exact h1.mul h2
  have hsum := listSum_height ((rows.zip b).map (fun p : List ℚ × ℚ => p.2 * dotL p.1 b))
  have hlen : (encodeList (enc : ℚ → List Bool)
      ((rows.zip b).map (fun p : List ℚ × ℚ => p.2 * dotL p.1 b))).length
      ≤ N * (6 * (H + Kl) + 21) := by
    have h1 := encodeList_length_le _ _ hterm
    have h2 : ((rows.zip b).map (fun p : List ℚ × ℚ => p.2 * dotL p.1 b)).length ≤ N := by
      rw [List.length_map]
      exact le_trans (zip_length_le rows b) hRn
    exact le_trans h1 (Nat.mul_le_mul_right _ h2)
  have hmain : HasHeight (qformRows rows b)
      ((encodeList (enc : ℚ → List Bool)
        ((rows.zip b).map (fun p : List ℚ × ℚ => p.2 * dotL p.1 b))).length) := by
    simpa [qformRows, List.sum] using hsum
  exact hmain.mono hlen

/-- **`zeroWitness`** at entry height `H`, width / row count `N`. -/
theorem zeroWitness_height {rows : Rows} {H N : ℕ} (hr : RowsHeight rows H)
    (hRn : rows.length ≤ N) (hWr : RowsWidth rows N) :
    ∀ q ∈ zeroWitness rows, HasHeight q (kapH H N) := by
  set Kl : ℕ := N * (6 * (2 * H) + 21) with hKl
  set Kq : ℕ := qfH H N with hKq
  have htail : ∀ q ∈ headTail rows, HasHeight q H := fun q hq => hr.headTail q hq
  have htailN : (headTail rows).length ≤ N := by
    cases rows with
    | nil =>
      rw [headTail_nil]
      simp
    | cons r rs =>
      rw [headTail_cons, List.length_tail]
      have h2 : r.length ≤ N := hWr r (by simp)
      omega
  have hdrop : RowsHeight (dropRows rows) H := fun v hv q hq => by
    obtain ⟨r, hr', rfl⟩ := List.mem_map.mp hv
    exact hr r (List.mem_of_mem_tail hr') q (List.mem_of_mem_tail hq)
  have hlen_drop : (dropRows rows).length ≤ N := by
    rw [dropRows, List.length_map, List.length_tail]
    have h2 : rows.length ≤ N := hRn
    omega
  have hWdrop : RowsWidth (dropRows rows) N := by
    intro v hv
    obtain ⟨r, hr', rfl⟩ := List.mem_map.mp hv
    rw [List.length_tail]
    have h2 : r.length ≤ N := hWr r (List.mem_of_mem_tail hr')
    omega
  have hqf : HasHeight (qformRows (dropRows rows) (headTail rows)) Kq :=
    qformRows_height hdrop htail hlen_drop hWdrop htailN
  have hrowSq : HasHeight (rowSq (headTail rows)) Kl := by
    have hs := rowSq_height (v := headTail rows) (H := H) htail
    exact hs.mono (Nat.mul_le_mul_right _ htailN)
  have hnum : HasHeight (-(qformRows (dropRows rows) (headTail rows) + 1)) (Kq + 1) := by
    have hadd : HasHeight (qformRows (dropRows rows) (headTail rows) + 1) (Kq + 0 + 1) :=
      hqf.add (HasHeight.one 0)
    exact hadd.neg
  have hden : HasHeight (2 * rowSq (headTail rows)) (1 + Kl) :=
    hasHeight_two.mul hrowSq
  have head : HasHeight (-(qformRows (dropRows rows) (headTail rows) + 1)
      / (2 * rowSq (headTail rows))) ((Kq + 1) + (1 + Kl)) := hnum.div hden
  intro q hq
  rw [zeroWitness] at hq
  rcases List.mem_cons.mp hq with rfl | hq'
  · exact head.mono (by rw [kapH, hKq, hKl]; omega)
  · exact (htail q hq').mono (by rw [kapH]; omega)

/-- **`negWitness`** at entry height `H`. -/
theorem negWitness_height {rows : Rows} {H N : ℕ} :
    ∀ q ∈ negWitness rows, HasHeight q (kapH H N) := by
  intro q hq
  rw [negWitness] at hq
  rcases List.mem_cons.mp hq with rfl | hq'
  · exact (HasHeight.one 1).mono (by simp [kapH]; omega)
  · obtain ⟨c, hc, rfl⟩ := List.mem_map.mp hq'
    exact (HasHeight.zero 0).mono (by rw [kapH]; omega)

/-! ## 3.  The descent's answer has bounded height -/

/-- **The answer of one descent step** at entry height `H`, width / row count `N`. -/
theorem pivStepL_inl_height {p : LSt} {a : Ans} {H N : ℕ}
    (hr : RowsHeight p.2.1 H) (hWr : RowsWidth p.2.1 N) (hRn : p.2.1.length ≤ N)
    (h : pivStepL p = Sum.inl a) :
    ∀ q ∈ a.2, HasHeight q (kapH H N) := by
  rw [pivStepL_def] at h
  by_cases h1 : p.2.1.isEmpty
  · rw [if_pos h1] at h
    cases h
    simp
  · rw [if_neg h1] at h
    by_cases h2 : piv p.2.1 < 0
    · rw [if_pos h2] at h
      cases h
      exact negWitness_height
    · rw [if_neg h2] at h
      by_cases h3 : piv p.2.1 = 0
      · rw [if_pos h3] at h
        by_cases h4 : rowSq (headTail p.2.1) = 0
        · rw [if_pos h4] at h
          cases h
        · rw [if_neg h4] at h
          cases h
          exact zeroWitness_height hr hRn hWr
      · rw [if_neg h3] at h
        cases h

/-- **The descent's answer**, by induction on the fuel: the state stays at entry height `K0` (each
step re-normalises into the `mu`-box / `d`-grid, which is height `L + D ≤ K0`) and width `N`, so the
witness produced at any step is at height `kapH K0 N`. -/
theorem runPivLFuel_ans_height {mu : ℚ} {d L D N K0 : ℕ} (hmu : HasHeight mu L)
    (hdD : d ≤ 2 ^ D) (hK0 : L + D ≤ K0) :
    ∀ (k : ℕ) (p : LSt), p.1 = (mu, d) →
      RowsHeight p.2.1 K0 → AccHeight p.2.2 K0 →
      RowsWidth p.2.1 N → AccWidth p.2.2 N → p.2.1.length ≤ N →
      ∀ q ∈ (runPivLFuel k p).2, HasHeight q (kapH K0 N) := by
  intro k
  induction k with
  | zero =>
    intro p _ _ _ _ _ _ q hq
    simp [runPivLFuel] at hq
  | succ k ih =>
    intro p hp hrh hah hWr hWa hRn q hq
    rcases hstep : pivStepL p with a | p'
    · rw [runPivLFuel_succ, hstep] at hq
      exact pivStepL_inl_height hrh hWr hRn hstep q hq
    · rw [runPivLFuel_succ, hstep] at hq
      have hp' : p'.1 = (mu, d) := by rw [pivStepL_snd_fst hstep, hp]
      have hmu' : HasHeight p.1.1 L := by rw [hp]; exact hmu
      have hdD' : p.1.2 ≤ 2 ^ D := by rw [hp]; exact hdD
      have hrh' : RowsHeight p'.2.1 K0 := by
        have := (pivStepL_snd_height hmu' hdD' hstep).1
        exact this.mono hK0
      have hah' : AccHeight p'.2.2 K0 := by
        intro z hz
        have h1 := (pivStepL_snd_height hmu' hdD' hstep).2 z hz
        exact ⟨h1.1.mono hK0, fun c hc => (h1.2 c hc).mono hK0⟩
      have hWr' : RowsWidth p'.2.1 N := (pivStepL_snd_width hstep hWr hWa).1
      have hWa' : AccWidth p'.2.2 N := (pivStepL_snd_width hstep hWr hWa).2
      have hRn' : p'.2.1.length ≤ N :=
        le_trans (Nat.le_of_lt (pivStepL_snd_block_length hstep)) hRn
      exact ih p' hp' hrh' hah' hWr' hWa' hRn' q hq

/-- **The answer of `runPivL`** (the state-dependent descent). -/
theorem runPivL_ans_height {mu : ℚ} {d L D N K0 : ℕ} (hmu : HasHeight mu L)
    (hdD : d ≤ 2 ^ D) (hK0 : L + D ≤ K0) {rows : Rows} {acc : Acc}
    (hr : RowsHeight rows K0) (ha : AccHeight acc K0)
    (hWr : RowsWidth rows N) (hWa : AccWidth acc N) (hRn : rows.length ≤ N) :
    ∀ q ∈ (runPivL ((mu, d), (rows, acc))).2, HasHeight q (kapH K0 N) :=
  runPivLFuel_ans_height hmu hdD hK0 rows.length ((mu, d), (rows, acc)) rfl hr ha hWr hWa hRn

open QMCLeafB.IntegrateM6

/-! ## 4.  The round-coded state as a sum of parts, and the caps

`IntegrateM6.enc_tuple_eq` splits `enc` of `RSt` into the frozen skeleton `n, A, t, mu, d` and the
three mutable lists `X` (coefficient `4`), `oks` (coefficient `6`) and `rec` (coefficient `1`).  Both
caps below are functions of the *frozen* data only, except for the height parameter `H` of `capRec`,
which the cap `Msz` feeds with `max (aX s) (capX s)` — that "max form" is what makes the ledger valid
**unconditionally**, without any reachability invariant: a first round from any state lands inside the
caps, and the `max` then absorbs whatever the initial state was. -/

/-- The encoded length of `mu`. -/
noncomputable def Lmu (s : RSt) : ℕ := (enc (stMu s)).length

/-- The encoded length of the grid denominator `d`. -/
noncomputable def Ld (s : RSt) : ℕ := (enc (stD s)).length

/-- The encoded length of the primal code `X`. -/
noncomputable def aX (s : RSt) : ℕ := (encodeList (enc : ℚ → List Bool) (stX s)).length

/-- The encoded length of the recorded cut payload `rec`. -/
noncomputable def aRec (s : RSt) : ℕ := (encodeList (enc : ℚ → List Bool) (stRec s)).length

/-- The **frozen skeleton**: everything `round` leaves alone (`n, A, t, mu, d`), with the three
mutable lists emptied. -/
noncomputable def skel (s : RSt) : ℕ :=
  (enc (((stN s, stA s), (([] : List ℚ), (stT s, stMu s))),
    ((stD s, ([] : List Bool)), ([] : List ℚ)))).length

/-- **The cap of the primal code.**  A cut round rebuilds `X` from `n²` entries, clipped into the
`mu`-box and snapped to the `d`-grid, so every entry has height at most `Lmu + Ld`. -/
noncomputable def capX (s : RSt) : ℕ := (stN s * stN s) * (6 * (Lmu s + Ld s) + 21)

/-- **The cap of the recorded oracle output**, at entry-height parameter `H`. -/
noncomputable def capRec (s : RSt) (H : ℕ) : ℕ :=
  (encodeList (enc : ℚ → List Bool) (stA s)).length
    + (stN s * stN s) * (6 * (2 * kapH (H + Lmu s + Ld s) (stN s)) + 21)
    + (stN s * stN s) * 33 + 1

/-- **The size cap `M` of the round-size ledger.** -/
noncomputable def Msz (s : RSt) : ℕ :=
  skel s + 4 * max (aX s) (capX s)
    + max (aRec s) (capRec s (max (aX s) (capX s))) + 6 * (stOks s).length + 6

/-- The additive decomposition of the state's encoding. -/
theorem enc_decomp (s : RSt) :
    (enc s).length = skel s + 4 * aX s + 6 * (stOks s).length + aRec s := by
  obtain ⟨⟨⟨n, A⟩, X, t, mu⟩, ⟨d, oks⟩, rec⟩ := s
  simp only [skel, aX, aRec, stN, stA, stX, stT, stMu, stD, stOks, stRec]
  exact IntegrateM6.enc_tuple_eq n A X t mu d oks rec

theorem round_components (s : RSt) :
    stN (round s) = stN s ∧ stA (round s) = stA s ∧ stT (round s) = stT s
      ∧ stMu (round s) = stMu s ∧ stD (round s) = stD s := by
  rw [round_eq]
  by_cases h : (oracleR s).1
  · rw [if_pos h]
    exact ⟨rfl, rfl, rfl, rfl, rfl⟩
  · rw [if_neg h]
    exact ⟨rfl, rfl, rfl, rfl, rfl⟩

theorem skel_round (s : RSt) : skel (round s) = skel s := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := round_components s
  simp only [skel, h1, h2, h3, h4, h5]

theorem Lmu_round (s : RSt) : Lmu (round s) = Lmu s := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := round_components s
  simp only [Lmu, h4]

theorem Ld_round (s : RSt) : Ld (round s) = Ld s := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := round_components s
  simp only [Ld, h5]

theorem capX_round (s : RSt) : capX (round s) = capX s := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := round_components s
  simp only [capX, h1, Lmu_round, Ld_round]

theorem capRec_round (s : RSt) (H : ℕ) : capRec (round s) H = capRec s H := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := round_components s
  simp only [capRec, h1, h2, Lmu_round, Ld_round]

theorem enc_round_decomp (s : RSt) :
    (enc (round s)).length
      = skel s + 4 * aX (round s) + 6 * (stOks (round s)).length + aRec (round s) := by
  rw [enc_decomp (round s), skel_round]

theorem oks_round_cut (s : RSt) (h : (oracleR s).1 = true) :
    stOks (round s) = stOks s ++ ([false] : List Bool) := by
  rw [round_eq, if_pos h]
  rfl

theorem stX_round_cut (s : RSt) (h : (oracleR s).1 = true) : stX (round s) = snapY s := by
  rw [round_eq, if_pos h]
  rfl

theorem stRec_round_cut (s : RSt) (h : (oracleR s).1 = true) :
    stRec (round s) = (oracleR s).2 := by
  rw [round_eq, if_pos h]
  rfl

theorem oks_round_ok (s : RSt) (h : (oracleR s).1 = false) :
    stOks (round s) = stOks s ++ ([true] : List Bool) := by
  rw [round_eq, if_neg (by simpa using h)]
  rfl

theorem stX_round_ok (s : RSt) (h : (oracleR s).1 = false) : stX (round s) = stX s := by
  rw [round_eq, if_neg (by simpa using h)]
  rfl

theorem stRec_round_ok (s : RSt) (h : (oracleR s).1 = false) : stRec (round s) = stRec s := by
  rw [round_eq, if_neg (by simpa using h)]
  rfl

/-! ### 4b.  Lengths and heights of the round's pieces -/

theorem flatMap_length_eq {α β : Type} (l : List α) (f : α → List β) (k : ℕ)
    (h : ∀ a ∈ l, (f a).length = k) : (l.flatMap f).length = l.length * k := by
  induction l with
  | nil => simp
  | cons a as ih =>
    rw [List.flatMap_cons, List.length_append, List.length_cons, ih (fun b hb => h b (by simp [hb])),
      h a (by simp)]
    ring

theorem flatMap_length_le {α β : Type} (l : List α) (f : α → List β) (k : ℕ)
    (h : ∀ a ∈ l, (f a).length ≤ k) : (l.flatMap f).length ≤ l.length * k := by
  induction l with
  | nil => simp
  | cons a as ih =>
    rw [List.flatMap_cons, List.length_append, List.length_cons]
    have h1 := ih (fun b hb => h b (by simp [hb]))
    have h2 := h a (by simp)
    have h3 : (as.length + 1) * k = as.length * k + k := by ring
    omega

theorem idxs_length_le (p : ℕ × List ℚ) : (idxs p).length ≤ p.1 := by
  simp only [idxs, List.length_range]
  exact List.length_take_le ..

theorem smulRaw_length (n : ℕ) (xs : List ℚ) (c : ℚ) :
    (QMCLeafB.MatQUpdate.smulRaw ((n, xs), c)).length
      = (xs.take n).length * (xs.take n).length := by
  simp only [QMCLeafB.MatQUpdate.smulRaw]
  rw [flatMap_length_eq _ _ ((xs.take n).length)]
  · simp
  · intro i _
    simp

theorem scaleY_length_le (s : RSt) : (scaleY s).length ≤ stN s * stN s := by
  simp only [scaleY]
  rw [smulRaw_length]
  have h : ((stepY s).take (stN s)).length ≤ stN s := List.length_take_le ..
  nlinarith

theorem snapY_length_le (s : RSt) : (snapY s).length ≤ stN s * stN s := by
  simp only [snapY]
  rw [nrmRow_length]
  exact scaleY_length_le s

theorem d_le_two_pow_Ld (s : RSt) : stD s ≤ 2 ^ Ld s := by
  have h := NatBinary.le_two_pow_length (stD s)
  have h2 : ((stD s).bits.length) = Ld s := rfl
  rwa [h2] at h

theorem snapY_height (s : RSt) :
    ∀ q ∈ snapY s, HasHeight q (Lmu s + Ld s) := by
  simp only [snapY]
  exact nrmRow_height (Ratio.height_length (stMu s)) (d_le_two_pow_Ld s) (scaleY s)

/-- **The primal code after a cut round is inside `capX`.** -/
theorem aX_round_le (s : RSt) (h : (oracleR s).1 = true) : aX (round s) ≤ capX s := by
  have hX : stX (round s) = snapY s := stX_round_cut s h
  simp only [aX, hX]
  have h1 : (encodeList (enc : ℚ → List Bool) (snapY s)).length
      ≤ (snapY s).length * (6 * (Lmu s + Ld s) + 21) :=
    encodeList_length_le _ _ (snapY_height s)
  have h2 : (snapY s).length ≤ stN s * stN s := snapY_length_le s
  have h3 : (snapY s).length * (6 * (Lmu s + Ld s) + 21)
      ≤ (stN s * stN s) * (6 * (Lmu s + Ld s) + 21) := Nat.mul_le_mul_right _ h2
  exact le_trans h1 (le_trans h3 (le_refl _))

theorem sgnOf_height (q : ℚ) : HasHeight (sgnOf q) 1 := by
  simp only [sgnOf]
  split_ifs
  · exact (HasHeight.one 1).neg
  · exact HasHeight.zero 1
  · exact HasHeight.one 1

theorem entV_height {p : ℕ × List ℚ} {H : ℕ} (h : ∀ q ∈ p.2, HasHeight q H) (i j : ℕ) :
    HasHeight (entV p i j) H := by
  simp only [entV]
  by_cases hk : i * p.1 + j < p.2.length
  · rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hk]
    simpa using h _ (List.getElem_mem hk)
  · rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by omega)]
    simpa [HasHeight.zero H] using HasHeight.zero H

theorem rowOf_height {p : ℕ × List ℚ} {H : ℕ} (h : ∀ q ∈ p.2, HasHeight q H) (i : ℕ) :
    ∀ q ∈ rowOf p i, HasHeight q H := by
  intro q hq
  simp only [rowOf, List.mem_map] at hq
  obtain ⟨j, _, rfl⟩ := hq
  exact entV_height h i j

theorem toRows_rowsHeight {n : ℕ} {X : List ℚ} {H : ℕ} (h : ∀ q ∈ X, HasHeight q H) :
    RowsHeight (toRows (n, X)) H := by
  intro v hv q hq
  simp only [toRows, List.mem_map] at hv
  obtain ⟨i, _, rfl⟩ := hv
  exact rowOf_height h i q hq

theorem toRows_rowsWidth (p : ℕ × List ℚ) : RowsWidth (toRows p) p.1 := by
  intro v hv
  simp only [toRows, List.mem_map] at hv
  obtain ⟨i, _, rfl⟩ := hv
  simp only [rowOf, List.length_map]
  exact idxs_length_le p

theorem toRows_length_le (p : ℕ × List ℚ) : (toRows p).length ≤ p.1 := by
  simp only [toRows, List.length_map]
  exact idxs_length_le p

theorem entries_le_aX {X : List ℚ} {q : ℚ} (hq : q ∈ X) :
    (enc q : List Bool).length ≤ (encodeList (enc : ℚ → List Bool) X).length := by
  induction X with
  | nil => simp at hq
  | cons a as ih =>
    rw [EncodedList.cons_length]
    rcases List.mem_cons.mp hq with rfl | h'
    · omega
    · have := ih h'
      omega

theorem diagSignF_length_le (p : ℕ × List ℚ) : (diagSignF p).length ≤ p.1 * p.1 := by
  have h := flatMap_length_le (idxs p)
    (fun i => (idxs p).map (fun j => if i = j then sgnOf (1 - entV p i i) else 0)) p.1
    (by
      intro i _
      simp only [List.length_map]
      exact idxs_length_le p)
  simp only [diagSignF]
  exact le_trans h (Nat.mul_le_mul_right _ (idxs_length_le p))

theorem diagSignF_height (p : ℕ × List ℚ) : ∀ q ∈ diagSignF p, HasHeight q 1 := by
  intro q hq
  simp only [diagSignF, List.mem_flatMap, List.mem_map] at hq
  obtain ⟨i, _, j, _, rfl⟩ := hq
  split_ifs
  · exact sgnOf_height _
  · exact HasHeight.zero 1

theorem getD_height {l : List ℚ} {H : ℕ} (h : ∀ q ∈ l, HasHeight q H) (i : ℕ) {d : ℚ}
    (hd : HasHeight d H) : HasHeight (l.getD i d) H := by
  by_cases hk : i < l.length
  · rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hk]
    simpa using h _ (List.getElem_mem hk)
  · rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by omega)]
    simpa using hd

theorem vecMulVecF_length_le (p : ℕ × List ℚ) : (vecMulVecF p).length ≤ p.1 * p.1 := by
  have h := flatMap_length_le (idxs p)
    (fun i => (idxs p).map (fun j => p.2.getD i 0 * p.2.getD j 0)) p.1
    (by
      intro i _
      simp only [List.length_map]
      exact idxs_length_le p)
  simp only [vecMulVecF]
  exact le_trans h (Nat.mul_le_mul_right _ (idxs_length_le p))

theorem vecMulVecF_height {p : ℕ × List ℚ} {K : ℕ} (h : ∀ q ∈ p.2, HasHeight q K) :
    ∀ q ∈ vecMulVecF p, HasHeight q (2 * K) := by
  intro q hq
  simp only [vecMulVecF, List.mem_flatMap, List.mem_map] at hq
  obtain ⟨i, _, j, _, rfl⟩ := hq
  have h1 : HasHeight (p.2.getD i 0) K := getD_height h i (HasHeight.zero K)
  have h2 : HasHeight (p.2.getD j 0) K := getD_height h j (HasHeight.zero K)
  have hm := h1.mul h2
  simpa [two_mul] using hm

/-- **The oracle's answer fits `capRec`.**  Branch analysis on `oracleR`: the diagonal-sign cut and
the descent's rank-one cut both have `n*n` entries at a height controlled by §2–§3, the stored matrix
`A` is bounded by the skeleton, and the `ok` answer is empty. -/
theorem oracleR_length_le (s : RSt) :
    (encodeList (enc : ℚ → List Bool) (oracleR s).2).length
      ≤ capRec s (max (aX s) (capX s)) := by
  set H := max (aX s) (capX s) with hHdef
  have hXd : aX s ≤ H := le_max_left _ _
  have hXh : ∀ q ∈ stX s, HasHeight q H := by
    intro q hq
    have h1 : HasHeight q (aX s) := by
      have h0 := Ratio.height_length q
      exact h0.mono (entries_le_aX hq)
    exact h1.mono hXd
  have hK0 : Lmu s + Ld s ≤ H + Lmu s + Ld s := by omega
  have hAns := runPivL_ans_height (mu := stMu s) (d := stD s) (L := Lmu s) (D := Ld s)
    (N := stN s) (K0 := H + Lmu s + Ld s) (Ratio.height_length (stMu s)) (d_le_two_pow_Ld s)
    hK0 (toRows_rowsHeight (fun q hq => (hXh q hq).mono (by omega)))
    (fun z hz => absurd hz (List.not_mem_nil))
    (toRows_rowsWidth (stN s, stX s))
    (fun z hz => absurd hz (List.not_mem_nil))
    (toRows_length_le (stN s, stX s))
  have hNcap : (stN s * stN s) * (6 * (2 * kapH (H + Lmu s + Ld s) (stN s)) + 21)
      ≤ capRec s H := by
    simp only [capRec]
    omega
  have hAterm : (encodeList (enc : ℚ → List Bool) (stA s)).length ≤ capRec s H := by
    simp only [capRec]
    omega
  have hDterm : (stN s * stN s) * 33 ≤ capRec s H := by
    simp only [capRec]
    omega
  have hV : (encodeList (enc : ℚ → List Bool) (vecMulVecF (stN s, (pivAns s).2))).length
      ≤ (stN s * stN s) * (6 * (2 * kapH (H + Lmu s + Ld s) (stN s)) + 21) := by
    have h1 : (encodeList (enc : ℚ → List Bool) (vecMulVecF (stN s, (pivAns s).2))).length
        ≤ (vecMulVecF (stN s, (pivAns s).2)).length
            * (6 * (2 * kapH (H + Lmu s + Ld s) (stN s)) + 21) := by
      refine encodeList_length_le _ _ ?_
      exact vecMulVecF_height hAns
    have h2 := vecMulVecF_length_le (stN s, (pivAns s).2)
    exact le_trans h1 (Nat.mul_le_mul_right _ h2)
  have hD : (encodeList (enc : ℚ → List Bool) (diagSignF (stN s, stX s))).length
      ≤ (stN s * stN s) * 33 := by
    have h1 : (encodeList (enc : ℚ → List Bool) (diagSignF (stN s, stX s))).length
        ≤ (diagSignF (stN s, stX s)).length * (6 * 1 + 21) :=
      encodeList_length_le _ 1 (diagSignF_height _)
    have h2 := diagSignF_length_le (stN s, stX s)
    calc (encodeList (enc : ℚ → List Bool) (diagSignF (stN s, stX s))).length
        ≤ (diagSignF (stN s, stX s)).length * (6 * 1 + 21) := h1
      _ ≤ (diagSignF (stN s, stX s)).length * 33 :=
          Nat.mul_le_mul_left _ (by norm_num)
      _ ≤ (stN s * stN s) * 33 := Nat.mul_le_mul_right _ h2
  by_cases hdv : dvR s = 0
  · have h1 : (oracleR s).2 = (threshB s).2 := by simp only [oracleR, if_pos hdv]
    rw [h1]
    by_cases hth : stT s ≤ fvR s
    · have h2 : (threshB s).2 = (pivCut s).2 := by simp only [threshB, if_pos hth]
      rw [h2]
      by_cases hp : (pivAns s).1 = true
      · have h3 : (pivCut s).2 = vecMulVecF (stN s, (pivAns s).2) := by
          simp only [pivCut, pivCutF, if_pos hp]
        rw [h3]
        exact le_trans hV hNcap
      · have h3 : (pivCut s).2 = ([] : List ℚ) := by
          simp only [pivCut, pivCutF, if_neg hp]
        rw [h3, EncodedList.nil]
        simp
    · have h2 : (threshB s).2 = stA s := by simp only [threshB, if_neg hth]
      rw [h2]
      exact hAterm
  · have h1 : (oracleR s).2 = diagSignF (stN s, stX s) := by
      simp only [oracleR, if_neg hdv]
    rw [h1]
    exact le_trans hD hDterm

theorem kapH_mono {H H' N : ℕ} (h : H ≤ H') : kapH H N ≤ kapH H' N := by
  have h1 : 6 * (2 * H) + 21 ≤ 6 * (2 * H') + 21 := by omega
  have h2 : N * (6 * (2 * H) + 21) ≤ N * (6 * (2 * H') + 21) := Nat.mul_le_mul_left _ h1
  have h3 : H + N * (6 * (2 * H) + 21) ≤ H' + N * (6 * (2 * H') + 21) := by omega
  have h4 : 6 * (H + N * (6 * (2 * H) + 21)) + 21
      ≤ 6 * (H' + N * (6 * (2 * H') + 21)) + 21 := by omega
  have h5 : qfH H N ≤ qfH H' N := by
    simp only [qfH]
    exact Nat.mul_le_mul_left N h4
  simp only [kapH]
  omega

theorem capRec_mono (s : RSt) {H H' : ℕ} (h : H ≤ H') : capRec s H ≤ capRec s H' := by
  have h1 : H + Lmu s + Ld s ≤ H' + Lmu s + Ld s := by omega
  have h2 := kapH_mono (N := stN s) h1
  have h3 : 6 * (2 * kapH (H + Lmu s + Ld s) (stN s)) + 21
      ≤ 6 * (2 * kapH (H' + Lmu s + Ld s) (stN s)) + 21 := by omega
  have h4 := Nat.mul_le_mul_left (stN s * stN s) h3
  simp only [capRec]
  omega

/-- The `ok` branch of one round: the state's encoding grows by exactly the flag. -/
theorem enc_round_ok (s : RSt) (h : (oracleR s).1 = false) :
    (enc (round s)).length = (enc s).length + 6 := by
  rw [enc_round_decomp s, enc_decomp s, oks_round_ok s h, List.length_append]
  simp only [aX, aRec, stX_round_ok s h, stRec_round_ok s h, List.length_append, List.length_cons,
    List.length_nil]
  omega

/-- The `cut` branch of one round: everything is inside the caps. -/
theorem enc_round_cut_le (s : RSt) (h : (oracleR s).1 = true) :
    (enc (round s)).length ≤ Msz s := by
  have hX := aX_round_le s h
  have hR := oracleR_length_le s
  have hR' : aRec (round s) ≤ capRec s (max (aX s) (capX s)) := by
    simp only [aRec, stRec_round_cut s h]
    exact hR
  have hX' : aX (round s) ≤ max (aX s) (capX s) := le_trans hX (le_max_right _ _)
  have hoks : (stOks (round s)).length = (stOks s).length + 1 := by
    rw [oks_round_cut s h, List.length_append]
    simp
  rw [enc_round_decomp s, hoks]
  simp only [Msz]
  omega

theorem round_step (s : RSt) :
    (enc (round s)).length ≤ max ((enc s).length + 6) (Msz s) := by
  by_cases h : (oracleR s).1 = true
  · exact le_trans (enc_round_cut_le s h) (le_max_right _ _)
  · have hf : (oracleR s).1 = false := by simpa using h
    rw [enc_round_ok s hf]
    exact le_max_left _ _

theorem round_cap (s : RSt) : Msz (round s) ≤ Msz s + 6 := by
  by_cases h : (oracleR s).1 = true
  · have hX := aX_round_le s h
    have hR := oracleR_length_le s
    have hR' : aRec (round s) ≤ capRec s (max (aX s) (capX s)) := by
      simp only [aRec, stRec_round_cut s h]
      exact hR
    have hXm : max (aX (round s)) (capX (round s)) = capX s := by
      rw [capX_round]
      exact max_eq_right hX
    have hcap : capRec s (capX s) ≤ capRec s (max (aX s) (capX s)) :=
      capRec_mono s (le_max_right _ _)
    have hoks : (stOks (round s)).length = (stOks s).length + 1 := by
      rw [oks_round_cut s h, List.length_append]
      simp
    rw [Msz, hXm, capRec_round, hoks, skel_round]
    simp only [Msz]
    omega
  · have hf : (oracleR s).1 = false := by simpa using h
    have h1 : stX (round s) = stX s := stX_round_ok s hf
    have h2 : stRec (round s) = stRec s := stRec_round_ok s hf
    have hoks : (stOks (round s)).length = (stOks s).length + 1 := by
      rw [oks_round_ok s hf, List.length_append]
      simp
    rw [Msz, skel_round, capX_round, capRec_round, hoks]
    simp only [Msz, aX, aRec, h1, h2]
    omega

local instance instRequestCodingRoundSize : Coding (QuantumMaxCutEnergy.Input × List Bool) :=
  ⟨QuantumMaxCutEnergy.encodeRequest⟩

/-- **The endgame with the round-size ledger discharged except for the cap bound `hM`.**

`IntegrateM6.endgame_RSt_ledger` at `σ = RoundProgram.RSt`, `round = RoundProgram.round`,
`c = 6` (one `ok` flag) and `M = Msz`: its `hMinv`/`hstep` slots are `round_cap`/`round_step`
(proved above, unconditionally), so the only remaining hypothesis is the polynomial cap bound
`hM` — which needs the normalisation guard discussed in `round-ledger-plan.md`. -/
theorem endgame_RSt_size
    (rmax : QuantumMaxCutEnergy.Input → ℚ) (m : QuantumMaxCutEnergy.Input → ℕ)
    (dq : QuantumMaxCutEnergy.Input → ℚ)
    (hrmax : ∀ G : QuantumMaxCutEnergy.Input, 0 ≤ rmax G)
    (hm1 : ∀ G : QuantumMaxCutEnergy.Input, 1 ≤ m G)
    (hdq : ∀ G : QuantumMaxCutEnergy.Input, 0 < dq G)
    (hhalve : ∀ G : QuantumMaxCutEnergy.Input,
      (Real.sqrt (QMCLeafB.EngineIterates.rho0R (G.n * G.n) ((rmax G : ℚ) : ℝ)))⁻¹ ^ (m G)
        ≤ 1 / 2)
    (K : QuantumMaxCutEnergy.Input → ℕ)
    (hK : ∀ G : QuantumMaxCutEnergy.Input,
      QMCLeafB.FinalStroke.budgetRounds G (dq G) (m G) ≤ K G)
    (init0 : ((QuantumMaxCutEnergy.Input × List Bool) × ℚ) → RSt)
    (hinit0 : Automatic.Poly init0)
    (hinitTape : ∀ p : ((QuantumMaxCutEnergy.Input × List Bool) × ℚ),
      init0 p = init0 (QMCLeafB.FinalStroke.noTape p.1.1 p.2))
    (fuel : ((QuantumMaxCutEnergy.Input × List Bool) × ℚ) → List Bool)
    (hfuel : Automatic.Poly fuel)
    (hfuelLen : ∀ p : ((QuantumMaxCutEnergy.Input × List Bool) × ℚ),
      (fuel p).length = K p.1.1 * m p.1.1)
    (C₀ k : ℕ) (hk : 1 ≤ k)
    (hM : ∀ s : RSt, Msz s ≤ C₀ * ((enc s).length + 1) ^ k)
    (htop : ∀ (G : QuantumMaxCutEnergy.Input) (t : ℚ),
      -(((QMCLeafB.EngineRuntime.Rq G / 40000 : ℚ)) : ℝ) ≤ (t : ℝ) → t ≤ 0 →
      QMCLeafB.FinalStroke.loopBit init0 round QMCLeafB.RoundProgram.verdict
        (fun G' _ => K G' * m G') G t = true)
    (hd : ∀ (G : QuantumMaxCutEnergy.Input) (t : ℚ), 2 ≤ G.n →
      -QMCLeafB.EngineRuntime.Rq G ≤ t →
      (t : ℝ) < -(((QMCLeafB.EngineRuntime.Rq G / 40000 : ℚ)) : ℝ) →
      QMCLeafB.FinalStroke.RunParts
        (QMCLeafB.FinalStroke.loopBit init0 round QMCLeafB.RoundProgram.verdict
          (fun G' _ => K G' * m G')) G t
        (QMCLeafB.FinalStroke.runParamsOfK G (dq G) (hdq G) (rmax G) (hrmax G) (m G) (hm1 G)
          (K G) (hK G) (hhalve G))) :
    QMCLeafB.FinishLine.SolutionStatement :=
  IntegrateM6.endgame_RSt_ledger rmax m dq hrmax hm1 hdq hhalve K hK init0 hinit0 hinitTape fuel hfuel
    hfuelLen Msz C₀ 6 k hk round_cap round_step hM htop hd

end QMCLeafB.RoundSizeM6

#print axioms QMCLeafB.RoundSizeM6.endgame_RSt_size
#print axioms QMCLeafB.RoundSizeM6.round_step
#print axioms QMCLeafB.RoundSizeM6.round_cap
#print axioms QMCLeafB.RoundSizeM6.oracleR_length_le
#print axioms QMCLeafB.RoundSizeM6.diagSignF_length_le
#print axioms QMCLeafB.RoundSizeM6.vecMulVecF_height
#print axioms QMCLeafB.RoundSizeM6.toRows_rowsHeight
#print axioms QMCLeafB.RoundSizeM6.aX_round_le
#print axioms QMCLeafB.RoundSizeM6.enc_decomp
#print axioms QMCLeafB.RoundSizeM6.capRec_round
#print axioms QMCLeafB.RoundSizeM6.pivStepL_inl_height
#print axioms QMCLeafB.RoundSizeM6.runPivLFuel_ans_height
#print axioms QMCLeafB.RoundSizeM6.runPivL_ans_height
#print axioms QMCLeafB.RoundSizeM6.qformRows_height
#print axioms QMCLeafB.RoundSizeM6.zeroWitness_height
#print axioms QMCLeafB.RoundSizeM6.negWitness_height


