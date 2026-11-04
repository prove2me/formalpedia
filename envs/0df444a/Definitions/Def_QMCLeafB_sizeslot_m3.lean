-- Prove2me | Definitions.Def_QMCLeafB_sizeslot_m3
-- name    : QMCLeafB_sizeslot_m3
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-04T00:32:19.571267+00:00
-- url     : https://prove2.me/theorems/a319f1a4-01bc-49e7-9a47-0fee9fd9918a
-- title:
--   QMCLeafB sizeslot_m3
-- statement:
--   # leaf B phase 14 — brick `size-slot` (swarm `smw1a99tp`, member m3, direction d6)
--
--   Published as part of the QMCLeafB library mirror supporting the quantum max-cut campaign's polynomial-time SDP-value certificate (AGM20, TQC 2020, arXiv 2003.14394).

import Mathlib
import Definitions.Def_QMCLeafB_final_reunion_m7
/-
# leaf B phase 14 — brick `size-slot` (swarm `smw1a99tp`, member m3, direction d6)

The closing stroke's size slot, at the concrete round of `QMCLeafB.RoundProgram`.

`QMCLeafB.FinalReunion.endgame_RSt` (and its two siblings at m8's `St`) need

    hmono : ∀ (s : RSt) (j : ℕ), (enc (round^[j] s)).length ≤ C * ((enc s).length + 1) ^ k

and turn it into the loop envelope through `orbit_of_monomial_pow`.  §2 of this file proves
that **no** `C`, `k` satisfy it at `RSt`: every round appends one `ok` flag to `stOks`, a `List Bool`
element costs 3 encoded bits, and `stOks` sits at positive weight in the encoding of the state — so
`(enc (round^[j] s)).length ≥ 3 j + const` against a right-hand side that does not move with `j`.
The same argument applies to any state that records per-round history, so the hypothesis is a defect
of the closing interface, not of `RSt`.

The satisfiable form is the **pair-level** growth class of the loop state `σ × List Bool`, where one
appended `ok` flag and one *dropped* fuel bit occur in the same step:

    ∀ s f j, j ≤ f.length →
      (encSt (round^[j] s, f.drop j)).length ≤ C * ((encSt (s, f)).length + 1) ^ k

§3 supplies the producer from this class (`orbit_of_pair_monomial`), §4 the endgame variant at `RSt`
that consumes it (`endgame_RSt_pair`), and §5 the clean sufficient condition a non-recording state
satisfies outright (one-step non-expansion of the pair).

No `sorry`, no `axiom`; audit in §6.
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000

open scoped BigOperators
open OAI.MetricKMedian.Binary
open OAI.MetricKMedian.Binary.Automatic

namespace QMCLeafB.SizeSlot

open QuantumMaxCutEnergy
open QMCLeafB.RoundProgram

/-! ## 1.  Encoding bookkeeping for the packed round state -/

theorem encodeList_append {α : Type} (ea : α → List Bool) (l₁ l₂ : List α) :
    encodeList ea (l₁ ++ l₂) = encodeList ea l₁ ++ encodeList ea l₂ := by
  induction l₁ with
  | nil => rfl
  | cons a t ih =>
      simp only [List.cons_append, encodeList, ih, List.append_assoc]

/-- One `Bool` costs exactly `3` encoded bits. -/
theorem encodeList_bool_length (l : List Bool) :
    (encodeList (enc : Bool → List Bool) l).length = 3 * l.length := by
  induction l with
  | nil => rfl
  | cons b t ih =>
      have h1 : (encodeList (enc : Bool → List Bool) (b :: t)).length
          = 2 * (enc b).length + 1 + (encodeList (enc : Bool → List Bool) t).length :=
        EncodedList.cons_length (ea := (enc : Bool → List Bool)) b t
      have h2 : (enc b).length = 1 := rfl
      rw [h1, h2, ih]
      simp only [List.length_cons]
      ring

/-- Dropping `j` fuel bits removes exactly `3j` encoded bits. -/
theorem encodeList_bool_drop_length (l : List Bool) (j : ℕ) :
    (encodeList (enc : Bool → List Bool) (l.drop j)).length = 3 * (l.length - j) := by
  rw [encodeList_bool_length, List.length_drop]

theorem enc_pair_fst_le {α β : Type} [Coding α] [Coding β] (x : α × β) :
    (enc x.1).length ≤ (enc x).length := by
  have h : (enc x).length = 2 * (enc x.1).length + 1 + (enc x.2).length :=
    encodePair_length (enc : α → List Bool) (enc : β → List Bool) x
  have h2 := Nat.zero_le (enc x.2).length
  omega

theorem enc_pair_snd_le {α β : Type} [Coding α] [Coding β] (x : α × β) :
    (enc x.2).length ≤ (enc x).length := by
  have h : (enc x).length = 2 * (enc x.1).length + 1 + (enc x.2).length :=
    encodePair_length (enc : α → List Bool) (enc : β → List Bool) x
  have h2 := Nat.zero_le (enc x.1).length
  omega

/-- **`stOks` is at positive weight**: three bits per recorded flag are inside `enc s`. -/
theorem enc_RSt_ge_oks (s : RSt) : 3 * (stOks s).length ≤ (enc s).length := by
  obtain ⟨⟨⟨n, A⟩, ⟨X, ⟨t, mu⟩⟩⟩, ⟨⟨d, oks⟩, rec⟩⟩ := s
  have h1 : (enc oks).length ≤ (enc (d, oks)).length :=
    enc_pair_snd_le (α := ℕ) (β := List Bool) (d, oks)
  have h2 : (enc (d, oks)).length ≤ (enc ((d, oks), rec)).length :=
    enc_pair_fst_le (α := ℕ × List Bool) (β := List ℚ) ((d, oks), rec)
  have h3 : (enc ((d, oks), rec)).length
      ≤ (enc (((n, A), (X, (t, mu))), ((d, oks), rec))).length :=
    enc_pair_snd_le (α := (ℕ × List ℚ) × (List ℚ × (ℚ × ℚ)))
      (β := (ℕ × List Bool) × List ℚ) (((n, A), (X, (t, mu))), ((d, oks), rec))
  have h4 : (enc oks).length = 3 * oks.length := encodeList_bool_length oks
  change 3 * oks.length ≤ (enc (((n, A), (X, (t, mu))), ((d, oks), rec))).length
  omega

theorem stOks_round (s : RSt) :
    (stOks (QMCLeafB.RoundProgram.round s)).length = (stOks s).length + 1 := by
  rw [QMCLeafB.RoundProgram.round_eq]
  split
  · simp [QMCLeafB.RoundProgram.roundCut]
  · simp [QMCLeafB.RoundProgram.roundOk]

theorem stOks_iterate (s : RSt) (j : ℕ) :
    (stOks ((QMCLeafB.RoundProgram.round^[j]) s)).length = (stOks s).length + j := by
  induction j with
  | zero => simp
  | succ j ih =>
      rw [Function.iterate_succ_apply', stOks_round, ih]
      omega

/-! ## 2.  The state-level growth class is unsatisfiable at `RSt` -/

/-- **No monomial growth class for the state alone.**  Whatever `C`, `k` are, `RSt`'s round
eventually outgrows `C ((enc s) + 1)^k`, because it records one `ok` flag — three encoded bits at
positive weight — per round.  Hence `QMCLeafB.FinalStroke.orbit_of_monomial_pow`'s hypothesis, which
`endgame_RSt`/`endgame_orbit(_sq)` all carry, can never be instantiated at this round. -/
theorem no_state_growth_class (C k : ℕ) :
    ¬ (∀ (s : RSt) (j : ℕ),
      (enc ((QMCLeafB.RoundProgram.round^[j]) s)).length ≤ C * ((enc s).length + 1) ^ k) := by
  intro h
  set s0 : RSt := mkSt 1 [] [] 0 0 0 [] [] with hs0
  set x : ℕ := C * ((enc s0).length + 1) ^ k with hx
  have hoks0 : (stOks s0).length = 0 := rfl
  have hbound := h s0 (3 * x + 1)
  have hlow := enc_RSt_ge_oks ((QMCLeafB.RoundProgram.round^[3 * x + 1]) s0)
  have hite := stOks_iterate s0 (3 * x + 1)
  rw [hoks0] at hite
  omega

/-! ## 3.  The pair-level producer -/

/-- **A pair-level growth class gives the loop envelope.**  One `ok` flag appended to the state and
one fuel bit dropped per round: the pair `(state, fuel tail)` is what the loop's size slot bounds, so
this is the class a recording round can satisfy. -/
theorem orbit_of_pair_monomial {σ : Type} [Coding σ] (round : σ → σ) (C k : ℕ)
    (hmono : ∀ (s : σ) (f : List Bool) (j : ℕ), j ≤ f.length →
      (QMCLeafB.SimPoly.encSt ((round^[j]) s, f.drop j)).length
        ≤ C * ((QMCLeafB.SimPoly.encSt (s, f)).length + 1) ^ k) :
    ∀ (a : σ × List Bool) (j : ℕ), j ≤ a.2.length →
      (QMCLeafB.SimPoly.encSt ((round^[j]) a.1, a.2.drop j)).length
        ≤ (QMCLeafB.FinalStroke.sizesOrbitPow C k).eval (QMCLeafB.SimPoly.encSt a).length := by
  intro a j hj
  have h := hmono a.1 a.2 j hj
  rw [QMCLeafB.FinalStroke.sizesOrbitPow_eval]
  have hle : C ≤ 2 * C + 2 := by omega
  calc (QMCLeafB.SimPoly.encSt ((round^[j]) a.1, a.2.drop j)).length
      ≤ C * ((QMCLeafB.SimPoly.encSt (a.1, a.2)).length + 1) ^ k := h
    _ = C * ((QMCLeafB.SimPoly.encSt a).length + 1) ^ k := rfl
    _ ≤ (2 * C + 2) * ((QMCLeafB.SimPoly.encSt a).length + 1) ^ k :=
        Nat.mul_le_mul_right _ hle

/-! ## 4.  The endgame at `RSt`, with the pair-level size hypothesis -/

/-- The request coding of the leaf, as in `Check_final_reunion_m7`. -/
local instance instRequestCodingSizeSlot :
    Coding (QuantumMaxCutEnergy.Input × List Bool) :=
  ⟨QuantumMaxCutEnergy.encodeRequest⟩

/-- **`d9f601e5` from the tape-free loop at `RSt`, with the pair-level size class.**  This is
`QMCLeafB.FinalReunion.endgame_RSt` with the unsatisfiable state-level `hmono` (§2) replaced by the
pair-level class of §3.  Every other hypothesis is unchanged. -/
theorem endgame_RSt_pair
    (rmax : ℚ) (hrmax : 0 ≤ rmax) (m : ℕ) (hm1 : 1 ≤ m)
    (hhalve : ∀ G : QuantumMaxCutEnergy.Input,
      (Real.sqrt (QMCLeafB.EngineIterates.rho0R (G.n * G.n) (rmax : ℝ)))⁻¹ ^ m ≤ 1 / 2)
    (K : QuantumMaxCutEnergy.Input → ℕ)
    (hK : ∀ G : QuantumMaxCutEnergy.Input,
      QMCLeafB.FinalStroke.budgetRounds G 1 m ≤ K G)
    (init0 : ((QuantumMaxCutEnergy.Input × List Bool) × ℚ) → QMCLeafB.RoundProgram.RSt)
    (hinit0 : Automatic.Poly init0)
    (hinitTape : ∀ p : ((QuantumMaxCutEnergy.Input × List Bool) × ℚ),
      init0 p = init0 (QMCLeafB.FinalStroke.noTape p.1.1 p.2))
    (fuel : ((QuantumMaxCutEnergy.Input × List Bool) × ℚ) → List Bool)
    (hfuel : Automatic.Poly fuel)
    (C k : ℕ)
    (hmono : ∀ (s : QMCLeafB.RoundProgram.RSt) (f : List Bool) (j : ℕ), j ≤ f.length →
      (QMCLeafB.SimPoly.encSt ((QMCLeafB.RoundProgram.round^[j]) s, f.drop j)).length
        ≤ C * ((QMCLeafB.SimPoly.encSt (s, f)).length + 1) ^ k)
    (hfuelLen : ∀ p : ((QuantumMaxCutEnergy.Input × List Bool) × ℚ),
      (fuel p).length = K p.1.1 * m)
    (hd : ∀ (G : QuantumMaxCutEnergy.Input) (t : ℚ),
      -QMCLeafB.EngineRuntime.Rq G ≤ t → t ≤ 0 →
      QMCLeafB.FinalStroke.RunParts
        (QMCLeafB.FinalStroke.loopBit init0 QMCLeafB.RoundProgram.round
          QMCLeafB.RoundProgram.verdict (fun G' _ => K G' * m)) G t
        (QMCLeafB.FinalStroke.runParamsOfK G 1 (by norm_num) rmax hrmax m hm1 (K G) (hK G)
          (hhalve G))) :
    QMCLeafB.FinishLine.SolutionStatement :=
  QMCLeafB.FinalStroke.endgame_orbit_of_parts
    init0 fuel QMCLeafB.RoundProgram.round QMCLeafB.RoundProgram.verdict
    hinit0 hfuel QMCLeafB.RoundProgram.poly_round QMCLeafB.RoundProgram.poly_verdict
    (QMCLeafB.FinalStroke.sizesOrbitPow C k)
    (fun a j hj => orbit_of_pair_monomial QMCLeafB.RoundProgram.round C k hmono a j hj)
    (fun G' _ => K G' * m) hinitTape hfuelLen
    (fun G t _ hlo hhi => (hd G t hlo hhi).toRunData)

/-! ## 5.  A sufficient condition for a non-recording state -/

/-- **One-step non-expansion of the loop pair gives the envelope.**  If a round never lengthens the
pair `(state, fuel tail)`, the orbit satisfies the size slot with `2(X+1)`.  This is what a state
that keeps only a running `any-ok` bit (instead of the full `ok` list) satisfies: the appended flag
costs `3` bits and the dropped fuel bit pays `3`. -/
theorem horbit_of_step_le {σ : Type} [Coding σ] (rnd : σ → σ)
    (hstep : ∀ (s : σ) (f : List Bool),
      (QMCLeafB.SimPoly.encSt (rnd s, f.tail)).length ≤ (QMCLeafB.SimPoly.encSt (s, f)).length) :
    ∀ (a : σ × List Bool) (j : ℕ), j ≤ a.2.length →
      (QMCLeafB.SimPoly.encSt ((rnd^[j]) a.1, a.2.drop j)).length
        ≤ (QMCLeafB.FinalStroke.sizesOrbitPow 0 1).eval (QMCLeafB.SimPoly.encSt a).length := by
  intro a j hj
  have key : ∀ j, j ≤ a.2.length →
      (QMCLeafB.SimPoly.encSt ((rnd^[j]) a.1, a.2.drop j)).length
        ≤ (QMCLeafB.SimPoly.encSt a).length := by
    intro j
    induction j with
    | zero => intro _; simp
    | succ j ih =>
        intro hj'
        have hjj : j ≤ a.2.length := by omega
        have hstepj := hstep ((rnd^[j]) a.1) (a.2.drop j)
        have hdrop : a.2.drop (j + 1) = (a.2.drop j).tail := by
          rw [← List.tail_drop]
        have h1 : (rnd^[j + 1]) a.1 = rnd ((rnd^[j]) a.1) :=
          Function.iterate_succ_apply' rnd j a.1
        rw [h1, hdrop]
        exact hstepj.trans (ih hjj)
  rw [QMCLeafB.FinalStroke.sizesOrbitPow_eval]
  have h := key j hj
  have : (QMCLeafB.SimPoly.encSt a).length ≤ (2 * 0 + 2) * ((QMCLeafB.SimPoly.encSt a).length + 1) ^ 1 := by
    simp
    omega
  exact h.trans this

/-! ## 6.  The concrete round's size ledger at `RSt`

The pair-level class of §3 needs the encoded length of every visited state.  This section proves it
from the packed state's own component formula, the snap's height ledger, and one explicit *charge*
hypothesis for the separation oracle's cut normal (see `Check_sizeslot_charge_m3` for the height
toolkit that discharges everything except the descent's witness heights). -/

/-- **The exact encoded length of the packed round state.** -/
theorem enc_RSt_eq (s : RSt) :
    (enc s).length
      = 8 * (enc (stN s)).length + 4 * (enc (stA s)).length + 4 * (enc (stX s)).length
        + 4 * (enc (stT s)).length + 2 * (enc (stMu s)).length + 4 * (enc (stD s)).length
        + 2 * (enc (stOks s)).length + (enc (stRec s)).length + 14 := by
  obtain ⟨⟨⟨n, A⟩, ⟨X, ⟨t, mu⟩⟩⟩, ⟨⟨d, oks⟩, rec⟩⟩ := s
  have e1 : (enc (((⟨n, A⟩, ⟨X, ⟨t, mu⟩⟩), ⟨⟨d, oks⟩, rec⟩) : RSt)).length
      = 2 * (enc ((⟨n, A⟩, ⟨X, ⟨t, mu⟩⟩) : (ℕ × List ℚ) × (List ℚ × (ℚ × ℚ)))).length + 1
        + (enc ((⟨⟨d, oks⟩, rec⟩) : (ℕ × List Bool) × List ℚ)).length :=
    encodePair_length (enc : ((ℕ × List ℚ) × (List ℚ × (ℚ × ℚ))) → List Bool)
      (enc : ((ℕ × List Bool) × List ℚ) → List Bool) _
  have e2 : (enc ((⟨n, A⟩, ⟨X, ⟨t, mu⟩⟩) : (ℕ × List ℚ) × (List ℚ × (ℚ × ℚ)))).length
      = 2 * (enc (⟨n, A⟩ : ℕ × List ℚ)).length + 1
        + (enc (⟨X, ⟨t, mu⟩⟩ : List ℚ × (ℚ × ℚ))).length :=
    encodePair_length (enc : (ℕ × List ℚ) → List Bool) (enc : (List ℚ × (ℚ × ℚ)) → List Bool) _
  have e3 : (enc (⟨n, A⟩ : ℕ × List ℚ)).length = 2 * (enc n).length + 1 + (enc A).length :=
    encodePair_length (enc : ℕ → List Bool) (enc : List ℚ → List Bool) _
  have e4 : (enc (⟨X, ⟨t, mu⟩⟩ : List ℚ × (ℚ × ℚ))).length
      = 2 * (enc X).length + 1 + (enc (⟨t, mu⟩ : ℚ × ℚ)).length :=
    encodePair_length (enc : List ℚ → List Bool) (enc : (ℚ × ℚ) → List Bool) _
  have e5 : (enc (⟨t, mu⟩ : ℚ × ℚ)).length = 2 * (enc t).length + 1 + (enc mu).length :=
    encodePair_length (enc : ℚ → List Bool) (enc : ℚ → List Bool) _
  have e6 : (enc (⟨⟨d, oks⟩, rec⟩ : (ℕ × List Bool) × List ℚ)).length
      = 2 * (enc (⟨d, oks⟩ : ℕ × List Bool)).length + 1 + (enc rec).length :=
    encodePair_length (enc : (ℕ × List Bool) → List Bool) (enc : List ℚ → List Bool) _
  have e7 : (enc (⟨d, oks⟩ : ℕ × List Bool)).length = 2 * (enc d).length + 1 + (enc oks).length :=
    encodePair_length (enc : ℕ → List Bool) (enc : List Bool → List Bool) _
  change (enc (((n, A), (X, (t, mu))), ((d, oks), rec)) : List Bool).length
      = 8 * (enc n).length + 4 * (enc A).length + 4 * (enc X).length + 4 * (enc t).length
        + 2 * (enc mu).length + 4 * (enc d).length + 2 * (enc oks).length + (enc rec).length + 14
  omega

/-- The same formula at the state constructor. -/
theorem enc_mkSt_eq (n : ℕ) (A X : List ℚ) (t mu : ℚ) (d : ℕ) (oks : List Bool) (rec : List ℚ) :
    (enc (mkSt n A X t mu d oks rec)).length
      = 8 * (enc n).length + 4 * (enc A).length + 4 * (enc X).length
        + 4 * (enc t).length + 2 * (enc mu).length + 4 * (enc d).length
        + 2 * (enc oks).length + (enc rec).length + 14 := by
  rw [show mkSt n A X t mu d oks rec = (((n, A), (X, (t, mu))), ((d, oks), rec)) from rfl]
  rw [enc_RSt_eq]
  simp [stN, stA, stX, stT, stMu, stD, stOks, stRec, mkSt]

/-- One `ok` flag costs exactly `3` encoded bits. -/
theorem enc_append_single_bool (l : List Bool) (b : Bool) :
    (enc (l ++ [b])).length = (enc l).length + 3 := by
  have e : (enc (l ++ [b]) : List Bool) = encodeList (enc : Bool → List Bool) l
      ++ encodeList (enc : Bool → List Bool) [b] := encodeList_append _ l [b]
  have h2 : (encodeList (enc : Bool → List Bool) [b]).length = 3 := by
    rw [encodeList_bool_length]; simp
  have h3 : (encodeList (enc : Bool → List Bool) l).length = 3 * l.length :=
    encodeList_bool_length l
  have h4 : (enc l).length = 3 * l.length := encodeList_bool_length l
  rw [e, List.length_append, h2, h4, h3]

/-- **The snap's charge**: the clipped, snapped matrix code of a state whose box bound has height
`M` and whose grid is `≤ 2^D` costs at most `ℓ (6(M+D)+21)` bits, where `ℓ` is the code's length. -/
theorem enc_snapY_le (s : RSt) (M D : ℕ) (hmu : HasHeight (stMu s) M) (hdD : stD s ≤ 2 ^ D) :
    (enc (QMCLeafB.RoundProgram.snapY s)).length
      ≤ (QMCLeafB.RoundProgram.snapY s).length * (6 * (M + D) + 21) := by
  have h : ∀ q ∈ QMCLeafB.RoundProgram.snapY s, HasHeight q (M + D) := by
    intro q hq
    unfold QMCLeafB.RoundProgram.snapY QMCLeafB.RoundProgram.nrmRow at hq
    obtain ⟨r, _, rfl⟩ := List.mem_map.mp hq
    exact QMCLeafB.RoundProgram.hasHeight_nrmQ hmu hdD r
  have h1 := QMCLeafB.SizesProfile.enc_row_le (QMCLeafB.RoundProgram.snapY s) (M + D) h
  refine le_trans h1 (Nat.mul_le_mul_left _ ?_)
  omega

/-- A list's encoded length dominates each of its entries' encoded lengths. -/
theorem list_entry_le {q : ℚ} {l : List ℚ} (h : q ∈ l) : (enc q).length ≤ (enc l).length := by
  induction l with
  | nil => simp at h
  | cons a t ih =>
      have h1 : (enc (a :: t) : List Bool).length = 2 * (enc a).length + 1 + (enc t).length :=
        EncodedList.cons_length (ea := (enc : ℚ → List Bool)) a t
      rcases List.mem_cons.mp h with rfl | hmem
      · rw [h1]; omega
      · have h2 := ih hmem; rw [h1]; omega

theorem enc_stN_le (s : RSt) : (enc (stN s)).length ≤ (enc s).length := by
  have := enc_RSt_eq s; omega
theorem enc_stA_le (s : RSt) : (enc (stA s)).length ≤ (enc s).length := by
  have := enc_RSt_eq s; omega
theorem enc_stX_le (s : RSt) : (enc (stX s)).length ≤ (enc s).length := by
  have := enc_RSt_eq s; omega
theorem enc_stT_le (s : RSt) : (enc (stT s)).length ≤ (enc s).length := by
  have := enc_RSt_eq s; omega
theorem enc_stMu_le (s : RSt) : (enc (stMu s)).length ≤ (enc s).length := by
  have := enc_RSt_eq s; omega
theorem enc_stD_le (s : RSt) : (enc (stD s)).length ≤ (enc s).length := by
  have := enc_RSt_eq s; omega
theorem enc_stRec_le (s : RSt) : (enc (stRec s)).length ≤ (enc s).length := by
  have := enc_RSt_eq s; omega
theorem enc_stOks_le (s : RSt) : (enc (stOks s)).length ≤ (enc s).length := by
  have := enc_RSt_eq s; omega

theorem d_le_two_pow_enc (d : ℕ) : d ≤ 2 ^ (enc d).length := by
  have h := NatBinary.le_two_pow_length d
  have e : (enc d : List Bool) = Nat.bits d := rfl
  rw [e]
  exact h

/-- **The ledger.**  `ℓ` bounds the primal code's length along the whole orbit (a shape invariant the
snap preserves, from `MatQUpdate.Step.stepFun_length`), `Br` bounds the separation oracle's cut normal
along the orbit, and `Ls` is the initial state's encoded length.  Then every visited state's encoded
length is `Ψ + 6j`: the six bits per round are exactly the appended `ok` flag. -/
theorem enc_iterate_le (s : RSt) (ℓ Br : ℕ)
    (hX0 : (stX s).length ≤ ℓ)
    (hsnap : ∀ t : RSt, (stX t).length ≤ ℓ → (QMCLeafB.RoundProgram.snapY t).length ≤ ℓ)
    (hc : ∀ (t : RSt), (∀ q ∈ stX t, HasHeight q (enc s).length) → (stX t).length ≤ ℓ →
      (enc (QMCLeafB.RoundProgram.oracleR t).2).length ≤ Br)
    (hBr : (enc (stRec s)).length ≤ Br) :
    ∀ j : ℕ, (enc ((QMCLeafB.RoundProgram.round^[j]) s)).length
      ≤ (8 * (enc (stN s)).length + 4 * (enc (stA s)).length
          + 4 * (max (enc (stX s)).length
              (ℓ * (6 * ((enc (stMu s)).length + (enc (stD s)).length) + 21)))
          + 4 * (enc (stT s)).length + 2 * (enc (stMu s)).length
          + 4 * (enc (stD s)).length + 6 * (stOks s).length + Br + 14) + 6 * j := by
  classical
  set Bx : ℕ := ℓ * (6 * ((enc (stMu s)).length + (enc (stD s)).length) + 21) with hBx
  set Bx' : ℕ := max (enc (stX s)).length Bx with hBx'
  set Ψ : ℕ := 8 * (enc (stN s)).length + 4 * (enc (stA s)).length + 4 * Bx'
      + 4 * (enc (stT s)).length + 2 * (enc (stMu s)).length + 4 * (enc (stD s)).length
      + 6 * (stOks s).length + Br + 14 with hΨ
  have hMD : (enc (stMu s)).length + (enc (stD s)).length ≤ (enc s).length := by
    have h := enc_RSt_eq s
    omega
  have key : ∀ j : ℕ,
      stN ((QMCLeafB.RoundProgram.round^[j]) s) = stN s ∧
      stA ((QMCLeafB.RoundProgram.round^[j]) s) = stA s ∧
      stT ((QMCLeafB.RoundProgram.round^[j]) s) = stT s ∧
      stMu ((QMCLeafB.RoundProgram.round^[j]) s) = stMu s ∧
      stD ((QMCLeafB.RoundProgram.round^[j]) s) = stD s ∧
      (stX ((QMCLeafB.RoundProgram.round^[j]) s)).length ≤ ℓ ∧
      (∀ q ∈ stX ((QMCLeafB.RoundProgram.round^[j]) s), HasHeight q (enc s).length) ∧
      (enc (stX ((QMCLeafB.RoundProgram.round^[j]) s))).length ≤ Bx' ∧
      (enc (stRec ((QMCLeafB.RoundProgram.round^[j]) s))).length ≤ Br := by
    intro j
    induction j with
    | zero =>
        refine ⟨rfl, rfl, rfl, rfl, rfl, hX0, ?_, ?_, ?_⟩
        · intro q hq
          have h1 : HasHeight q (enc q).length := Ratio.height_length q
          have h2 : (enc q).length ≤ (enc (stX s)).length := list_entry_le hq
          have h3 : (enc (stX s)).length ≤ (enc s).length := enc_stX_le s
          exact HasHeight.mono h1 (by omega)
        · rw [hBx']; exact le_max_left _ _
        · exact hBr
    | succ j ih =>
        obtain ⟨i1, i2, i3, i4, i5, i6, i7, i8, i9⟩ := ih
        have hstep : (QMCLeafB.RoundProgram.round^[j + 1]) s
            = QMCLeafB.RoundProgram.round ((QMCLeafB.RoundProgram.round^[j]) s) :=
          Function.iterate_succ_apply' _ j s
        rw [hstep, QMCLeafB.RoundProgram.round_eq]
        split
        · -- the cut branch: a fresh snapped code and a fresh cut normal
          refine ⟨i1, i2, i3, i4, i5, ?_, ?_, ?_, ?_⟩
          · simp only [QMCLeafB.RoundProgram.roundCut, mkSt_stX]
            exact hsnap _ i6
          · intro q hq
            simp only [QMCLeafB.RoundProgram.roundCut, mkSt_stX] at hq
            unfold QMCLeafB.RoundProgram.snapY QMCLeafB.RoundProgram.nrmRow at hq
            obtain ⟨r, _, rfl⟩ := List.mem_map.mp hq
            have hmu : HasHeight (stMu ((QMCLeafB.RoundProgram.round^[j]) s))
                (enc (stMu s)).length := by
              have h4' : stMu ((QMCLeafB.RoundProgram.round^[j]) s) = stMu s := i4
              rw [h4']
              exact Ratio.height_length _
            have hdD : stD ((QMCLeafB.RoundProgram.round^[j]) s) ≤ 2 ^ (enc (stD s)).length := by
              have h5' : stD ((QMCLeafB.RoundProgram.round^[j]) s) = stD s := i5
              rw [h5']
              exact d_le_two_pow_enc _
            have := QMCLeafB.RoundProgram.hasHeight_nrmQ hmu hdD r
            exact HasHeight.mono this hMD
          · simp only [QMCLeafB.RoundProgram.roundCut, mkSt_stX]
            have h1 := enc_snapY_le ((QMCLeafB.RoundProgram.round^[j]) s)
              (enc (stMu s)).length (enc (stD s)).length
              (by
                have h4' : stMu ((QMCLeafB.RoundProgram.round^[j]) s) = stMu s := i4
                rw [h4']; exact Ratio.height_length _)
              (by
                have h5' : stD ((QMCLeafB.RoundProgram.round^[j]) s) = stD s := i5
                rw [h5']; exact d_le_two_pow_enc _)
            have h2 : (QMCLeafB.RoundProgram.snapY ((QMCLeafB.RoundProgram.round^[j]) s)).length
                ≤ ℓ := hsnap _ i6
            have h3 : (enc (QMCLeafB.RoundProgram.snapY
                ((QMCLeafB.RoundProgram.round^[j]) s))).length ≤ Bx := by
              rw [hBx]
              exact le_trans h1 (Nat.mul_le_mul_right _ h2)
            rw [hBx']
            exact le_trans h3 (le_max_right _ _)
          · simp only [QMCLeafB.RoundProgram.roundCut, mkSt_stRec]
            exact hc _ i7 i6
        · -- the ok branch: the state is frozen
          refine ⟨i1, i2, i3, i4, i5, i6, i7, i8, i9⟩
  intro j
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9⟩ := key j
  have hoks := stOks_iterate s j
  have hform := enc_RSt_eq ((QMCLeafB.RoundProgram.round^[j]) s)
  rw [h1, h2, h3, h4, h5] at hform
  have hoksenc : (enc (stOks ((QMCLeafB.RoundProgram.round^[j]) s))).length
      = 3 * (stOks s).length + 3 * j := by
    have h1 : (enc (stOks ((QMCLeafB.RoundProgram.round^[j]) s))).length
        = (encodeList (enc : Bool → List Bool) (stOks ((QMCLeafB.RoundProgram.round^[j]) s))).length :=
      rfl
    rw [h1, encodeList_bool_length, hoks]
    ring
  rw [hoksenc] at hform
  rw [hform]
  have h6 : 2 * (3 * (stOks s).length + 3 * j) = 6 * (stOks s).length + 6 * j := by ring
  rw [h6]
  rw [show 8 * (enc (stN s)).length + 4 * (enc (stA s)).length + 4 * Bx'
      + 4 * (enc (stT s)).length + 2 * (enc (stMu s)).length + 4 * (enc (stD s)).length
      + 6 * (stOks s).length + Br + 14 + 6 * j
      = Ψ + 6 * j from by rw [hΨ]]
  omega

/-- **The loop pair's growth, explicitly.**  With the ledger's `Ψ`, the visited loop states satisfy

    (encSt (round^[j] s, f.drop j)).length ≤ 2Ψ + 1 + 4 (enc f).length,

because the state grows by `6j` and the fuel tail pays `3j` of it back.  Every quantity on the right
is either a component of the initial state's encoding, `ℓ` (the primal code's length bound), or `Br`
(the oracle charge) — so a polynomial `sizes` dominating them closes the orbit size slot. -/
theorem pair_growth_RSt (s : RSt) (ℓ Br : ℕ)
    (hX0 : (stX s).length ≤ ℓ)
    (hsnap : ∀ t : RSt, (stX t).length ≤ ℓ → (QMCLeafB.RoundProgram.snapY t).length ≤ ℓ)
    (hc : ∀ (t : RSt), (∀ q ∈ stX t, HasHeight q (enc s).length) → (stX t).length ≤ ℓ →
      (enc (QMCLeafB.RoundProgram.oracleR t).2).length ≤ Br)
    (hBr : (enc (stRec s)).length ≤ Br) :
    ∀ (f : List Bool) (j : ℕ), j ≤ f.length →
      (QMCLeafB.SimPoly.encSt ((QMCLeafB.RoundProgram.round^[j]) s, f.drop j)).length
        ≤ 2 * (8 * (enc (stN s)).length + 4 * (enc (stA s)).length
            + 4 * (max (enc (stX s)).length
                (ℓ * (6 * ((enc (stMu s)).length + (enc (stD s)).length) + 21)))
            + 4 * (enc (stT s)).length + 2 * (enc (stMu s)).length
            + 4 * (enc (stD s)).length + 6 * (stOks s).length + Br + 14)
          + 1 + 4 * (enc f).length := by
  intro f j hj
  set P : ℕ := 8 * (enc (stN s)).length + 4 * (enc (stA s)).length
      + 4 * (max (enc (stX s)).length
          (ℓ * (6 * ((enc (stMu s)).length + (enc (stD s)).length) + 21)))
      + 4 * (enc (stT s)).length + 2 * (enc (stMu s)).length
      + 4 * (enc (stD s)).length + 6 * (stOks s).length + Br + 14 with hP
  have hstate := enc_iterate_le s ℓ Br hX0 hsnap hc hBr j
  rw [← hP] at hstate
  -- the fuel tail
  have hfuel : (enc (f.drop j)).length = (enc f).length - 3 * j := by
    have h1 : (enc (f.drop j)).length
        = (encodeList (enc : Bool → List Bool) (f.drop j)).length := rfl
    have h2 : (enc f).length = (encodeList (enc : Bool → List Bool) f).length := rfl
    rw [h1, h2, encodeList_bool_drop_length, encodeList_bool_length]
    exact Nat.mul_sub 3 f.length j
  have hfj : 3 * j ≤ (enc f).length := by
    have h2 : (enc f).length = 3 * f.length := encodeList_bool_length f
    omega
  have hsplit : (QMCLeafB.SimPoly.encSt ((QMCLeafB.RoundProgram.round^[j]) s, f.drop j)).length
      = 2 * (enc ((QMCLeafB.RoundProgram.round^[j]) s)).length + 1 + (enc (f.drop j)).length :=
    encodePair_length _ _ _
  rw [hsplit, hfuel]
  have step1 : 12 * j + ((enc f).length - 3 * j) = 9 * j + (enc f).length := by omega
  have step2 : 9 * j ≤ 3 * (enc f).length := by omega
  have step3 : 2 * (enc ((QMCLeafB.RoundProgram.round^[j]) s)).length ≤ 2 * P + 12 * j := by
    have h := Nat.mul_le_mul_left 2 hstate
    omega
  omega

/-- **The pair-level growth class at `RSt`, in monomial form.**  This is the hypothesis of
`orbit_of_pair_monomial` (§3), hence the size slot of `endgame_RSt_pair` (§4), reduced to three
explicit inputs: the primal code's length bound `ℓ`, the oracle charge `Br` (quadratic in the state's
own encoded length), and the two shape facts `hX0`/`hsnap`.  Every component of the state is bounded
by the initial encoded length `Ls`, so the constant is `1000`. -/
theorem pair_monomial_RSt (s : RSt) (ℓ Br : ℕ)
    (hX0 : (stX s).length ≤ ℓ)
    (hsnap : ∀ t : RSt, (stX t).length ≤ ℓ → (QMCLeafB.RoundProgram.snapY t).length ≤ ℓ)
    (hc : ∀ (t : RSt), (∀ q ∈ stX t, HasHeight q (enc s).length) → (stX t).length ≤ ℓ →
      (enc (QMCLeafB.RoundProgram.oracleR t).2).length ≤ Br)
    (hBr : (enc (stRec s)).length ≤ Br)
    (hℓ : ℓ ≤ (enc s).length + 1)
    (hBq : Br ≤ (enc s).length * (enc s).length + 1) :
    ∀ (f : List Bool) (j : ℕ), j ≤ f.length →
      (QMCLeafB.SimPoly.encSt ((QMCLeafB.RoundProgram.round^[j]) s, f.drop j)).length
        ≤ 1000 * ((QMCLeafB.SimPoly.encSt (s, f)).length + 1) ^ 2 := by
  intro f j hj
  have hmain := pair_growth_RSt s ℓ Br hX0 hsnap hc hBr f j hj
  set Ls : ℕ := (enc s).length with hLs
  set F : ℕ := (enc f).length with hF
  -- component bounds by `Ls`
  have h1 : (enc (stN s)).length ≤ Ls := by rw [hLs]; exact enc_stN_le s
  have h2 : (enc (stA s)).length ≤ Ls := by rw [hLs]; exact enc_stA_le s
  have h3 : (enc (stX s)).length ≤ Ls := by rw [hLs]; exact enc_stX_le s
  have h4 : (enc (stT s)).length ≤ Ls := by rw [hLs]; exact enc_stT_le s
  have h5 : (enc (stMu s)).length ≤ Ls := by rw [hLs]; exact enc_stMu_le s
  have h6 : (enc (stD s)).length ≤ Ls := by rw [hLs]; exact enc_stD_le s
  have h8 : Br ≤ Ls * Ls + 1 := by rw [hLs]; exact hBq
  -- the pair's own length
  have hpair : (QMCLeafB.SimPoly.encSt (s, f)).length = 2 * Ls + 1 + F := by
    rw [hLs, hF]
    exact encodePair_length _ _ _
  have hFL : F ≤ (QMCLeafB.SimPoly.encSt (s, f)).length := by rw [hpair]; omega
  have hLsL : Ls ≤ (QMCLeafB.SimPoly.encSt (s, f)).length := by rw [hpair]; omega
  -- the max term
  have hmax : (max (enc (stX s)).length
      (ℓ * (6 * ((enc (stMu s)).length + (enc (stD s)).length) + 21))) ≤ 21 * (Ls + 1) ^ 2 := by
    have hA : (enc (stX s)).length ≤ 21 * (Ls + 1) ^ 2 := by nlinarith
    have hB : ℓ * (6 * ((enc (stMu s)).length + (enc (stD s)).length) + 21)
        ≤ 21 * (Ls + 1) ^ 2 := by
      have h6' : 6 * ((enc (stMu s)).length + (enc (stD s)).length) + 21 ≤ 21 * (Ls + 1) := by
        omega
      have hmul : ℓ * (6 * ((enc (stMu s)).length + (enc (stD s)).length) + 21)
          ≤ (Ls + 1) * (21 * (Ls + 1)) := by
        have h1' : ℓ ≤ Ls + 1 := by rw [hLs]; exact hℓ
        exact Nat.mul_le_mul h1' h6'
      calc ℓ * (6 * ((enc (stMu s)).length + (enc (stD s)).length) + 21)
          ≤ (Ls + 1) * (21 * (Ls + 1)) := hmul
        _ = 21 * (Ls + 1) ^ 2 := by ring
    exact max_le hA hB
  have hPL : 8 * (enc (stN s)).length + 4 * (enc (stA s)).length
      + 4 * (max (enc (stX s)).length
          (ℓ * (6 * ((enc (stMu s)).length + (enc (stD s)).length) + 21)))
      + 4 * (enc (stT s)).length + 2 * (enc (stMu s)).length
      + 4 * (enc (stD s)).length + 6 * (stOks s).length + Br + 14
      ≤ 200 * (Ls + 1) ^ 2 := by
    have h7 : (stOks s).length ≤ Ls := by
      have := enc_stOks_le s
      rw [hLs]
      have : (enc (stOks s)).length = 3 * (stOks s).length := encodeList_bool_length _
      omega
    have h9 : 4 * (max (enc (stX s)).length
        (ℓ * (6 * ((enc (stMu s)).length + (enc (stD s)).length) + 21)))
        ≤ 84 * (Ls + 1) ^ 2 := by
      have := Nat.mul_le_mul_left 4 hmax
      calc 4 * (max (enc (stX s)).length
          (ℓ * (6 * ((enc (stMu s)).length + (enc (stD s)).length) + 21)))
          ≤ 4 * (21 * (Ls + 1) ^ 2) := this
        _ = 84 * (Ls + 1) ^ 2 := by ring
    have hsq : Ls * Ls + 1 ≤ (Ls + 1) ^ 2 := by nlinarith
    nlinarith [h1, h2, h3, h4, h5, h6, h7, h8, h9, hsq]
  have hRHS : 2 * (8 * (enc (stN s)).length + 4 * (enc (stA s)).length
      + 4 * (max (enc (stX s)).length
          (ℓ * (6 * ((enc (stMu s)).length + (enc (stD s)).length) + 21)))
      + 4 * (enc (stT s)).length + 2 * (enc (stMu s)).length
      + 4 * (enc (stD s)).length + 6 * (stOks s).length + Br + 14) + 1 + 4 * F
      ≤ 1000 * ((QMCLeafB.SimPoly.encSt (s, f)).length + 1) ^ 2 := by
    have hp1 : (QMCLeafB.SimPoly.encSt (s, f)).length + 1 = 2 * Ls + 2 + F := by
      rw [hpair]; omega
    nlinarith [hPL, hFL, hLsL, hp1, Nat.zero_le Ls]
  exact le_trans hmain hRHS

end QMCLeafB.SizeSlot

#print axioms QMCLeafB.SizeSlot.no_state_growth_class
#print axioms QMCLeafB.SizeSlot.orbit_of_pair_monomial
#print axioms QMCLeafB.SizeSlot.endgame_RSt_pair
#print axioms QMCLeafB.SizeSlot.horbit_of_step_le
#print axioms QMCLeafB.SizeSlot.enc_RSt_eq
#print axioms QMCLeafB.SizeSlot.enc_snapY_le
#print axioms QMCLeafB.SizeSlot.enc_iterate_le
#print axioms QMCLeafB.SizeSlot.pair_growth_RSt
#print axioms QMCLeafB.SizeSlot.pair_monomial_RSt

#print axioms QMCLeafB.SizeSlot.no_state_growth_class
#print axioms QMCLeafB.SizeSlot.orbit_of_pair_monomial
#print axioms QMCLeafB.SizeSlot.endgame_RSt_pair
#print axioms QMCLeafB.SizeSlot.horbit_of_step_le


