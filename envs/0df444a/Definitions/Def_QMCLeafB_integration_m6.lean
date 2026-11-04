-- Prove2me | Definitions.Def_QMCLeafB_integration_m6
-- name    : QMCLeafB_integration_m6
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-04T00:15:33.281494+00:00
-- url     : https://prove2.me/theorems/e853b34c-6cad-4d5c-950d-31d2e67e4c13
-- title:
--   QMCLeafB integration_m6
-- statement:
--   # leaf B phase 14 — brick `integration` (swarm `smw1a99tp`, member m6, direction d5)
--
--   Published as part of the QMCLeafB library mirror supporting the quantum max-cut campaign's polynomial-time SDP-value certificate (AGM20, TQC 2020, arXiv 2003.14394).

import Mathlib
import Definitions.Def_QMCLeafB_final_stroke_m7
import Definitions.Def_QMCLeafB_LoopRestate
import Definitions.Def_QMCLeafB_round_program_m3
import Definitions.Def_QMCLeafB_brick_verdict_sound
/-
# leaf B phase 14 — brick `integration` (swarm `smw1a99tp`, member m6, direction d5)

The closing stroke m7 shipped (`Check_final_reunion_m7.lean`, `endgame_orbit` /
`endgame_orbit_sq` / `endgame_RSt`) rests on the **orbit size slot**

    hmono : ∀ (s : σ) (j : ℕ), (enc (round^[j] s)).length ≤ C * ((enc s).length + 1) ^ k

(`QMCLeafB.FinalStroke.orbit_of_monomial_pow`).  That hypothesis is **not the shape the ledger
produces, and it is false for the round it is meant to feed**: every round of this engine *appends
one `ok` flag* to the state (`RoundProgram.roundCut`/`roundOk` both do `stOks s ++ [·]`), and in
`RSt`'s encoding a flag costs `6` bits (§2b proves it exactly: `enc_roundOk_eq`).  So
`(enc (round^[j] s)).length = (enc s).length + 6 * j` along an `ok`-branch orbit, which no
`C * ((enc s).length + 1) ^ k` dominates as `j → ∞`.  The cancellation that makes the loop
affordable is against the *fuel tail*
(`QMCLeafB.SimPoly.encSt (s, f) = 2·(enc s) + 1 + 3·|f|`), and that tail is simply not present in
`hmono`.

This file supplies the form the ledger actually proves, and the endgame on top of it:

* §1 length facts for the joint encoding `encSt` of a loop state — `3` bits per fuel bit, `6` bits
  per `ok` flag in `enc`, and the additive decomposition of `RSt`'s picture of a state.
* §2 **`iterate_length_le`** — from a *one-step* budget "the state either grows by the flag only
  (`+c`) or stays under a time-independent cap `M`" and `M (round s) = M s + c`, every iterate obeys
  `(enc (round^[j] s)).length ≤ max ((enc s).length) (M s) + c * j`.  Nothing is assumed about `j`:
  the bound is linear in `j` because the flag is the only unbounded field.
* §3 **`orbit_envelope`** — that linear orbit bound, composed with `M s ≤ C₀·((enc s).length + 1)³`
  (the one-time clip/snap enlarge of the `n²`-entry matrix code, a *single* step, not a per-round
  growth), gives the closing stroke's `horbit` slot at `sizesOrbitPow (C₀+c+2) 3`.  This is the
  hypothesis a dyadic-snap ledger discharges; `hmono` is not.
* §4 **`solution_of_bricks`** — `SolutionStatement` from the four bricks' outputs *in their provable
  shapes*: `init`/`fuel`/`round`/`verdict` as `Poly` programs, `horbit` (from §3), the interior
  `RunData` (`t < -Rq G/40000`) and the top-slice verdict `htop`.  It goes straight through
  `QMCLeafB.LoopRestate.solution_of_loop_bounded` and
  `QMCLeafB.VerdictSound.soundEpsOnBracket_of_runData_interior`, so neither of the broken ball forms
  (`hsize`/`hsize0`) nor the false `hmono` appears anywhere in the residual.

No `sorry`, no `axiom`, no `native_decide`, no `unsafe`.  Axiom audit at the end.
-/

set_option autoImplicit false

open scoped BigOperators
open Matrix
open OAI.MetricKMedian.Binary
open OAI.MetricKMedian.Binary.Automatic

namespace QMCLeafB.IntegrateM6

open QuantumMaxCutEnergy

/-- The request coding of the leaf, definitionally as in `Check_brick_finish_line`,
`Check_final_stroke_m7` and `Check_loop_restate`. -/
local instance instRequestCodingIntegrate : Coding (QuantumMaxCutEnergy.Input × List Bool) :=
  ⟨QuantumMaxCutEnergy.encodeRequest⟩

/-! ## 1.  Length facts for the encodings

`encodePair ea eb (a, b) = quote (ea a) ++ eb b` with `(quote w).length = 2·|w| + 1`, and
`encodeList ea (a :: as) = quote (ea a) ++ encodeList ea as`.  Hence a `Bool` in a list costs exactly
`3` bits (`encodeBool b = [b]`, one bit, quoted to `3`), and the fuel tail is a *linear* term of the
loop-state encoding — the term that pays for the per-round `ok` flag. -/

@[simp] theorem enc_list_length {α : Type} [Coding α] (l : List α) :
    (enc l).length = (encodeList (enc : α → List Bool) l).length := rfl

@[simp] theorem enc_prod_length {α β : Type} [Coding α] [Coding β] (a : α) (b : β) :
    (enc (a, b)).length = 2 * (enc a).length + 1 + (enc b).length :=
  encodePair_length (enc : α → List Bool) (enc : β → List Bool) (a, b)

theorem encodeList_bool_length (f : List Bool) :
    (encodeList (enc : Bool → List Bool) f).length = 3 * f.length := by
  induction f with
  | nil => rfl
  | cons a as ih =>
    rw [EncodedList.cons_length, ih, List.length_cons]
    have h1 : (enc a : List Bool).length = 1 := by
      cases a <;> rfl
    omega

theorem encSt_length {σ : Type} [Coding σ] (s : σ) (f : List Bool) :
    (QMCLeafB.SimPoly.encSt (s, f)).length = 2 * (enc s).length + 1 + 3 * f.length := by
  have h : (QMCLeafB.SimPoly.encSt (s, f)).length
      = 2 * (enc s).length + 1 + (encodeList (enc : Bool → List Bool) f).length :=
    encodePair_length (enc : σ → List Bool) (enc : List Bool → List Bool) (s, f)
  rw [h, encodeList_bool_length]

/-- A fuel list is never longer than the encoding of the loop state: the fuel tail contributes `3`
bits per bit. -/
theorem fuel_length_le_encSt {σ : Type} [Coding σ] (s : σ) (f : List Bool) :
    f.length ≤ (QMCLeafB.SimPoly.encSt (s, f)).length := by
  rw [encSt_length]
  omega

/-! ## 1b.  `RSt` as a sum of its parts

`RSt` is a nested product, so `enc` of it is a chain of `encodePair`s and the encoded length is a
linear combination of the parts — with the left-nested parts `quote`d once more per level.  Two facts
come out: the `ok` flag list `oks` enters with coefficient `6`, and `X`, `rec` can be split off
additively from the skeleton `n, A, t, mu, d`. -/

theorem enc_tuple_eq (n : ℕ) (A X : List ℚ) (t mu : ℚ) (d : ℕ) (oks : List Bool)
    (rec : List ℚ) :
    (enc (((n, A), (X, (t, mu))), ((d, oks), rec))).length
      = (enc (((n, A), (([] : List ℚ), (t, mu))), ((d, ([] : List Bool)), ([] : List ℚ)))).length
        + 4 * (encodeList (enc : ℚ → List Bool) X).length
        + 6 * oks.length
        + (encodeList (enc : ℚ → List Bool) rec).length := by
  simp [encodeList_bool_length, EncodedList.nil]
  ring

/-- **The `ok` branch appends exactly one flag and nothing else, and a flag costs `6` bits.** -/
theorem enc_roundOk_eq (n : ℕ) (A X : List ℚ) (t mu : ℚ) (d : ℕ) (oks : List Bool)
    (rec : List ℚ) :
    (enc (QMCLeafB.RoundProgram.roundOk
        (((n, A), (X, (t, mu))), ((d, oks), rec)))).length
      = (enc (((n, A), (X, (t, mu))), ((d, oks), rec))).length + 6 := by
  have hL := enc_tuple_eq n A X t mu d (oks ++ [true]) rec
  have hR := enc_tuple_eq n A X t mu d oks rec
  simp only [QMCLeafB.RoundProgram.roundOk, QMCLeafB.RoundProgram.mkSt,
    QMCLeafB.RoundProgram.stN, QMCLeafB.RoundProgram.stA, QMCLeafB.RoundProgram.stX,
    QMCLeafB.RoundProgram.stT, QMCLeafB.RoundProgram.stMu, QMCLeafB.RoundProgram.stD,
    QMCLeafB.RoundProgram.stOks, QMCLeafB.RoundProgram.stRec]
  rw [hL, hR, List.length_append]
  simp only [List.length_cons, List.length_nil]
  ring

/-! ## 2.  The orbit length bound: flag growth cancels against the fuel tail

The hypothesis set is exactly what a clip-and-snap ledger gives for a round that keeps `n²` matrix
entries and appends one flag of cost `c`:

* `hstep` — one round either grows the state's own encoding by at most the flag (`+c`) or lands
  inside a cap `M s` that does not depend on the round index,
* `hMinv` — the cap itself only moves with the flag (`M (round s) = M s + c`),

so the cap is `M s₀ + cj` along the orbit and the state's length grows at most linearly in `j`.  The
fuel tail of `encSt` shrinks by `3` per round, which is the linear term that pays for most of it. -/

theorem cap_iterate {σ : Type} [Coding σ] (round : σ → σ) (M : σ → ℕ) (c : ℕ)
    (hMinv : ∀ s, M (round s) ≤ M s + c) (s : σ) :
    ∀ j : ℕ, M (round^[j] s) ≤ M s + c * j := by
  intro j
  induction j with
  | zero => simp
  | succ k ih =>
    have hstep := hMinv (round^[k] s)
    rw [Function.iterate_succ_apply']
    have hcm : c * (k + 1) = c * k + c := by ring
    omega

/-- **Linear orbit bound for the state's own encoding.** -/
theorem iterate_length_le {σ : Type} [Coding σ] (round : σ → σ) (M : σ → ℕ) (c : ℕ)
    (hMinv : ∀ s, M (round s) ≤ M s + c)
    (hstep : ∀ s, (enc (round s)).length ≤ max ((enc s).length + c) (M s)) (s : σ) :
    ∀ j : ℕ, (enc (round^[j] s)).length ≤ max ((enc s).length) (M s) + c * j := by
  intro j
  induction j with
  | zero =>
    have h0 : (enc (round^[0] s)).length = (enc s).length := by simp
    omega
  | succ k ih =>
    have hcap := cap_iterate round M c hMinv s k
    have h1 : (enc (round^[k + 1] s)).length = (enc (round (round^[k] s))).length := by
      rw [Function.iterate_succ_apply']
    rw [h1]
    have h2 := hstep (round^[k] s)
    have h2' : (enc (round (round^[k] s))).length
        ≤ max ((enc (round^[k] s)).length + c) (M s + c * k) :=
      le_trans h2 (Nat.max_le.2 ⟨le_max_left _ _, le_trans hcap (le_max_right _ _)⟩)
    have h3 : (enc (round (round^[k] s))).length
        ≤ max ((enc s).length) (M s) + c * k + c := by
      rcases le_total ((enc (round^[k] s)).length + c) (M s + c * k) with hle | hle
      · rw [max_eq_right hle] at h2'; omega
      · rw [max_eq_left hle] at h2'; omega
    have h4 : c * (k + 1) = c * k + c := by ring
    omega

/-! ## 3.  The orbit envelope in the closing stroke's shape -/

/-- **The envelope's arithmetic, in isolation.**  A pure `ℕ` estimate: if the iterate grows at most
`max (enc s) (M s) + c * j` and the cap is a polynomial in the initial length, then the fuel-coupled
encoding of the visited state fits in `sizesOrbitPow (C₀+c+2) k`'s value.

The proof is a chain of monotone estimates with the monomial `P := (2L+1+3F+1)^k` as the single
nonlinear atom — deliberately no linear-arithmetic solver over products. -/
theorem arith_envelope (k b L F j c C₀ M : ℕ) (hk : 1 ≤ k) (hj : j ≤ F)
    (hb : b ≤ max L M + c * j) (hM : M ≤ C₀ * (L + 1) ^ k) :
    2 * b + 1 + 3 * (F - j) ≤ (2 * (C₀ + c + 2) + 2) * (2 * L + 1 + 3 * F + 1) ^ k := by
  have hX1 : 1 ≤ 2 * L + 1 + 3 * F + 1 := by omega
  have hXP : 2 * L + 1 + 3 * F + 1 ≤ (2 * L + 1 + 3 * F + 1) ^ k := by
    cases k with
    | zero => omega
    | succ m =>
      calc 2 * L + 1 + 3 * F + 1 = (2 * L + 1 + 3 * F + 1) * 1 := by ring
        _ ≤ (2 * L + 1 + 3 * F + 1) * (2 * L + 1 + 3 * F + 1) ^ m :=
            Nat.mul_le_mul_left _ (Nat.one_le_pow _ _ hX1)
        _ = (2 * L + 1 + 3 * F + 1) ^ (m + 1) := by ring
  set P := (2 * L + 1 + 3 * F + 1) ^ k with hP
  have hPP : 2 * L + 1 + 3 * F + 1 ≤ P := hXP
  have hLP : L ≤ P := by omega
  have hFP : F ≤ P := by omega
  have hL1P : (L + 1) ^ k ≤ P := by
    rw [hP]
    exact Nat.pow_le_pow_left (by omega) k
  have hmax : max L M ≤ L + M := by omega
  have hb1 : b ≤ L + M + c * j := le_trans hb (by omega)
  have hcj : c * j ≤ c * F := Nat.mul_le_mul_left c hj
  have hb2 : b ≤ L + C₀ * (L + 1) ^ k + c * F := by omega
  have hCP : C₀ * (L + 1) ^ k ≤ C₀ * P := Nat.mul_le_mul_left C₀ hL1P
  have hcP : c * F ≤ c * P := Nat.mul_le_mul_left c hFP
  have hbP : b ≤ P + C₀ * P + c * P := by omega
  have h2b : 2 * b ≤ 2 * P + 2 * (C₀ * P) + 2 * (c * P) := by
    have hh := Nat.mul_le_mul_left 2 hbP
    have e : 2 * (P + C₀ * P + c * P) = 2 * P + 2 * (C₀ * P) + 2 * (c * P) := by ring
    rw [e] at hh
    exact hh
  have h3Fj : 3 * (F - j) ≤ 3 * P :=
    le_trans (Nat.mul_le_mul_left 3 (Nat.sub_le F j)) (Nat.mul_le_mul_left 3 hFP)
  have hsum : 2 * b + 1 + 3 * (F - j) ≤ 2 * (C₀ * P) + 2 * (c * P) + 6 * P := by omega
  refine le_trans hsum ?_
  have e2 : 2 * (C₀ * P) + 2 * (c * P) + 6 * P = (2 * (C₀ + c + 2) + 2) * P := by ring
  exact le_of_eq e2

/-- **The closing stroke's orbit slot, in the shape the ledger proves.**

`hM` is the *one-time* enlarge of the `n²`-entry matrix code when a round clips to the rational box
`mu` and snaps to the grid `d` — one `O(L³)` step (`n²` entries, each of height at most
`(enc mu).length + (enc d).length`), not a per-round growth.  After it, every round is covered by the
cap, so the whole orbit fits in `sizesOrbitPow (C₀+c+2) 3`. -/
theorem orbit_envelope {σ : Type} [Coding σ] (round : σ → σ) (M : σ → ℕ) (C₀ c k : ℕ)
    (hk : 1 ≤ k)
    (hMinv : ∀ s, M (round s) ≤ M s + c)
    (hstep : ∀ s, (enc (round s)).length ≤ max ((enc s).length + c) (M s))
    (hM : ∀ s, M s ≤ C₀ * ((enc s).length + 1) ^ k) :
    ∀ (a : σ × List Bool) (j : ℕ), j ≤ a.2.length →
      (QMCLeafB.SimPoly.encSt (round^[j] a.1, a.2.drop j)).length
        ≤ (QMCLeafB.FinalStroke.sizesOrbitPow (C₀ + c + 2) k).eval
            (QMCLeafB.SimPoly.encSt a).length := by
  intro a j hj
  have haj := iterate_length_le round M c hMinv hstep a.1 j
  have hcap := hM a.1
  have hLHS : (QMCLeafB.SimPoly.encSt (round^[j] a.1, a.2.drop j)).length
      = 2 * (enc (round^[j] a.1)).length + 1 + 3 * ((a.2.drop j).length) :=
    encSt_length _ _
  have hJ : (QMCLeafB.SimPoly.encSt a).length
      = 2 * (enc a.1).length + 1 + 3 * a.2.length := encSt_length _ _
  rw [hLHS, QMCLeafB.FinalStroke.sizesOrbitPow_eval, hJ, List.length_drop]
  exact arith_envelope k _ _ _ j c C₀ (M a.1) hk hj haj hcap

/-! ## 4.  The endgame on the provable size slot

Slot-for-slot `QMCLeafB.LoopRestate.solution_of_loop_bounded`, but with the run only on the interior
of the bracket (`RunData` on `t < -Rq G/40000`) and the top slice paid by `htop` — exactly the
residual the brief asks for.  Nothing here mentions `hsize`, `hsize0` or `hmono`. -/
theorem solution_of_bricks {σ : Type} [Coding σ]
    (init : ((QuantumMaxCutEnergy.Input × List Bool) × ℚ) → σ)
    (fuel : ((QuantumMaxCutEnergy.Input × List Bool) × ℚ) → List Bool)
    (round : σ → σ) (verdict : σ → Bool)
    (hinit : Automatic.Poly init) (hfuel : Automatic.Poly fuel)
    (hr : Automatic.Poly round) (hv : Automatic.Poly verdict)
    (M : σ → ℕ) (C₀ c k : ℕ) (hk : 1 ≤ k)
    (hMinv : ∀ s, M (round s) ≤ M s + c)
    (hstep : ∀ s, (enc (round s)).length ≤ max ((enc s).length + c) (M s))
    (hM : ∀ s, M s ≤ C₀ * ((enc s).length + 1) ^ k)
    (K : QuantumMaxCutEnergy.Input → ℕ)
    (hinitTape : ∀ p : ((QuantumMaxCutEnergy.Input × List Bool) × ℚ),
      init p = init (QMCLeafB.FinalStroke.noTape p.1.1 p.2))
    (hfuelLen : ∀ p : ((QuantumMaxCutEnergy.Input × List Bool) × ℚ),
      (fuel p).length = K p.1.1)
    (htop : ∀ (G : QuantumMaxCutEnergy.Input) (t : ℚ),
      -(((QMCLeafB.EngineRuntime.Rq G / 40000 : ℚ)) : ℝ) ≤ (t : ℝ) → t ≤ 0 →
      QMCLeafB.FinalStroke.loopBit init round verdict
        (fun G' _ => K G') G t = true)
    (hd : ∀ (G : QuantumMaxCutEnergy.Input) (t : ℚ), 2 ≤ G.n →
      -QMCLeafB.EngineRuntime.Rq G ≤ t →
      (t : ℝ) < -(((QMCLeafB.EngineRuntime.Rq G / 40000 : ℚ)) : ℝ) →
      QMCLeafB.VerdictSound.RunData
        (QMCLeafB.FinalStroke.loopBit init round verdict (fun G' _ => K G')) G t) :
    QMCLeafB.FinishLine.SolutionStatement :=
  QMCLeafB.LoopRestate.solution_of_loop_bounded init fuel round verdict
    hinit hfuel hr hv
    (QMCLeafB.FinalStroke.sizesOrbitPow (C₀ + c + 2) k)
    (orbit_envelope round M C₀ c k hk hMinv hstep hM)
    (QMCLeafB.FinalStroke.loopBit init round verdict (fun G' _ => K G'))
    (QMCLeafB.FinalStroke.hspec_of_tape_free init fuel round verdict (fun G' _ => K G')
      hinitTape hfuelLen)
    (QMCLeafB.VerdictSound.soundEpsOnBracket_of_runData_interior
      (QMCLeafB.FinalStroke.loopBit init round verdict (fun G' _ => K G')) htop
      (fun G t hn hlo hhi => hd G t (by omega) hlo hhi))


/-! ## 4b.  The concrete instance at m3's `RoundProgram.RSt` (and at `InitVerdict.St`)

The same endgame with `σ`, `round` and `verdict` filled in by m3's round program (whose
`poly_round`, `poly_verdict` are proved in `Check_round_program_m3`), the numeric half by
`FinalStroke.runParamsOfK`, and the fuel length `K * m` — i.e. a drop-in replacement for
`QMCLeafB.FinalReunion.endgame_RSt` in which the unusable `hmono` slot is replaced by the one-step
ledger `(hMinv, hstep, hM)` of §2–§3, and `RunParts` is consumed on the interior
`t < -Rq G/40000` through `RunParts.toRunData`. -/
theorem endgame_RSt_ledger
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
    (init0 : ((QuantumMaxCutEnergy.Input × List Bool) × ℚ) → QMCLeafB.RoundProgram.RSt)
    (hinit0 : Automatic.Poly init0)
    (hinitTape : ∀ p : ((QuantumMaxCutEnergy.Input × List Bool) × ℚ),
      init0 p = init0 (QMCLeafB.FinalStroke.noTape p.1.1 p.2))
    (fuel : ((QuantumMaxCutEnergy.Input × List Bool) × ℚ) → List Bool)
    (hfuel : Automatic.Poly fuel)
    (hfuelLen : ∀ p : ((QuantumMaxCutEnergy.Input × List Bool) × ℚ),
      (fuel p).length = K p.1.1 * m p.1.1)
    (M : QMCLeafB.RoundProgram.RSt → ℕ) (C₀ c k : ℕ) (hk : 1 ≤ k)
    (hMinv : ∀ s, M (QMCLeafB.RoundProgram.round s) ≤ M s + c)
    (hstep : ∀ s, (enc (QMCLeafB.RoundProgram.round s)).length
      ≤ max ((enc s).length + c) (M s))
    (hM : ∀ s, M s ≤ C₀ * ((enc s).length + 1) ^ k)
    (htop : ∀ (G : QuantumMaxCutEnergy.Input) (t : ℚ),
      -(((QMCLeafB.EngineRuntime.Rq G / 40000 : ℚ)) : ℝ) ≤ (t : ℝ) → t ≤ 0 →
      QMCLeafB.FinalStroke.loopBit init0 QMCLeafB.RoundProgram.round
        QMCLeafB.RoundProgram.verdict (fun G' _ => K G' * m G') G t = true)
    (hd : ∀ (G : QuantumMaxCutEnergy.Input) (t : ℚ), 2 ≤ G.n →
      -QMCLeafB.EngineRuntime.Rq G ≤ t →
      (t : ℝ) < -(((QMCLeafB.EngineRuntime.Rq G / 40000 : ℚ)) : ℝ) →
      QMCLeafB.FinalStroke.RunParts
        (QMCLeafB.FinalStroke.loopBit init0 QMCLeafB.RoundProgram.round
          QMCLeafB.RoundProgram.verdict (fun G' _ => K G' * m G')) G t
        (QMCLeafB.FinalStroke.runParamsOfK G (dq G) (hdq G) (rmax G) (hrmax G) (m G) (hm1 G)
          (K G) (hK G) (hhalve G))) :
    QMCLeafB.FinishLine.SolutionStatement :=
  solution_of_bricks init0 fuel QMCLeafB.RoundProgram.round QMCLeafB.RoundProgram.verdict
    hinit0 hfuel QMCLeafB.RoundProgram.poly_round QMCLeafB.RoundProgram.poly_verdict
    M C₀ c k hk hMinv hstep hM
    (fun G => K G * m G) hinitTape hfuelLen htop
    (fun G t hn hlo hhi => (hd G t hn hlo hhi).toRunData)

end QMCLeafB.IntegrateM6

#print axioms QMCLeafB.IntegrateM6.encodeList_bool_length
#print axioms QMCLeafB.IntegrateM6.encSt_length
#print axioms QMCLeafB.IntegrateM6.enc_roundOk_eq
#print axioms QMCLeafB.IntegrateM6.iterate_length_le
#print axioms QMCLeafB.IntegrateM6.arith_envelope
#print axioms QMCLeafB.IntegrateM6.orbit_envelope
#print axioms QMCLeafB.IntegrateM6.solution_of_bricks
#print axioms QMCLeafB.IntegrateM6.endgame_RSt_ledger


