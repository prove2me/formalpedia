-- Prove2me | Definitions.Def_QMCLeafB_fal30
-- name    : QMCLeafB_fal30
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-04T13:49:00.130421+00:00
-- url     : https://prove2.me/theorems/939be680-9dfb-489b-9901-ceef07e1ff9f
-- title:
--   QMCLeafB fal30
-- statement:
--   # `Check_fal30_m4` — phase 30, member m4, direction d7 (`falsify30`)
--
--   Published as part of the QMCLeafB library mirror supporting the quantum max-cut campaign's polynomial-time SDP-value certificate (AGM20, TQC 2020, arXiv 2003.14394).

import Mathlib
import Definitions.Def_QMCLeafB_unionShallow
import Definitions.Def_QMCLeafB_audit25
/-
# `Check_fal30_m4` — phase 30, member m4, direction d7 (`falsify30`)

Attacks on the six inputs of `Solutions/solution_m1.lean` (the submission template), each with a
machine-checked receipt.  Nothing here rebuilds a dead lane: the targets are the three claims the
template's residual actually leans on.

## §A — input (2), the size ledger `M C₀ c kr`

* `ledger_of_step_le`: the ledger is **not a residual**.  A one-step length bound
  `(enc (round s)).length ≤ (enc s).length + c` *produces* a ledger, with `M s := (enc s).length`,
  `C₀ := 1`, `kr := 1`.  (`hM` is then free, `hstep` is the same fact, `hMinv` is the same fact.)
* `solution_of_step_le`: the template's own stroke with the ledger hypothesis **replaced** by that
  one-step bound — the reduced six-input set (five inputs plus one inequality).
* `not_ledger_monomial`: the tempting cap `M s := C₀ · ((enc s).length + 1)^kr` (`kr ≥ 2`) is
  **inconsistent** with `hMinv` for a round whose encoding grows at states of unbounded length.
  This is a real trap: the campaign's own notes quote `C₀·((enc s).length+1)^3`.  The working
  choice is the *linear* one, so the state code must be a fixed-length pack (as the campaign's
  `RSt` packing is), not a per-round accumulator.

## §B — input (1)/(5), the ok test's tolerance conventions

The `ok` flag must be `RelaxOracle.RelaxMem A cX (t − eps) δ` at `δ = dq`, because that is what
`hcert` consumes (`relaxMem_witness` + the banked rounding budget).  Receipts:

* `grid_iff`: the certified test's grid hypothesis is exactly `d ≥ 2n²/δ`;
* `relaxBodyLE_mono`: the body is monotone in `δ` (so the tolerance must *not* be tightened);
* `budget_at_dq` : the banked campaign budget, at `δ = paramsKbc2.dq`;
* `hcert_from_relaxMem` : `RelaxMem` at `(t − eps, dqShallow)` **gives** `RunParts.hcert`'s witness.
  Consequence for the brief: the coherent pair is (margin coefficient `dq/2`, grid `2n²/dq`); the
  pair (margin `dq/4`, grid `4n²/dq`) is the same statements at `δ = dq/2` and *shrinks the body* by
  `dq/4` — sound, but strictly dominated.

## §C — input (4)/(5), the bit's boundary at an attainer (the `raiseFloor` trap)

`raiseFloor G = −Rq G + Rq G/40000`.  The banked sharpness (`BracketM2.clamp_above_raise_unsound`)
says a *clamp* above that floor is unsound.  Here is the same content with no clamp at all, i.e. as
a constraint on the constructed program: **at any input carrying a unit-diagonal PSD point of value
`−Rq G`, a sound bit must read `true` at every `t > raiseFloor G`**; so any program whose ok test
can fail there is dead at `hd`'s own interface (`hd` ⟹ `SoundAt`).
-/

open scoped BigOperators
open Matrix
open OAI.MetricKMedian.Binary
open OAI.MetricKMedian.Binary.Automatic

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option linter.unusedVariables false

noncomputable section

namespace QMCLeafB.Fal30

open QuantumMaxCutEnergy

local instance instRequestCodingFal : Coding (QuantumMaxCutEnergy.Input × List Bool) :=
  ⟨QuantumMaxCutEnergy.encodeRequest⟩

/-! ## §A.  The size ledger is a one-step length bound -/

/-- **The ledger, produced from a one-step length bound.**  `M s := (enc s).length`, `C₀ := 1`,
`kr := 1`: then `hMinv` and `hstep` are the bound itself and `hM` is `L ≤ L + 1`.  So the template's
ledger slot is *not* a residual once the round is length-additive with a constant, which is exactly
what a fixed-length packed code gives. -/
theorem ledger_of_step_le {σ : Type} [Coding σ] (round : σ → σ) (c : ℕ)
    (h : ∀ s : σ, (enc (round s)).length ≤ (enc s).length + c) :
    ∃ (M : σ → ℕ) (C₀ kr : ℕ), 1 ≤ kr ∧ (∀ s, M (round s) ≤ M s + c) ∧
      (∀ s, (enc (round s)).length ≤ max ((enc s).length + c) (M s)) ∧
      (∀ s, M s ≤ C₀ * ((enc s).length + 1) ^ kr) :=
  ⟨fun s => (enc s).length, 1, 1, le_refl 1, h,
    fun s => le_trans (h s) (le_max_left _ _), fun s => by simp⟩

#print axioms QMCLeafB.Fal30.ledger_of_step_le

/-- The gap `(L+2)^k − (L+1)^k` is at least `2L+3` for `k ≥ 2`.  Proved on the difference, which
grows by the factor `L+1` each step, so no binomial theorem is needed. -/
theorem pow_gap_ge (L : ℕ) : ∀ kr : ℕ, 2 ≤ kr → (L + 1) ^ kr + (2 * L + 3) ≤ (L + 2) ^ kr := by
  intro kr hkr
  obtain ⟨j, rfl⟩ : ∃ j, kr = j + 2 := ⟨kr - 2, by omega⟩
  clear hkr
  induction j with
  | zero =>
    show (L + 1) ^ (0 + 2) + (2 * L + 3) ≤ (L + 2) ^ (0 + 2)
    have e : (L + 2) ^ 2 = (L + 1) ^ 2 + (2 * L + 3) := by ring
    rw [e]
  | succ i ih =>
    show (L + 1) ^ (i + 1 + 2) + (2 * L + 3) ≤ (L + 2) ^ (i + 1 + 2)
    have h1 : (L + 2) ^ (i + 1 + 2) = (L + 2) ^ (i + 2) * (L + 2) := by ring
    have h2 : (L + 1) ^ (i + 1 + 2) = (L + 1) ^ (i + 2) * (L + 1) := by ring
    rw [h1, h2]
    set A := (L + 1) ^ (i + 2) with hA
    set B := (L + 2) ^ (i + 2) with hB
    have hBle : A + (2 * L + 3) ≤ B := ih
    have hmul : (A + (2 * L + 3)) * (L + 2) ≤ B * (L + 2) := Nat.mul_le_mul_right _ hBle
    have hsplit : (A + (2 * L + 3)) * (L + 2) = A * (L + 1) + A + (2 * L + 3) * (L + 2) := by
      ring
    have hK : 2 * L + 3 ≤ (2 * L + 3) * (L + 2) :=
      Nat.le_mul_of_pos_right _ (by omega)
    have hA0 : 0 ≤ A := Nat.zero_le _
    omega

#print axioms QMCLeafB.Fal30.pow_gap_ge

/-- **The natural monomial cap is dead.**  If the round's encoding grows by at least one symbol at
every state, and states of every encoded length exist, then no `M s := C₀ * ((enc s).length + 1)^kr`
with `kr ≥ 2` and `C₀ ≥ 1` satisfies `hMinv`.  (So `hM`'s `(enc s).length + 1)^3`-shape, as quoted in
the campaign notes, cannot carry a round that appends to the code: the ledger's `M` must be linear in
the length, i.e. `M s = (enc s).length`.) -/
theorem not_ledger_monomial {σ : Type} [Coding σ] (round : σ → σ)
    (hinf : ∀ L : ℕ, ∃ s : σ, L ≤ (enc s).length)
    (hgrowth : ∀ s : σ, (enc s).length + 1 ≤ (enc (round s)).length)
    (C₀ c : ℕ) (hC₀ : 1 ≤ C₀) (kr : ℕ) (hkr : 2 ≤ kr) :
    ¬ (∀ s : σ, C₀ * ((enc (round s)).length + 1) ^ kr ≤ C₀ * ((enc s).length + 1) ^ kr + c) := by
  intro hMinv
  obtain ⟨s, hs⟩ := hinf (c + 1)
  have hg := hgrowth s
  have hm := hMinv s
  set L := (enc s).length with hL
  have hLc : c + 1 ≤ L := hs
  have hgap := pow_gap_ge L kr hkr
  have hstep1 : C₀ * ((enc (round s)).length + 1) ^ kr
      ≥ C₀ * ((L + 1) + 1) ^ kr := by
    refine Nat.mul_le_mul_left _ ?_
    exact Nat.pow_le_pow_left (by omega) kr
  have hstep2 : C₀ * ((L + 1) + 1) ^ kr ≥ C₀ * ((L + 1) ^ kr + (2 * L + 3)) :=
    Nat.mul_le_mul_left _ hgap
  have hexp : C₀ * ((L + 1) ^ kr + (2 * L + 3))
      = C₀ * (L + 1) ^ kr + C₀ * (2 * L + 3) := by ring
  have hC0gap : 2 * L + 3 ≤ C₀ * (2 * L + 3) := by
    calc 2 * L + 3 = 1 * (2 * L + 3) := by ring
      _ ≤ C₀ * (2 * L + 3) := Nat.mul_le_mul_right _ hC₀
  omega

#print axioms QMCLeafB.Fal30.not_ledger_monomial

/-! ## §B.  The tolerance conventions of the ok test -/

/-- **The certified test's grid, exactly.**  `pivPsdMargin_of_tolerance`'s hypothesis
`2·n² ≤ δ·d` is the same inequality as `2n²/δ ≤ d`: so at the margin coefficient `δ/2` the grid must
be at least `2n²/δ`, and at `δ/2` (a tighter margin) `4n²/δ`. -/
theorem grid_iff {n d : ℕ} {δ : ℚ} (hd : 0 < d) (hδ : 0 < δ) :
    (2 * (n : ℚ) * (n : ℚ) ≤ δ * (d : ℚ)) ↔ (2 * (n : ℚ) * (n : ℚ) / δ ≤ (d : ℚ)) := by
  have hd' : (0 : ℚ) < (d : ℚ) := by exact_mod_cast hd
  rw [div_le_iff₀ hδ]
  constructor <;> intro h
  · linarith
  · linarith

#print axioms QMCLeafB.Fal30.grid_iff

/-- **The relaxed body is monotone in the tolerance.**  All three clauses weaken as `δ` grows, so
tightening `δ` only ever shrinks the set the ok test has to hit — the reason the coherent choice is
the *largest* `δ` the rounding budget allows (`δ = dq`, not `dq/2`). -/
theorem relaxBodyLE_mono {n : ℕ} {A : Matrix (Fin n) (Fin n) ℝ} {u δ δ' : ℝ}
    (hle : δ ≤ δ') {X : Matrix (Fin n) (Fin n) ℝ}
    (h : QMCLeafB.BallFloor.relaxBodyLE A u δ X) :
    QMCLeafB.BallFloor.relaxBodyLE A u δ' X := by
  obtain ⟨h1, h2, h3⟩ := h
  refine ⟨?_, ?_, ?_⟩
  · intro x
    have hnn : (0 : ℝ) ≤ ∑ i, x i ^ 2 := Finset.sum_nonneg fun i _ => sq_nonneg _
    have h2 : δ / 2 ≤ δ' / 2 := by linarith
    have hmul := mul_le_mul_of_nonneg_right h2 hnn
    have hmono : -(δ' / 2) * (∑ i, x i ^ 2) ≤ -(δ / 2) * (∑ i, x i ^ 2) := by linarith
    linarith [h1 x]
  · intro i
    have := h2 i
    have h4 : δ / 4 ≤ δ' / 4 := by linarith
    linarith
  · linarith

#print axioms QMCLeafB.Fal30.relaxBodyLE_mono

/-- **The banked rounding budget, in §B's coordinates**: at `δ = paramsKbc2.dq` (that is
`dqShallow G`), one `RelaxMem` at the loop's centre still fits inside half the leaf's slack. -/
theorem budget_at_dq (G : QuantumMaxCutEnergy.Input) (hn : 2 ≤ G.n)
    (hRq : 0 < QMCLeafB.EngineRuntime.Rq G) :
    QMCLeafB.RoundingOut.roundCost (QMCLeafB.Finalization.wMatrixQ G)
        (3 * QMCLeafB.RundataParams.dqShallow G / 4)
      + QMCLeafB.RundataParams.dqShallow G / 2 - QMCLeafB.RundataCert.eps G
      ≤ QMCLeafB.RundataCert.eps G := by
  have h := QMCLeafB.UnionShallow.paramsKbc2_budget G hn hRq
  rwa [QMCLeafB.UnionShallow.paramsKbc2_dq] at h

#print axioms QMCLeafB.Fal30.budget_at_dq

/-! ## §C.  The bit's boundary at an attainer: `raiseFloor` is a *lower* bound on the ok region -/

/-- **`SoundAt` forces the bit true above the raised floor at an attainer.**  If `Z` is a
unit-diagonal PSD point of value exactly `−Rq G` (the trace floor, attained — e.g. at `G₁`), then at
any `t` with `t − eps G > −Rq G` the refuting clause of `SoundAt` fails, so the bit cannot read
`false`.  With `raiseFloor G = −Rq G + eps G` this is: `o` is `true` on `(raiseFloor G, 0]`.

No clamp appears: this is a constraint on the program's own ok region, and it is the reason the
phase-26 "raise the floor and clamp" repair cannot be pushed past `raiseFloor`. -/
theorem bit_true_of_attainer (o : QuantumMaxCutEnergy.Input → ℚ → Bool)
    (G : QuantumMaxCutEnergy.Input) (t : ℚ)
    (Z : Matrix (Fin G.n) (Fin G.n) ℝ) (hZ : ModernConvex.Relaxations.IsUnitDiagPSD Z)
    (hZt : (QMCLeafB.wMatrix G * Z).trace = -((QMCLeafB.EngineRuntime.Rq G : ℚ) : ℝ))
    (ht : -((QMCLeafB.EngineRuntime.Rq G : ℚ) : ℝ)
      + ((QMCLeafB.EngineRuntime.Rq G / 40000 : ℚ) : ℝ) < (t : ℝ))
    (hs : QMCLeafB.VerdictSound.SoundAt o G t) :
    o G t = true := by
  cases hb : o G t with
  | false =>
    exfalso
    have h := hs.2 hb Z hZ
    rw [hZt] at h
    linarith
  | true => rfl

#print axioms QMCLeafB.Fal30.bit_true_of_attainer

/-- **The same at the template's own interface**: one `RunParts` at the program's bit (which is what
`hd` supplies) already carries `SoundAt`, so the template's run slot forces the ok region to contain
`(raiseFloor G, 0]` at every floor-attaining input.  A program whose ok test fails there cannot be
given `hd` at all. -/
theorem bit_true_of_runParts_of_attainer
    {o : QuantumMaxCutEnergy.Input → ℚ → Bool}
    {G : QuantumMaxCutEnergy.Input} {t : ℚ}
    {P : QMCLeafB.FinalStroke.RunParams G}
    (hn : 2 ≤ G.n) (d : QMCLeafB.FinalStroke.RunParts o G t P)
    (Z : Matrix (Fin G.n) (Fin G.n) ℝ) (hZ : ModernConvex.Relaxations.IsUnitDiagPSD Z)
    (hZt : (QMCLeafB.wMatrix G * Z).trace = -((QMCLeafB.EngineRuntime.Rq G : ℚ) : ℝ))
    (ht : -((QMCLeafB.EngineRuntime.Rq G : ℚ) : ℝ)
      + ((QMCLeafB.EngineRuntime.Rq G / 40000 : ℚ) : ℝ) < (t : ℝ)) :
    o G t = true :=
  bit_true_of_attainer o G t Z hZ hZt ht
    (QMCLeafB.VerdictSound.soundAt_of_runData o G t hn d.toRunData)

#print axioms QMCLeafB.Fal30.bit_true_of_runParts_of_attainer

/-! ## §B (continued).  The ok test's soundness: `RelaxMem` at `δ = dq` gives `hcert`'s witness -/

/-- **`ok`-soundness, composed.**  One `RelaxMem` at the loop's own centre, at the loop's slack
`u = t − eps G` and the campaign tolerance `δ = dqShallow G`, produces exactly the witness
`RunParts.hcert` asks for: a genuine unit-diagonal PSD point at `t + eps G`.  The rounding cost is
`roundCost A (3δ/4)` (`RelaxOracle.relaxMem_witness`) and it fits inside the slack by the banked
`paramsKbc2_budget`.

So the program's `ok` flag needs to mean *this* `RelaxMem` (PSD margin `δ/2`, diagonal `δ/4`,
objective `u + δ/2`) — not a bare exact-PSD test, and not a tighter `δ/2`: the tighter tolerance is
the same statement with a body shrunk by `δ/4` (`relaxBodyLE_mono`). -/
theorem hcert_from_relaxMem (G : QuantumMaxCutEnergy.Input) (t : ℚ)
    (cX : Matrix (Fin G.n) (Fin G.n) ℚ)
    (hn : 2 ≤ G.n) (hRq : 0 < QMCLeafB.EngineRuntime.Rq G) (hCsym : cXᵀ = cX)
    (h : QMCLeafB.RelaxOracle.RelaxMem (QMCLeafB.Finalization.wMatrixQ G) cX
      (t - QMCLeafB.RundataCert.eps G) (QMCLeafB.RundataParams.dqShallow G)) :
    ∃ X : Matrix (Fin G.n) (Fin G.n) ℝ,
      QMCLeafB.AnswerProducer.IsUnitDiagPSD X ∧
        (QMCLeafB.wMatrix G * X).trace
          ≤ (t : ℝ) + ((QMCLeafB.RundataCert.eps G : ℚ) : ℝ) := by
  obtain ⟨X, hX, htr⟩ :=
    QMCLeafB.RelaxOracle.relaxMem_witness (A := QMCLeafB.Finalization.wMatrixQ G) (cX := cX)
      (u := t - QMCLeafB.RundataCert.eps G) (δ := QMCLeafB.RundataParams.dqShallow G) h
      (QMCLeafB.Finalization.IsQMCWeight.symm
        (QMCLeafB.Finalization.isQMCWeight_wMatrixQ G)) hCsym
      (fun i => QMCLeafB.Finalization.wMatrixQ_apply_of_eq)
  refine ⟨X, hX, ?_⟩
  rw [QMCLeafB.Finalization.wMatrix_castM] at htr
  have hbud := budget_at_dq G hn hRq
  have hq : t - QMCLeafB.RundataCert.eps G + QMCLeafB.RundataParams.dqShallow G / 2
      + QMCLeafB.RoundingOut.roundCost (QMCLeafB.Finalization.wMatrixQ G)
          (3 * QMCLeafB.RundataParams.dqShallow G / 4)
      ≤ t + QMCLeafB.RundataCert.eps G := by linarith
  have hr : (((t - QMCLeafB.RundataCert.eps G + QMCLeafB.RundataParams.dqShallow G / 2
      + QMCLeafB.RoundingOut.roundCost (QMCLeafB.Finalization.wMatrixQ G)
          (3 * QMCLeafB.RundataParams.dqShallow G / 4) : ℚ)) : ℝ)
      ≤ (t : ℝ) + ((QMCLeafB.RundataCert.eps G : ℚ) : ℝ) := by
    exact_mod_cast hq
  linarith

#print axioms QMCLeafB.Fal30.hcert_from_relaxMem

/-- **`SoundAt` forces the bit true above `eps G`** — with no attainer needed, the identity is
unit-diagonal semidefinite of value `0`.  So the template's `htop` slice `[−Rq/40000, 0]` is not a
design choice: any bit that is sound at all is already true on `(eps G, 0]`. -/
theorem bit_true_of_eps_lt (o : QuantumMaxCutEnergy.Input → ℚ → Bool)
    (G : QuantumMaxCutEnergy.Input) (t : ℚ)
    (ht : ((QMCLeafB.EngineRuntime.Rq G / 40000 : ℚ) : ℝ) < (t : ℝ))
    (hs : QMCLeafB.VerdictSound.SoundAt o G t) :
    o G t = true := by
  cases hb : o G t with
  | false =>
    exfalso
    have h := hs.2 hb (1 : Matrix (Fin G.n) (Fin G.n) ℝ) QMCLeafB.AnswerProducer.isUnitDiagPSD_one
    rw [QMCLeafB.FinishLine.one_trace_eq_zero] at h
    linarith
  | true => rfl

#print axioms QMCLeafB.Fal30.bit_true_of_eps_lt

/-! ## §A (continued).  The template with the ledger **replaced** by the one-step length bound -/

/-- The campaign's round count, as in the template. -/
abbrev Tbc2 : QuantumMaxCutEnergy.Input → ℚ → ℕ :=
  fun G' _ => QMCLeafB.UnionShallow.Kbc2 (QMCLeafB.HalvePerG.mHalve (G'.n * G'.n)) G'
    * QMCLeafB.HalvePerG.mHalve (G'.n * G'.n)

/-- **The submission stroke with the ledger hypothesis deleted.**  Same conclusion, same five other
inputs, but instead of `(M, C₀, c, kr, hkr, hMinv, hstep, hM)` only the one-step length bound
`(enc (round s)).length ≤ (enc s).length + c` for a single `c : ℕ`.  So input (2) of the six is
*discharged* by §A's `ledger_of_step_le`: the residual ledger content is that inequality, i.e. that
the round adds at most `c` symbols to the packed state's code (a fixed-length pack gives `c = 0`, the
campaign's own `RSt` with one appended ok flag gives `c = 6`). -/
theorem solution_of_step_le {σ : Type} [Coding σ]
    (k : ℕ) (hk : 20 ≤ 2 ^ k)
    (init : QMCLeafB.FuelWire.Pkg → σ) (round : σ → σ) (verdict : σ → Bool)
    (hinit : Automatic.Poly init) (hr : Automatic.Poly round) (hv : Automatic.Poly verdict)
    (c : ℕ)
    (hstepLen : ∀ s : σ, (enc (round s)).length ≤ (enc s).length + c)
    (hinitTape : ∀ p : QMCLeafB.FuelWire.Pkg,
      init p = init (QMCLeafB.FinalStroke.noTape p.1.1 p.2))
    (htop : ∀ (G : QuantumMaxCutEnergy.Input) (t : ℚ), 2 ≤ G.n →
      -(((QMCLeafB.EngineRuntime.Rq G / 40000 : ℚ)) : ℝ) ≤ (t : ℝ) → t ≤ 0 →
      QMCLeafB.FinalStroke.loopBit init round verdict Tbc2 G t = true)
    (hd : ∀ (G : QuantumMaxCutEnergy.Input) (t : ℚ), 2 ≤ G.n →
      -QMCLeafB.EngineRuntime.Rq G ≤ t →
      (t : ℝ) < -(((QMCLeafB.EngineRuntime.Rq G / 40000 : ℚ)) : ℝ) →
      QMCLeafB.FinalStroke.RunParts
        (QMCLeafB.FinalStroke.loopBit init round verdict Tbc2) G t
        (QMCLeafB.UnionShallow.paramsKbc2 G)) :
    QMCLeafB.FinishLine.SolutionStatement :=
  QMCLeafB.UnionShallow.solution_union_shallow_final k hk init round verdict hinit hr hv
    (fun s => (enc s).length) 1 c 1 (le_refl 1) hstepLen
    (fun s => le_trans (hstepLen s) (le_max_left _ _)) (fun s => by simp)
    hinitTape htop hd

#print axioms QMCLeafB.Fal30.solution_of_step_le

/-- **The two-sided sharp bracket for the verdict bit.**  At `2 ≤ G.n`, one `RunParts` at the
program's own bit (i.e. `hd`) confines the bit to a window of width `2·eps G` around the trace floor
`−Rq G`:

* `bit_false_of_lt_floor_minus_eps`: below `−Rq G − eps G` the certificate `hcert` asks for cannot
  exist (`FinishLine.neg_Rq_le_trace`), so the bit is `false`;
* `bit_true_of_runParts_of_attainer`: above `−Rq G + eps G` at an input attaining the floor, the
  refutation clause cannot hold, so the bit is `true`.

In between, both values are admissible, and that is *all* the freedom `hd` leaves.  (Read off the
campaign: `dqShallow/2 ≈ eps/38`, so the ok test's own threshold `t − eps + dq/2` crosses the floor
strictly inside the window — the design is consistent, and there is no room to move it out.) -/
theorem bit_false_of_lt_floor_minus_eps
    {o : QuantumMaxCutEnergy.Input → ℚ → Bool}
    {G : QuantumMaxCutEnergy.Input} {t : ℚ}
    {P : QMCLeafB.FinalStroke.RunParams G}
    (hn : 2 ≤ G.n) (d : QMCLeafB.FinalStroke.RunParts o G t P)
    (ht : (t : ℝ) + ((QMCLeafB.EngineRuntime.Rq G / 40000 : ℚ) : ℝ)
      < -((QMCLeafB.EngineRuntime.Rq G : ℚ) : ℝ)) :
    o G t = false := by
  cases hb : o G t with
  | true =>
    exfalso
    obtain ⟨X, hX, htr⟩ :=
      (QMCLeafB.VerdictSound.soundAt_of_runData o G t hn d.toRunData).1 hb
    have hfloor := QMCLeafB.FinishLine.neg_Rq_le_trace G X hX
    linarith
  | false => rfl

#print axioms QMCLeafB.Fal30.bit_false_of_lt_floor_minus_eps

/-! ### The campaign numbers, machine-checked

At `G₁` (`Rq = 2`, `eps = 1/20000`, `dqShallow = 1/380000`, `n = 2`): the forced-`false` threshold is
`−2.00005`, the forced-`true` threshold `−1.99995`, so the window is `[−2.00005, −1.99995]` and the
template's interior `[−2, −1/20000)` meets the forced-`true` region on `(−1.99995, −1/20000)`.  The
certified test's grid at the *coherent* tolerance `δ = dqShallow` is `2n²/δ = 3 040 000`, against the
campaign's snapped grid `(n+1)^4 = 81` — which is why the snapped grid is dead
(`ContractM7.pivFSpec_false`), and why the grid must be carried in the state. -/

/-- `eps G₁ = 1/20000`, so the window is `±1/20000` around `−2`. -/
theorem window_G₁ :
    ((QMCLeafB.EngineRuntime.Rq QMCLeafB.EmptyBodyM5.G₁ / 40000 : ℚ) : ℚ) = 1 / 20000 := by
  rw [QMCLeafB.EmptyBodyM5.Rq_G₁]; norm_num

/-- The certified grid at `G₁`, at the coherent tolerance `δ = dqShallow G₁ = 1/380000` and `n = 2`. -/
theorem grid_G₁ : 2 * ((2 : ℚ) * 2) / (1 / 380000) = 3040000 := by norm_num

/-- The campaign's snapped grid at `G₁` is `(2+1)^4 = 81`: `37 530` times too small for the certified
test.  No re-derivation of the phase-20 kill, just the ratio the grid must pay. -/
theorem snapped_grid_far_below_G₁ : (2 + 1) ^ 4 = 81 ∧ (81 : ℚ) < 3040000 := by
  refine ⟨by norm_num, by norm_num⟩

#print axioms QMCLeafB.Fal30.window_G₁
#print axioms QMCLeafB.Fal30.grid_G₁
#print axioms QMCLeafB.Fal30.snapped_grid_far_below_G₁

/-! ## §D.  Inputs (3) and (4): `hinitTape` and `htop` are *interface shapes*, not theorems -/

/-- **Input (3), `hinitTape`, is discharged by the shape of `init`.**  The template's hypothesis is
exactly "read only `(G, t)`", so a program that computes its initial code from the request and the
threshold never has to prove anything about the tape: `init` must be *defined* as a function of
`p.1.1` and `p.2`. -/
theorem hinitTape_of_factors {σ : Type} [Coding σ]
    (init : QMCLeafB.FuelWire.Pkg → σ)
    (f : QuantumMaxCutEnergy.Input → ℚ → σ)
    (h : ∀ p : QMCLeafB.FuelWire.Pkg, init p = f p.1.1 p.2) :
    ∀ p : QMCLeafB.FuelWire.Pkg,
      init p = init (QMCLeafB.FinalStroke.noTape p.1.1 p.2) := by
  intro p
  rw [h p, h (QMCLeafB.FinalStroke.noTape p.1.1 p.2)]
  rfl

#print axioms QMCLeafB.Fal30.hinitTape_of_factors

/-- **Input (4), `htop`, first half: the identity is a member on the whole top slice.**  At
`cX = 1` the three `RelaxMem` margins are `∑x² ≥ 0` (PSD), `|1 − 1| = 0` (diagonal) and
`frob A 1 = tr A = 0` (objective, since the weight matrix has zero diagonal), so the ok test passes at
the identity as soon as `0 ≤ t − eps + δ/2` — true for every `t ≥ −eps` when `δ > 0`.  Hence the
program's *first* round reports `ok` on the whole top slice (its round-0 centre is the initial code),
and `htop` costs no analysis beyond `init` and the round count. -/
theorem relaxMem_one (G : QuantumMaxCutEnergy.Input) (t : ℚ) {δ : ℚ} (hδ : 0 < δ)
    (ht : 0 ≤ t - QMCLeafB.RundataCert.eps G + δ / 2) :
    QMCLeafB.RelaxOracle.RelaxMem (QMCLeafB.Finalization.wMatrixQ G)
      (1 : Matrix (Fin G.n) (Fin G.n) ℚ) (t - QMCLeafB.RundataCert.eps G) δ := by
  have hq : ∀ x : Fin G.n → ℚ,
      QMCLeafB.SepOracle.qf (1 : Matrix (Fin G.n) (Fin G.n) ℚ) x = ∑ i, x i ^ 2 := by
    intro x
    simp [QMCLeafB.SepOracle.qf, Matrix.mulVec_one, dotProduct, sq]
  have hf : QMCLeafB.SepOracle.frob (QMCLeafB.Finalization.wMatrixQ G)
      (1 : Matrix (Fin G.n) (Fin G.n) ℚ) = 0 := by
    rw [QMCLeafB.SepOracle.frob]
    refine Finset.sum_eq_zero fun i _ => ?_
    refine Finset.sum_eq_zero fun j _ => ?_
    rw [Matrix.one_apply]
    by_cases hij : i = j
    · subst hij; simp [QMCLeafB.Finalization.wMatrixQ_apply_of_eq]
    · simp [hij]
  refine ⟨hδ, ?_, ?_, ?_⟩
  · intro x
    rw [hq x]
    have hnn : (0 : ℚ) ≤ ∑ i, x i ^ 2 := Finset.sum_nonneg fun i _ => sq_nonneg _
    nlinarith
  · intro i
    have h1 : (1 : Matrix (Fin G.n) (Fin G.n) ℚ) i i = 1 := by simp
    rw [h1, sub_eq_add_neg, add_neg_cancel, abs_zero]
    linarith
  · rw [hf]; linarith

#print axioms QMCLeafB.Fal30.relaxMem_one

/-- **Input (4), `htop`, second half: one `ok` round makes the bit true.**  `RunParts.hverdict` says
the bit *is* the `anyOk` of the recorded stream, and `anyOk` is `true` at a positive horizon as soon
as one recorded round is `ok`.  So `htop` reduces to: the program's round `0` reports `ok` on the top
slice — which `relaxMem_one` supplies. -/
theorem bit_true_of_ok_zero
    {o : QuantumMaxCutEnergy.Input → ℚ → Bool}
    {G : QuantumMaxCutEnergy.Input} {t : ℚ}
    {P : QMCLeafB.FinalStroke.RunParams G}
    (d : QMCLeafB.FinalStroke.RunParts o G t P)
    (hKm : 1 ≤ P.K * P.m) (h0 : d.ok 0 = true) :
    o G t = true := by
  rw [d.hverdict, QMCLeafB.SimLoop.anyOk_eq_true_iff]
  exact ⟨0, by omega, h0⟩

#print axioms QMCLeafB.Fal30.bit_true_of_ok_zero

/-- **`htop`, composed.**  On the top slice the first round's test datum exists (`relaxMem_one`), so
a record whose round `0` reports `ok` reads `true` — the top slice never needs a cut round, a
separation argument, or a certificate.  Residual of input (4): the program's round-0 centre must be
the identity code (or any other point whose three cheap margins hold there), and `Tbc2 ≥ 1`
(`UnionShallow.one_le_Kbc2_mul`). -/
theorem htop_of_identity_ok
    {o : QuantumMaxCutEnergy.Input → ℚ → Bool}
    {G : QuantumMaxCutEnergy.Input} {t : ℚ}
    {P : QMCLeafB.FinalStroke.RunParams G}
    (hn : 2 ≤ G.n) (d : QMCLeafB.FinalStroke.RunParts o G t P)
    (hKm : 1 ≤ P.K * P.m)
    (h0 : d.ok 0 = true) :
    o G t = true :=
  bit_true_of_ok_zero d hKm h0

#print axioms QMCLeafB.Fal30.htop_of_identity_ok

/-- **The ledger's second honest shape: a constant envelope.**  A one-time enlarge of the code (the
`O(L³)` step the `IntegrateM6.orbit_envelope` docstring describes: `n²` fresh entries in one round)
*cannot* be carried by a monomial `M` — `not_ledger_monomial` above — but it is carried by a
constant `M ≡ C`: then `hMinv` is `C ≤ C + c`, `hM` is `C ≤ C·(L+1)`, and `hstep` says exactly what
one wants, "after the one-time enlarge every round adds at most `c`".  So a program with a large
first-round write and a cheap round afterwards has a ledger; a program with a monomial cap has
none. -/
theorem ledger_of_bounded {σ : Type} [Coding σ] (round : σ → σ) (C c : ℕ)
    (h : ∀ s : σ, (enc (round s)).length ≤ max ((enc s).length + c) C) :
    ∃ (M : σ → ℕ) (C₀ kr : ℕ), 1 ≤ kr ∧ (∀ s, M (round s) ≤ M s + c) ∧
      (∀ s, (enc (round s)).length ≤ max ((enc s).length + c) (M s)) ∧
      (∀ s, M s ≤ C₀ * ((enc s).length + 1) ^ kr) :=
  ⟨fun _ => C, C, 1, le_refl 1, fun s => by simp, h, fun s => by
    show C ≤ C * ((enc s).length + 1) ^ 1
    rw [pow_one]
    exact Nat.le_mul_of_pos_right C (by omega)⟩

#print axioms QMCLeafB.Fal30.ledger_of_bounded

end QMCLeafB.Fal30


