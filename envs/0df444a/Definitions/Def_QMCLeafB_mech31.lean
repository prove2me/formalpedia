-- Prove2me | Definitions.Def_QMCLeafB_mech31
-- name    : QMCLeafB_mech31
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-05T10:28:19.54395+00:00
-- url     : https://prove2.me/theorems/a8914f26-8320-4f7e-bace-d95f7a38bf9b
-- title:
--   QMCLeafB mech31
-- statement:
--   # `Check_mech31_m6` — phase 31, member m6, direction `mech-slots` (d3)
--
--   Published as part of the QMCLeafB library mirror supporting the quantum max-cut campaign's polynomial-time SDP-value certificate (AGM20, TQC 2020, arXiv 2003.14394).

import Mathlib
import Definitions.Def_QMCLeafB_htop_ledgerW_m7
import Definitions.Def_QMCLeafB_initdq_m1
import Definitions.Def_QMCLeafB_assembly_m5
import Definitions.Def_QMCLeafB_asm2
/-
# `Check_mech31_m6` — phase 31, member m6, direction `mech-slots` (d3)

The phase-30 composite `Asm2M8.solution_of_residual` leaves NINE inputs: the three `Poly` slots of
`(init, round, verdict)`, the one-step length bound `hstepLen`, `hinitTape`, `htop`, `hbit`, `hok`,
`hC`.  This file reduces them to TWO, at a concrete program — the campaign's own packed state
(`RoundProgram.RSt`), the campaign initial state (`InitDq.init0`, re-packed at the campaign tolerance
`dqShallow`), the guarded lower-body round (`LedgerW.roundWG`) and the campaign verdict
(`RoundProgram.verdict`), at the campaign count `Tbc2`.

**Headline (§10): `leaf_of_hok_and_complete (hok) (hcomplete) : <verbatim d9f601e5>`.**  The leaf
follows from exactly two analytic statements at that program — `hok` (bit `true` ⟹ a symmetric
rational `RelaxMem` at the loop's own centre, level `t − eps`, tolerance `dqShallow`) and
`hcomplete` (body non-empty ⟹ bit `true`).  Everything else is proved here or banked:

* §1 the three `Poly` slots (`InitDq.poly_init0`, `LedgerW.poly_roundWG`, `RoundProgram.poly_verdict`);
* §2 `hinitTape` (`InitDq.init0_tape`);
* §3 `htop` (`LedgerW.htop_roundWG` + `stOks_init0`/`init_normalised`/`stT_init0`/`epsOf_init0_any`;
  no `2 ≤ G.n` needed, and it holds for every `T0 ≥ 1`);
* §4 the size slot: the campaign's own ledger is `max`-form with the cap `MszG`
  (`enc_roundWG_le`, `MszG_roundWG_le`, `MszG_capW`), and the residual's *additive* `hstepLen` is a
  strictly stronger form that the shelf cannot give.  §4a isolates the missing hypothesis
  (`MszG s ≤ (enc s).length + c`, false in general); §4b gives the repair — pad the code to the cap:
  `padTo (enc s) (MszG s)` is length-additive with `c = 6`;
* §5 `Inst.solution_of_campaign`: `Asm2M8.solution_of_residual` at the concrete program;
* §6 **`hbit`'s `mpr` half is `hok`'s corollary** (`HemptyR_M3.relaxBodyLE_of_relaxMem`: a rational
  `RelaxMem` member casts to a real body point), **`hbit` follows from `hok` + completeness**, and
  **`hC` is vacuous** given `hbit` (`bit = false ⟹ EmptyBody` contradicts `hC`'s `¬EmptyBody`);
  §6 closes with `solution_of_hok_and_complete`;
* §7 the length ledger's own algebra (composition recipes for a length-safe round; note
  `enc_roundOk` is *exactly* additive, so only the cut branch of the campaign round offends);
* §9 the padded-coding instantiation: at `padCoding` the length slot is a theorem, so the leaf is the
  three `Poly` slots at the padded code plus `hok` + completeness;
* §11 the grid receipt: `hok`'s `RelaxMem` carries the relaxed-PSD clause at `δ = dqShallow`, i.e.
  `LdltCertM5.pivPsdMargin_of_tolerance`'s grid condition `2n² ≤ dq·d`; the campaign's grid
  `gridOf n = (n+1)^4` fails it at the exemplar `G₁` (`8 ≤ 81/380000` is false), so `hok` forces the
  state's `d` register to be enlarged to `d ≥ 2n²/dqShallow` — a program change.

Discipline: no `sorry`/`admit`/`axiom`/`native_decide`/`unsafe`; `#print axioms` at the end.
-/

open scoped BigOperators
open Matrix
open OAI.MetricKMedian.Binary
open OAI.MetricKMedian.Binary.Automatic

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option linter.unusedVariables false

noncomputable section

/-- The request coding of the leaf, as in the residual's own file.  Declared at file scope so that it
survives every namespace block below. -/
local instance instRequestCodingMech : Coding (QuantumMaxCutEnergy.Input × List Bool) :=
  ⟨QuantumMaxCutEnergy.encodeRequest⟩

namespace QMCLeafB.MechM6

open QuantumMaxCutEnergy


/-! ## 0.  The concrete program -/

/-- The packed campaign state. -/
abbrev St : Type := QMCLeafB.RoundProgram.RSt

/-- The campaign initial state, at the campaign tolerance `dqShallow` (m1's `init0`). -/
def init0 : QMCLeafB.FuelWire.Pkg → St := QMCLeafB.InitDq.init0

/-- The guarded lower-body round: the shelf engine's step with the lower-body `ok` test, the guard
falling back to the trivially-`ok` round whenever the state is not normalised. -/
def round0 : St → St := QMCLeafB.LedgerW.roundWG

/-- The campaign verdict: a positive count of recorded `ok` flags. -/
def verdict0 : St → Bool := QMCLeafB.RoundProgram.verdict

/-- **The program's bit**, at the residual's own count `Tbc2`. -/
def bit0 : QuantumMaxCutEnergy.Input → ℚ → Bool :=
  QMCLeafB.FinalStroke.loopBit init0 round0 verdict0 AsmM8.Tbc2

/-! ## 1.  The three `Poly` slots -/

theorem poly_init0 : Poly init0 := QMCLeafB.InitDq.poly_init0

theorem poly_round0 : Poly round0 := QMCLeafB.LedgerW.poly_roundWG

theorem poly_verdict0 : Poly verdict0 := QMCLeafB.RoundProgram.poly_verdict

/-! ## 2.  `hinitTape` -/

/-- **The initial state ignores the random tape** — the residual's `hinitTape` at `init0`. -/
theorem hinitTape0 : ∀ p : QMCLeafB.FuelWire.Pkg,
    init0 p = init0 (QMCLeafB.FinalStroke.noTape p.1.1 p.2) :=
  fun p => QMCLeafB.InitDq.init0_tape p

/-! ## 3.  `htop` -/

/-- **The bit is `true` on the whole top slice.**  Above `-eps G = -Rq G/40000` the state's own slack
swallows the level, so the very first round reports `ok` (the guard `0 ≤ stT + epsOf` fires) and the
run reads `true` for *every* positive round count — in particular `Tbc2`.  No `2 ≤ G.n` is needed and
no geometry: `relaxMem_one`-class content is not even consumed here, only the guard. -/
theorem htop0 : ∀ (G : QuantumMaxCutEnergy.Input) (t : ℚ), 2 ≤ G.n →
    -(((QMCLeafB.EngineRuntime.Rq G / 40000 : ℚ)) : ℝ) ≤ (t : ℝ) → t ≤ 0 →
    bit0 G t = true := by
  intro G t _ hlo hhi
  exact QMCLeafB.LedgerW.htop_roundWG init0
    (fun p => QMCLeafB.InitDq.stOks_init0 p)
    (fun p => QMCLeafB.InitDq.init_normalised p)
    (fun p => QMCLeafB.InitDq.stT_init0 p)
    (fun p => QMCLeafB.AssemblyM5.epsOf_init0_any p)
    AsmM8.Tbc2
    (fun G' t' => QMCLeafB.UnionShallow.one_le_Kbc2_mul G') G t hlo hhi

/-! ## 4.  The length slot -/

/-! ### 4a.  What the campaign's ledger does and does not give -/

/-- **A `max`-form ledger plus an additive cap gives the residual's one-step bound.**  This is the
exact arithmetic shape the campaign's ledger has (`enc_roundWG_le`), and the exact extra hypothesis
it needs (`M s ≤ (enc s).length + c₁` — a bound on the *cap* by the state's *own* code length). -/
theorem hstepLen_of_max_form {σ : Type} [Coding σ] (round : σ → σ) (M : σ → ℕ) (c₀ c₁ : ℕ)
    (hled : ∀ s, (enc (round s)).length ≤ max ((enc s).length + c₀) (M s))
    (hcap : ∀ s, M s ≤ (enc s).length + c₁) :
    ∀ s, (enc (round s)).length ≤ (enc s).length + max c₀ c₁ := by
  intro s
  have h := hled s
  have h2 : M s ≤ (enc s).length + max c₀ c₁ := le_trans (hcap s) (Nat.add_le_add_left (le_max_right _ _) _)
  have h3 : (enc s).length + c₀ ≤ (enc s).length + max c₀ c₁ :=
    Nat.add_le_add_left (le_max_left _ _) _
  exact le_trans h (max_le h3 h2)

/-- The campaign's ledger at the guarded round, restated: the `max`-form with the cap `MszG`. -/
theorem enc_round0_le (s : St) :
    (enc (round0 s)).length ≤ max ((enc s).length + 6) (QMCLeafB.CapGuard.MszG s) :=
  QMCLeafB.LedgerW.enc_roundWG_le s

/-- The cap grows by `6` per round. -/
theorem MszG_round0_le (s : St) :
    QMCLeafB.CapGuard.MszG (round0 s) ≤ QMCLeafB.CapGuard.MszG s + 6 :=
  QMCLeafB.LedgerW.MszG_roundWG_le s

/-- The state's own code length is below the cap. -/
theorem enc_le_MszG (s : St) : (enc s).length ≤ QMCLeafB.CapGuard.MszG s :=
  QMCLeafB.CapGuard.enc_le_MszG s

/-! ### 4b.  The padding receipt: at the ledger cap the round *is* length-additive -/

/-- Pad a bit string to a prescribed length (no-op once it is long enough). -/
def padTo (b : List Bool) (n : ℕ) : List Bool := b ++ List.replicate (n - b.length) false

theorem padTo_length {b : List Bool} {n : ℕ} (h : b.length ≤ n) : (padTo b n).length = n := by
  simp only [padTo, List.length_append, List.length_replicate]
  omega

/-- **The residual's `hstepLen` from a ledger, by padding the code to the cap.**  If the code is
padded to a length `M` that is monotone under the round with increment `c` and that dominates the raw
code length, then the padded code is length-additive with the same `c`.  This is the exact repair of
§4a's missing hypothesis: it is *not* true that the raw campaign code is additive, but the padded
campaign code is. -/
theorem hstepLen_padded {σ : Type} [Coding σ] (round : σ → σ) (M : σ → ℕ) (c : ℕ)
    (hlen : ∀ s, (enc s).length ≤ M s) (hM : ∀ s, M (round s) ≤ M s + c) :
    ∀ s, (padTo (enc (round s)) (M (round s))).length
      ≤ (padTo (enc s) (M s)).length + c := by
  intro s
  rw [padTo_length (hlen (round s)), padTo_length (hlen s)]
  exact hM s

/-- **The campaign's code padded to its own ledger cap is length-additive with `c = 6`.**  This is
`hstepLen` of the residual, discharged at the padded coding. -/
theorem hstepLen_padded_campaign (s : St) :
    (padTo (enc (round0 s)) (QMCLeafB.CapGuard.MszG (round0 s))).length
      ≤ (padTo (enc s) (QMCLeafB.CapGuard.MszG s)).length + 6 :=
  hstepLen_padded round0 QMCLeafB.CapGuard.MszG 6 enc_le_MszG MszG_round0_le s

/-! ## 5.  The instantiation: `d9f601e5` at the concrete program

The residual's nine inputs, with §1–§3 supplying five of them.  What remains is `hstepLen` (§4: the
code's length slot), `hbit`, `hok`, `hC`. -/

namespace Inst

open QMCLeafB.MechM6

/-- **The leaf at the campaign program**, from the four remaining slots. -/
theorem solution_of_campaign (c : ℕ)
    (hstepLen : ∀ s : St, (enc (round0 s)).length ≤ (enc s).length + c)
    (hbit : ∀ (G : QuantumMaxCutEnergy.Input) (t : ℚ), 2 ≤ G.n → AsmM8.Interior G t →
      (bit0 G t = false ↔
        AsmM8.EmptyBody G t (QMCLeafB.UnionShallow.paramsKbc2 G)))
    (hok : ∀ (G : QuantumMaxCutEnergy.Input) (t : ℚ), 2 ≤ G.n → AsmM8.Interior G t →
      bit0 G t = true →
      ∃ cX : Matrix (Fin G.n) (Fin G.n) ℚ, cXᵀ = cX ∧
        QMCLeafB.RelaxOracle.RelaxMem (QMCLeafB.Finalization.wMatrixQ G) cX
          (t - QMCLeafB.RundataCert.eps G) (QMCLeafB.RundataParams.dqShallow G))
    (hC : ∀ (G : QuantumMaxCutEnergy.Input) (t : ℚ), 2 ≤ G.n → AsmM8.Interior G t →
      ¬ AsmM8.EmptyBody G t (QMCLeafB.UnionShallow.paramsKbc2 G) →
      bit0 G t = false →
      QMCLeafB.FinalStroke.RunParts bit0 G t (QMCLeafB.UnionShallow.paramsKbc2 G)) :
    ∃ L : QuantumMaxCutEnergy.Input → ℚ≥0,
      Nonempty (Turing.TM2ComputableInPolyTime QuantumMaxCutEnergy.encodeRequest
        QuantumMaxCutEnergy.encodeValue
        (fun request : QuantumMaxCutEnergy.Input × List Bool => L request.1)) ∧
      ∀ G : QuantumMaxCutEnergy.Input, ∃ S : ℝ,
        ModernConvex.Relaxations.IsMaxcutSDPValue
          (Matrix.of fun i j : Fin G.n =>
            if h : i < j then (G.weights ⟨(i, j), h⟩ : ℝ)
            else if h : j < i then (G.weights ⟨(j, i), h⟩ : ℝ) else 0) S ∧
        (L G : ℝ) ≤ S ∧
        S - (L G : ℝ) ≤ (∑ e, (G.weights e : ℝ)) / 10000 :=
  Asm2M8.solution_of_residual (σ := St) 20 (by norm_num) init0 round0 verdict0
    poly_init0 poly_round0 poly_verdict0 c hstepLen hinitTape0 htop0 hbit hok hC

/-- **The five closed slots, in one statement.**  Everything `Asm2M8.solution_of_residual` asks about
the *program* except the length slot, at the campaign's own `(init0, roundWG, verdict, Tbc2)`. -/
theorem mech_slots_closed :
    Automatic.Poly init0 ∧ Automatic.Poly round0 ∧ Automatic.Poly verdict0 ∧
    (∀ p : QMCLeafB.FuelWire.Pkg, init0 p = init0 (QMCLeafB.FinalStroke.noTape p.1.1 p.2)) ∧
    (∀ (G : QuantumMaxCutEnergy.Input) (t : ℚ), 2 ≤ G.n →
      -(((QMCLeafB.EngineRuntime.Rq G / 40000 : ℚ)) : ℝ) ≤ (t : ℝ) → t ≤ 0 →
      bit0 G t = true) :=
  ⟨poly_init0, poly_round0, poly_verdict0, hinitTape0, htop0⟩

end Inst

/-! ## 6.  `hbit`'s easy half is `hok`'s corollary — and `hC` is then vacuous

The phase-30 composite carries `hC` (`RunParts` at body-non-empty, bit-false points) as an independent
slot, but with `hbit` read as a genuine equivalence it cannot be inhabited:
`hbit.mp` turns `bit = false` into `EmptyBody`, contradicting `hC`'s own non-emptiness hypothesis.
And one half of `hbit` needs no search argument at all: a bit-`true` point carries a rational
`RelaxMem` (`hok`), whose member casts to a real point of the relaxed body
(`HemptyR_M3.relaxBodyLE_of_relaxMem`), so an empty body cannot be bit-`true`.  So

  `hbit  ⟸  hok  +  (body non-empty ⟹ bit true)`

and the leaf's analytic residual is exactly `hok` together with the program's *completeness* — the
thin-band `hC` disappears. -/

/-- **A rational `RelaxMem` at level `t − eps G` and tolerance `dqShallow G` excludes an empty
body** — the cast bridge `HemptyR_M3.relaxBodyLE_of_relaxMem` at the campaign's own parameters. -/
theorem not_emptyBody_of_relaxMem {G : QuantumMaxCutEnergy.Input} {t : ℚ}
    {cX : Matrix (Fin G.n) (Fin G.n) ℚ}
    (h : QMCLeafB.RelaxOracle.RelaxMem (QMCLeafB.Finalization.wMatrixQ G) cX
      (t - QMCLeafB.RundataCert.eps G) (QMCLeafB.RundataParams.dqShallow G)) :
    ¬ AsmM8.EmptyBody G t (QMCLeafB.UnionShallow.paramsKbc2 G) := by
  intro hempty
  have hbody := QMCLeafB.HemptyR_M3.relaxBodyLE_of_relaxMem h
  rw [QMCLeafB.HemptyR_M3.castMat_wMatrixQ] at hbody
  have hlevel : (((t - QMCLeafB.RundataCert.eps G : ℚ)) : ℝ)
      = (t : ℝ) - (((QMCLeafB.EngineRuntime.Rq G / 40000 : ℚ)) : ℝ) := by
    unfold QMCLeafB.RundataCert.eps
    push_cast
    ring
  have hdq : (((QMCLeafB.RundataParams.dqShallow G : ℚ)) : ℝ)
      = (((QMCLeafB.UnionShallow.paramsKbc2 G).dq : ℚ) : ℝ) := by
    rw [QMCLeafB.UnionShallow.paramsKbc2_dq]
  rw [hlevel, hdq] at hbody
  exact hempty (QMCLeafB.SepOracle.castMat cX) hbody

/-- **`hbit.mpr` from `hok`**: at an empty body the bit reads `false`. -/
theorem bit_eq_false_of_emptyBody
    (hok : ∀ (G : QuantumMaxCutEnergy.Input) (t : ℚ), 2 ≤ G.n → AsmM8.Interior G t →
      bit0 G t = true →
      ∃ cX : Matrix (Fin G.n) (Fin G.n) ℚ, cXᵀ = cX ∧
        QMCLeafB.RelaxOracle.RelaxMem (QMCLeafB.Finalization.wMatrixQ G) cX
          (t - QMCLeafB.RundataCert.eps G) (QMCLeafB.RundataParams.dqShallow G))
    (G : QuantumMaxCutEnergy.Input) (t : ℚ) (hn : 2 ≤ G.n) (hint : AsmM8.Interior G t)
    (hempty : AsmM8.EmptyBody G t (QMCLeafB.UnionShallow.paramsKbc2 G)) : bit0 G t = false := by
  cases hb : bit0 G t with
  | false => rfl
  | true =>
    obtain ⟨cX, _, hmem⟩ := hok G t hn hint hb
    exact absurd hempty (not_emptyBody_of_relaxMem hmem)

/-- **`hbit` from `hok` plus the program's completeness** — the iff, with no thin-band record
required in the assembly. -/
theorem hbit_of_hok_and_complete
    (hok : ∀ (G : QuantumMaxCutEnergy.Input) (t : ℚ), 2 ≤ G.n → AsmM8.Interior G t →
      bit0 G t = true →
      ∃ cX : Matrix (Fin G.n) (Fin G.n) ℚ, cXᵀ = cX ∧
        QMCLeafB.RelaxOracle.RelaxMem (QMCLeafB.Finalization.wMatrixQ G) cX
          (t - QMCLeafB.RundataCert.eps G) (QMCLeafB.RundataParams.dqShallow G))
    (hcomplete : ∀ (G : QuantumMaxCutEnergy.Input) (t : ℚ), 2 ≤ G.n → AsmM8.Interior G t →
      ¬ AsmM8.EmptyBody G t (QMCLeafB.UnionShallow.paramsKbc2 G) → bit0 G t = true) :
    ∀ (G : QuantumMaxCutEnergy.Input) (t : ℚ), 2 ≤ G.n → AsmM8.Interior G t →
      (bit0 G t = false ↔ AsmM8.EmptyBody G t (QMCLeafB.UnionShallow.paramsKbc2 G)) := by
  intro G t hn hint
  constructor
  · intro hf
    by_contra hne
    have ht : bit0 G t = true := hcomplete G t hn hint hne
    rw [hf] at ht
    exact absurd ht (by simp)
  · intro he
    exact bit_eq_false_of_emptyBody hok G t hn hint he

/-- **The leaf from `hok` + completeness + the length slot.**  `hC` and `hbit` are *proved* here from
those two, so the campaign's residual at the campaign program is two analytic slots and the code's
length discipline. -/
theorem solution_of_hok_and_complete (c : ℕ)
    (hstepLen : ∀ s : St, (enc (round0 s)).length ≤ (enc s).length + c)
    (hok : ∀ (G : QuantumMaxCutEnergy.Input) (t : ℚ), 2 ≤ G.n → AsmM8.Interior G t →
      bit0 G t = true →
      ∃ cX : Matrix (Fin G.n) (Fin G.n) ℚ, cXᵀ = cX ∧
        QMCLeafB.RelaxOracle.RelaxMem (QMCLeafB.Finalization.wMatrixQ G) cX
          (t - QMCLeafB.RundataCert.eps G) (QMCLeafB.RundataParams.dqShallow G))
    (hcomplete : ∀ (G : QuantumMaxCutEnergy.Input) (t : ℚ), 2 ≤ G.n → AsmM8.Interior G t →
      ¬ AsmM8.EmptyBody G t (QMCLeafB.UnionShallow.paramsKbc2 G) → bit0 G t = true) :
    ∃ L : QuantumMaxCutEnergy.Input → ℚ≥0,
      Nonempty (Turing.TM2ComputableInPolyTime QuantumMaxCutEnergy.encodeRequest
        QuantumMaxCutEnergy.encodeValue
        (fun request : QuantumMaxCutEnergy.Input × List Bool => L request.1)) ∧
      ∀ G : QuantumMaxCutEnergy.Input, ∃ S : ℝ,
        ModernConvex.Relaxations.IsMaxcutSDPValue
          (Matrix.of fun i j : Fin G.n =>
            if h : i < j then (G.weights ⟨(i, j), h⟩ : ℝ)
            else if h : j < i then (G.weights ⟨(j, i), h⟩ : ℝ) else 0) S ∧
        (L G : ℝ) ≤ S ∧
        S - (L G : ℝ) ≤ (∑ e, (G.weights e : ℝ)) / 10000 :=
  Inst.solution_of_campaign c hstepLen
    (hbit_of_hok_and_complete hok hcomplete) hok
    (fun G t hn hint hne hbf => absurd ((hbit_of_hok_and_complete hok hcomplete G t hn hint).mp hbf) hne)

/-! ## 7.  The length ledger's own algebra — what a length-safe round must satisfy

The residual's `hstepLen` is *one* inequality per state, so it is closed under the operations a round
is built from.  These are the recipes the program lane needs to keep the slot provable while the
round grows (the cut branch of the campaign round is the only offender: the `ok` branch is additive
*exactly*, `enc_roundOk : (enc (roundOk s)).length = (enc s).length + 6`). -/

section Algebra

variable {σ : Type} [Coding σ]

/-- The identity round is length-neutral (`c = 0`). -/
theorem stepLen_id : ∀ s : σ, (enc (id s)).length ≤ (enc s).length + 0 := by
  intro s; simp

/-- A constant round costs its own code length. -/
theorem stepLen_const (s₀ : σ) : ∀ s : σ, (enc ((fun _ => s₀) s)).length ≤ (enc s).length + (enc s₀).length := by
  intro s; simp

/-- Length bounds compose. -/
theorem stepLen_comp (f g : σ → σ) (c₁ c₂ : ℕ)
    (hf : ∀ s, (enc (f s)).length ≤ (enc s).length + c₁)
    (hg : ∀ s, (enc (g s)).length ≤ (enc s).length + c₂) :
    ∀ s, (enc ((f ∘ g) s)).length ≤ (enc s).length + (c₁ + c₂) := by
  intro s
  have h1 := hf (g s)
  have h2 := hg s
  have h3 : (enc (g s)).length + c₁ ≤ (enc s).length + c₂ + c₁ := Nat.add_le_add_right h2 c₁
  calc (enc ((f ∘ g) s)).length = (enc (f (g s))).length := rfl
    _ ≤ (enc (g s)).length + c₁ := h1
    _ ≤ (enc s).length + c₂ + c₁ := h3
    _ = (enc s).length + (c₁ + c₂) := by omega

/-- A branch is length-cheap when it is the `ok` branch: the campaign's own `ok` round appends
exactly six symbols, so *any* `c ≥ 6` absorbs it. -/
theorem stepLen_roundOk_le (s : St) :
    (enc (QMCLeafB.RoundProgram.roundOk s)).length ≤ (enc s).length + 6 :=
  le_of_eq (QMCLeafB.CapGuard.enc_roundOk s)

end Algebra

/-! ## 9.  The padded coding: `hstepLen` closed, the `Poly` slots moved

§4b proved that at the code padded to the campaign's own ledger cap the guarded round is
length-additive with `c = 6`.  Here is that coding written out and the instantiation at it: the leaf
from the three `Poly` slots *at the padded coding* plus `hok` and completeness — the length slot is a
theorem. -/

/-- **The campaign code padded to its own ledger cap** `MszG` (the length the ledger guarantees for
the state's own records). -/
@[instance_reducible] def padCoding : Coding St := ⟨fun s => padTo (enc s) (QMCLeafB.CapGuard.MszG s)⟩

/-- The request's coding, as in the residual. -/
@[instance_reducible] def pkgCoding : Coding QMCLeafB.FuelWire.Pkg := inferInstance

/-- The `Bool` coding. -/
@[instance_reducible] def boolCoding : Coding Bool := inferInstance

/-- **`hstepLen` at the padded coding**, `c = 6`. -/
theorem stepLen_padCoding : ∀ s : St,
    (@enc St padCoding (round0 s)).length ≤ (@enc St padCoding s).length + 6 :=
  fun s => hstepLen_padded_campaign s

/-- **`htop` at the padded coding** — `loopBit` never reads the code, so the slot transports. -/
theorem htop_padCoding : ∀ (G : QuantumMaxCutEnergy.Input) (t : ℚ), 2 ≤ G.n →
    -(((QMCLeafB.EngineRuntime.Rq G / 40000 : ℚ)) : ℝ) ≤ (t : ℝ) → t ≤ 0 →
    @QMCLeafB.FinalStroke.loopBit St padCoding init0 round0 verdict0 AsmM8.Tbc2 G t = true := by
  intro G t hn hlo hhi
  exact htop0 G t hn hlo hhi

/-- **The leaf at the padded coding**: `hstepLen` and `hinitTape` are proved, the three `Poly` slots
are owed at the padded code, and the two analytic slots are `hok` + completeness. -/
theorem solution_of_hok_and_complete_padded
    (hinit : @Poly QMCLeafB.FuelWire.Pkg St pkgCoding padCoding init0)
    (hr : @Poly St St padCoding padCoding round0)
    (hv : @Poly St Bool padCoding boolCoding verdict0)
    (hstepLen : ∀ s : St, (@enc St padCoding (round0 s)).length ≤ (@enc St padCoding s).length + 6)
    (hok : ∀ (G : QuantumMaxCutEnergy.Input) (t : ℚ), 2 ≤ G.n → AsmM8.Interior G t →
      @QMCLeafB.FinalStroke.loopBit St padCoding init0 round0 verdict0 AsmM8.Tbc2 G t = true →
      ∃ cX : Matrix (Fin G.n) (Fin G.n) ℚ, cXᵀ = cX ∧
        QMCLeafB.RelaxOracle.RelaxMem (QMCLeafB.Finalization.wMatrixQ G) cX
          (t - QMCLeafB.RundataCert.eps G) (QMCLeafB.RundataParams.dqShallow G))
    (hcomplete : ∀ (G : QuantumMaxCutEnergy.Input) (t : ℚ), 2 ≤ G.n → AsmM8.Interior G t →
      ¬ AsmM8.EmptyBody G t (QMCLeafB.UnionShallow.paramsKbc2 G) →
      @QMCLeafB.FinalStroke.loopBit St padCoding init0 round0 verdict0 AsmM8.Tbc2 G t = true) :
    ∃ L : QuantumMaxCutEnergy.Input → ℚ≥0,
      Nonempty (Turing.TM2ComputableInPolyTime QuantumMaxCutEnergy.encodeRequest
        QuantumMaxCutEnergy.encodeValue
        (fun request : QuantumMaxCutEnergy.Input × List Bool => L request.1)) ∧
      ∀ G : QuantumMaxCutEnergy.Input, ∃ S : ℝ,
        ModernConvex.Relaxations.IsMaxcutSDPValue
          (Matrix.of fun i j : Fin G.n =>
            if h : i < j then (G.weights ⟨(i, j), h⟩ : ℝ)
            else if h : j < i then (G.weights ⟨(j, i), h⟩ : ℝ) else 0) S ∧
        (L G : ℝ) ≤ S ∧
        S - (L G : ℝ) ≤ (∑ e, (G.weights e : ℝ)) / 10000 :=
  @Asm2M8.solution_of_residual St padCoding 20 (by norm_num) init0 round0 verdict0
    hinit hr hv 6 hstepLen hinitTape0 htop_padCoding
    (hbit_of_hok_and_complete hok hcomplete) hok
    (fun G t hn hint hne hbf => absurd ((hbit_of_hok_and_complete hok hcomplete G t hn hint).mp hbf) hne)

/-! ## 10.  The leaf from `hok` + completeness, with the size slot supplied by the campaign's OWN
ledger (no `hstepLen` anywhere)

m4's `Fal30.ledger_of_step_le` replaced the template's ledger `(M, C₀, c, kr, hMinv, hstep, hM)` by the
single additive inequality `hstepLen`, which then became a residual (§4: it is not obtainable at the
campaign code).  But the campaign's engine proves the *max-form* ledger outright at `M := MszG`:

* `hMinv`  — `LedgerW.MszG_roundWG_le`  (`MszG (roundWG s) ≤ MszG s + 6`),
* `hstep`  — `LedgerW.enc_roundWG_le`   (`≤ max (len s + 6) (MszG s)`),
* `hM`     — `LedgerW.MszG_capW`        (`MszG s ≤ 11448595 · (len s + 1)^6`).

So the size slot is *closed* at the campaign program, `hstepLen` is not needed at all, and the
template stroke fires with only two analytic inputs left: `hok` and completeness. -/

theorem leaf_of_hok_and_complete
    (hok : ∀ (G : QuantumMaxCutEnergy.Input) (t : ℚ), 2 ≤ G.n → AsmM8.Interior G t →
      bit0 G t = true →
      ∃ cX : Matrix (Fin G.n) (Fin G.n) ℚ, cXᵀ = cX ∧
        QMCLeafB.RelaxOracle.RelaxMem (QMCLeafB.Finalization.wMatrixQ G) cX
          (t - QMCLeafB.RundataCert.eps G) (QMCLeafB.RundataParams.dqShallow G))
    (hcomplete : ∀ (G : QuantumMaxCutEnergy.Input) (t : ℚ), 2 ≤ G.n → AsmM8.Interior G t →
      ¬ AsmM8.EmptyBody G t (QMCLeafB.UnionShallow.paramsKbc2 G) → bit0 G t = true) :
    ∃ L : QuantumMaxCutEnergy.Input → ℚ≥0,
      Nonempty (Turing.TM2ComputableInPolyTime QuantumMaxCutEnergy.encodeRequest
        QuantumMaxCutEnergy.encodeValue
        (fun request : QuantumMaxCutEnergy.Input × List Bool => L request.1)) ∧
      ∀ G : QuantumMaxCutEnergy.Input, ∃ S : ℝ,
        ModernConvex.Relaxations.IsMaxcutSDPValue
          (Matrix.of fun i j : Fin G.n =>
            if h : i < j then (G.weights ⟨(i, j), h⟩ : ℝ)
            else if h : j < i then (G.weights ⟨(j, i), h⟩ : ℝ) else 0) S ∧
        (L G : ℝ) ≤ S ∧
        S - (L G : ℝ) ≤ (∑ e, (G.weights e : ℝ)) / 10000 :=
  QMCLeafB.UnionShallow.solution_union_shallow_final (σ := St) 20 (by norm_num)
    init0 round0 verdict0 poly_init0 poly_round0 poly_verdict0
    QMCLeafB.CapGuard.MszG 11448595 6 6 (by norm_num)
    MszG_round0_le enc_round0_le (fun s => QMCLeafB.LedgerW.MszG_capW s) hinitTape0 htop0
    (fun G t hn hlo hhi =>
      AsmM8.hd_of_classes (o := bit0)
        (fun G' t' hn' hint he => bit_eq_false_of_emptyBody hok G' t' hn' hint he)
        (fun G' t' hn' hint hb => Asm2M8.memberAt_of_relaxMem hn' hint (hok G' t' hn' hint hb))
        (fun G' t' hn' hint hne hbf =>
          absurd ((hbit_of_hok_and_complete hok hcomplete G' t' hn' hint).mp hbf) hne)
        G t hn hlo hhi)

/-! ## 11.  The grid receipt: `hok` is not dischargeable at the packed campaign state

`hok`'s conclusion `RelaxMem … (t − eps) dqShallow` carries the *relaxed PSD* clause at `δ = dqShallow`,
which for the engine's own `ok` answer is exactly `LdltCertM5.pivPsdMargin_of_tolerance` — and that
theorem's hypothesis is the grid condition `2·n² ≤ dq·d`.  The campaign's grid is
`gridOf n = (n+1)^4`; at the campaign's own exemplar `G₁` (`n = 2`, `dqShallow = 1/380000`) the
condition reads `8 ≤ 81/380000`, which is false.  So the packed state cannot carry `hok`: the `d`
register must be enlarged to `d ≥ 2n²/dqShallow` (polynomial in the bit cost), which is a program
change, not a proof one.  (The banked refutation of the unconditional form is
`LdltCertM5.no_unconditional_campaign_margin`; the repair interface is
`pivPsdMargin_of_tolerance`.) -/

theorem gridOf_two : QMCLeafB.InitVerdict.gridOf 2 = 81 := by
  unfold QMCLeafB.InitVerdict.gridOf
  norm_num

/-- **The campaign's grid fails the certified test's condition** at the exemplar `G₁`. -/
theorem campaign_grid_fails_certified :
    ¬ (2 * (2 : ℚ) * 2 ≤ (1 / 380000) * ((QMCLeafB.InitVerdict.gridOf 2 : ℕ) : ℚ)) := by
  rw [gridOf_two]
  norm_num

/-- **The campaign initial state's grid fails it** — at `G₁`'s order, at every tape. -/
theorem init0_grid_fails_certified (p : QMCLeafB.FuelWire.Pkg)
    (hG : p.1.1 = QMCLeafB.EmptyBodyM5.G₁) :
    ¬ (2 * (QMCLeafB.RoundProgram.stN (init0 p) : ℚ) * (QMCLeafB.RoundProgram.stN (init0 p) : ℚ)
      ≤ QMCLeafB.RundataParams.dqShallow p.1.1 * (QMCLeafB.RoundProgram.stD (init0 p) : ℚ)) := by
  unfold QMCLeafB.MechM6.init0
  have hN : QMCLeafB.RoundProgram.stN (QMCLeafB.InitDq.init0 p) = 2 := by
    rw [QMCLeafB.InitDq.stN_init0, hG]
  have hD : QMCLeafB.RoundProgram.stD (QMCLeafB.InitDq.init0 p) = 81 := by
    rw [QMCLeafB.InitDq.stD_init0, hN]
    exact gridOf_two
  have hdq : QMCLeafB.RundataParams.dqShallow p.1.1 = 1 / 380000 := by
    rw [hG]; exact QMCLeafB.EmptyBodyM5.dqShallow_G₁
  rw [hN, hD, hdq]
  norm_num

end QMCLeafB.MechM6

/-! ## 8.  Axiom audit -/

#print axioms QMCLeafB.MechM6.poly_init0
#print axioms QMCLeafB.MechM6.poly_round0
#print axioms QMCLeafB.MechM6.poly_verdict0
#print axioms QMCLeafB.MechM6.hinitTape0
#print axioms QMCLeafB.MechM6.htop0
#print axioms QMCLeafB.MechM6.hstepLen_of_max_form
#print axioms QMCLeafB.MechM6.hstepLen_padded
#print axioms QMCLeafB.MechM6.hstepLen_padded_campaign
#print axioms QMCLeafB.MechM6.Inst.solution_of_campaign
#print axioms QMCLeafB.MechM6.Inst.mech_slots_closed
#print axioms QMCLeafB.MechM6.not_emptyBody_of_relaxMem
#print axioms QMCLeafB.MechM6.bit_eq_false_of_emptyBody
#print axioms QMCLeafB.MechM6.hbit_of_hok_and_complete
#print axioms QMCLeafB.MechM6.solution_of_hok_and_complete
#print axioms QMCLeafB.MechM6.stepLen_comp
#print axioms QMCLeafB.MechM6.stepLen_roundOk_le
#print axioms QMCLeafB.MechM6.stepLen_padCoding
#print axioms QMCLeafB.MechM6.htop_padCoding
#print axioms QMCLeafB.MechM6.solution_of_hok_and_complete_padded
#print axioms QMCLeafB.MechM6.leaf_of_hok_and_complete
#print axioms QMCLeafB.MechM6.campaign_grid_fails_certified
#print axioms QMCLeafB.MechM6.init0_grid_fails_certified


