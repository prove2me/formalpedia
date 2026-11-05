-- Prove2me | Definitions.Def_QMCLeafB_asm_m8
-- name    : QMCLeafB_asm_m8
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-04T14:00:51.418499+00:00
-- url     : https://prove2.me/theorems/6b2e36a7-a2ce-4e0e-bbd6-a2f617dacc49
-- title:
--   QMCLeafB asm_m8
-- statement:
--   `Check_asm_m8` — phase 30, member m8, direction `assembly`.
--
--   Published as part of the QMCLeafB library mirror supporting the quantum max-cut campaign's polynomial-time SDP-value certificate (AGM20, TQC 2020, arXiv 2003.14394).

import Mathlib
import Definitions.Def_QMCLeafB_unionShallow
import Definitions.Def_QMCLeafB_audit25
import Definitions.Def_QMCLeafB_refuted_m3
/-
  `Check_asm_m8` — phase 30, member m8, direction `assembly`.

  What this file does: it fires the phase-29 submission template
  (`Solutions/solution_m1.lean` -> `QMCLeafB.UnionShallow.solution_union_shallow_final`) and then
  **diffs the hardest of the six inputs down**.  Nothing here is new mathematics; everything is
  either a one-line application of a banked brick or the assembly bookkeeping that the template
  leaves to the last mile.

  ## The diff (load-bearing)

  The template's `hd` is `RunParts o G t (paramsKbc2 G)` at every interior point, at the program's
  OWN loop bit `o`.  Its slots split into three classes, keyed on the bit and on the relaxed body:

  * **M class** (`MemberAt G t`: a genuine unit-diagonal PSD point at level `t + Rq/40000`).
    If the bit reads `true` there, `hd` is FREE: the all-`ok` stream reports the certificate at
    every round, `hcert` is that one point, and every cut slot is vacuous.
    (`runParts_of_member`)
  * **E class** (the relaxed body `relaxBall` is empty).  If the bit reads `false` there, `hd` is
    FREE and banked: `QMCLeafB.RefutedM3.runParts_of_emptyBody`, at exactly the template's
    `RunParts` type.  (`runParts_of_emptyBody`)
  * **C class** (body non-empty, bit `false`): the ONLY remaining construction.

  `hd_of_classes` is the trichotomy: `hd` follows from {bit false on E} + {bit true implies a
  member} + {C-class records}.  `member_of_runParts` is the necessity half: any program that meets
  the template ALREADY has `bit true -> member`, so the second obligation is not an extra
  hypothesis but the semantics the program lane owes.  Together they say the template's `hd` is
  equivalent to the C-class records plus two program-side bit facts — i.e. the campaign's thin-band
  residual, nothing more.

  Discipline: `set_option autoImplicit false`; no `sorry`/`admit`/`axiom`/`native_decide`/`unsafe`;
  `#print axioms` at the end (expected `[propext, Classical.choice, Quot.sound]`).
-/

open scoped BigOperators
open Matrix

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option maxRecDepth 4000

noncomputable section

namespace AsmM8

open QuantumMaxCutEnergy
open OAI.MetricKMedian.Binary
open OAI.MetricKMedian.Binary.Automatic

/-- The request coding of the leaf, as in the template (`local`, so it does not collide). -/
local instance instRequestCodingAsm : Coding (QuantumMaxCutEnergy.Input × List Bool) :=
  ⟨QuantumMaxCutEnergy.encodeRequest⟩

/-- The campaign's round count, at the campaign factor — verbatim from `solution_m1`. -/
abbrev Tbc2 : QuantumMaxCutEnergy.Input → ℚ → ℕ :=
  fun G' _ => QMCLeafB.UnionShallow.Kbc2 (QMCLeafB.HalvePerG.mHalve (G'.n * G'.n)) G'
    * QMCLeafB.HalvePerG.mHalve (G'.n * G'.n)

section Classes

variable {σ : Type} [Coding σ]
variable (init : QMCLeafB.FuelWire.Pkg → σ) (round : σ → σ) (verdict : σ → Bool)

/-- **The program's own bit**, spelled once so the classes below are readable. -/
abbrev Bit : QuantumMaxCutEnergy.Input → ℚ → Bool :=
  QMCLeafB.FinalStroke.loopBit init round verdict Tbc2

end Classes

/-! ## 1.  The two predicates the diff is stated at -/

/-- **The interior bracket** of `hd` (no `hn`: that is passed separately, as in the template). -/
def Interior (G : QuantumMaxCutEnergy.Input) (t : ℚ) : Prop :=
  -QMCLeafB.EngineRuntime.Rq G ≤ t ∧
    (t : ℝ) < -(((QMCLeafB.EngineRuntime.Rq G / 40000 : ℚ)) : ℝ)

/-- **The relaxed body is empty at `t`** — the `E` class.  This is *the* hypothesis
`RefutedM3.runParts_of_emptyBody` consumes, at the template's own `RunParams`. -/
def EmptyBody (G : QuantumMaxCutEnergy.Input) (t : ℚ) (P : QMCLeafB.FinalStroke.RunParams G) : Prop :=
  ∀ X : Matrix (Fin G.n) (Fin G.n) ℝ,
    ¬ QMCLeafB.BallFloor.relaxBodyLE (QMCLeafB.wMatrix G)
        ((t : ℝ) - (((QMCLeafB.EngineRuntime.Rq G / 40000 : ℚ)) : ℝ)) ((P.dq : ℚ) : ℝ) X

/-- **A genuine unit-diagonal PSD point at the shifted level `t + Rq/40000`** — the `M` class.
This is exactly the existential `RunParts.hcert` asks for at an `ok` round. -/
def MemberAt (G : QuantumMaxCutEnergy.Input) (t : ℚ) : Prop :=
  ∃ X : Matrix (Fin G.n) (Fin G.n) ℝ,
    QMCLeafB.AnswerProducer.IsUnitDiagPSD X ∧
      (QMCLeafB.wMatrix G * X).trace
        ≤ (t : ℝ) + (((QMCLeafB.EngineRuntime.Rq G / 40000 : ℚ)) : ℝ)

/-! ## 2.  `anyOk` at a constant stream -/

theorem anyOk_const_true (T : ℕ) (hT : 0 < T) :
    QMCLeafB.SimLoop.anyOk (fun _ : ℕ => true) T = true := by
  induction T with
  | zero => exact absurd hT (Nat.lt_irrefl 0)
  | succ k _ =>
      rw [QMCLeafB.SimLoop.anyOk_succ]
      rfl

/-! ## 3.  The `M` class is free: a bit-true point with a member carries `RunParts` -/

/-- **`hd` at the `M` class.**  If the bit reads `true` and a genuine unit-diagonal PSD point
exists at `t + Rq/40000`, the all-`ok` stream is a complete record: `hcert` is that point (it does
not depend on the round index), and every cut slot is vacuous.  No geometry, no drift, no ledger. -/
noncomputable def runParts_of_member {o : QuantumMaxCutEnergy.Input → ℚ → Bool}
    {G : QuantumMaxCutEnergy.Input} {t : ℚ} (P : QMCLeafB.FinalStroke.RunParams G)
    (hn : 2 ≤ G.n) (hKm : 1 ≤ P.K * P.m)
    (hbit : o G t = true) (hmem : MemberAt G t) :
    QMCLeafB.FinalStroke.RunParts o G t P := by
  classical
  have hN : 2 ≤ G.n * G.n := by have := hn; nlinarith
  haveI : NeZero (G.n * G.n) := ⟨by omega⟩
  set c : ℕ → Fin (G.n * G.n) → ℚ := fun _ => QMCLeafB.RefutedM3.e₀ (G.n * G.n) with hc
  have hcne : ∀ k : ℕ, c k ≠ 0 := fun _ => QMCLeafB.RefutedM3.e₀_ne (G.n * G.n)
  set cd : ℕ → QMCLeafB.EngineIterates.CutData (G.n * G.n) :=
    QMCLeafB.RunPartsDilate.runCut G P hn c hcne with hcd
  have hrunwit : ∀ k,
      QMCLeafB.EngineIterates.Aat (G.n * G.n)
          (QMCLeafB.Boundary.initShapeOf (G.n * G.n)
            (2 * (G.n : ℚ) ^ 2 + 2 * P.dq ^ 2)) cd k *ᵥ (cd k).p = (cd k).c :=
    fun k => QMCLeafB.RunPartsDilate.runCut_wit G P hn c hcne k
  exact
    { ok := fun _ => true
      cd := cd
      del := fun _ => 0
      hcert := by intro k _ _; exact hmem
      hwit := by intro k _ hok; exact absurd hok (by simp)
      hrho := by intro k _ hok; exact absurd hok (by simp)
      hcne := by intro k _ hok; exact absurd hok (by simp)
      hdel0 := by intro k _ hok; exact absurd hok (by simp)
      hcheck := by intro k _ hok; exact absurd hok (by simp)
      hle := by intro k _ hok; exact absurd hok (by simp)
      hcut := by intro k _ hok; exact absurd hok (by simp)
      hverdict := by
        rw [hbit]
        exact (anyOk_const_true (P.K * P.m) (by omega)).symm }

/-! ## 4.  The `E` class is banked: bit false at an empty body -/

/-- **`hd` at the `E` class**, verbatim from `RefutedM3` (banked, published): the all-`cut` stream
with zero margins, `hcut` vacuous because the ball is empty. -/
noncomputable def runParts_of_emptyBody {o : QuantumMaxCutEnergy.Input → ℚ → Bool}
    {G : QuantumMaxCutEnergy.Input} {t : ℚ} (P : QMCLeafB.FinalStroke.RunParams G)
    (hn : 2 ≤ G.n) (hbit : o G t = false) (hempty : EmptyBody G t P) :
    QMCLeafB.FinalStroke.RunParts o G t P :=
  QMCLeafB.RefutedM3.runParts_of_emptyBody G t P hn hbit hempty

/-! ## 5.  The necessity half: the template forces bit soundness on any program -/

/-- **Every program that meets the template is bit-sound.**  If the bit reads `true` at an interior
point, some round `k < K·m` reported `ok` (`hverdict`), and that round's `hcert` is a genuine
unit-diagonal PSD point at `t + Rq/40000`.  So `M` is not an extra assumption of the assembly: it is
entailed by `hd` itself, and it is a cheap test any candidate program must pass. -/
theorem member_of_runParts {o : QuantumMaxCutEnergy.Input → ℚ → Bool}
    {G : QuantumMaxCutEnergy.Input} {t : ℚ} {P : QMCLeafB.FinalStroke.RunParams G}
    (B : QMCLeafB.FinalStroke.RunParts o G t P) (hbit : o G t = true) : MemberAt G t := by
  have h := B.hverdict
  rw [hbit] at h
  obtain ⟨k, hk, hok⟩ :=
    (QMCLeafB.SimLoop.anyOk_eq_true_iff B.ok (P.K * P.m)).mp h.symm
  exact B.hcert k hk hok

/-! ## 6.  The trichotomy: `hd` from the three classes -/

/-- **`hd` follows from the three classes.**  This is the template's hardest input, diffed down:

* `hE` — the program's bit is `false` wherever the relaxed body is empty (a program-side fact);
* `hM` — the program's bit is `true` only where a genuine unit-diagonal PSD point exists (also
  program-side; `member_of_runParts` shows the template entails it);
* `hC` — `RunParts` at the remaining strata: body non-empty and bit `false`.

Everything else is free (`runParts_of_member`, `runParts_of_emptyBody`). -/
noncomputable def hd_of_classes {o : QuantumMaxCutEnergy.Input → ℚ → Bool}
    (hE : ∀ (G : QuantumMaxCutEnergy.Input) (t : ℚ), 2 ≤ G.n → Interior G t →
      EmptyBody G t (QMCLeafB.UnionShallow.paramsKbc2 G) → o G t = false)
    (hM : ∀ (G : QuantumMaxCutEnergy.Input) (t : ℚ), 2 ≤ G.n → Interior G t →
      o G t = true → MemberAt G t)
    (hC : ∀ (G : QuantumMaxCutEnergy.Input) (t : ℚ), 2 ≤ G.n → Interior G t →
      ¬ EmptyBody G t (QMCLeafB.UnionShallow.paramsKbc2 G) → o G t = false →
      QMCLeafB.FinalStroke.RunParts o G t (QMCLeafB.UnionShallow.paramsKbc2 G)) :
    ∀ (G : QuantumMaxCutEnergy.Input) (t : ℚ), 2 ≤ G.n →
      -QMCLeafB.EngineRuntime.Rq G ≤ t →
      (t : ℝ) < -(((QMCLeafB.EngineRuntime.Rq G / 40000 : ℚ)) : ℝ) →
      QMCLeafB.FinalStroke.RunParts o G t (QMCLeafB.UnionShallow.paramsKbc2 G) := by
  intro G t hn hlo hhi
  have hint : Interior G t := ⟨hlo, hhi⟩
  by_cases hb : o G t = true
  · exact runParts_of_member (QMCLeafB.UnionShallow.paramsKbc2 G) hn
      (QMCLeafB.UnionShallow.one_le_Kbc2_mul G) hb (hM G t hn hint hb)
  · have hbf : o G t = false := by
      cases h : o G t with
      | false => rfl
      | true => exact absurd h hb
    by_cases he : EmptyBody G t (QMCLeafB.UnionShallow.paramsKbc2 G)
    · exact runParts_of_emptyBody (QMCLeafB.UnionShallow.paramsKbc2 G) hn
        (hE G t hn hint he) he
    · exact hC G t hn hint he hbf


/-! ## 7.  The top slice is `M`-consistent

`htop` forces the bit `true` on `-Rq/40000 ≤ t ≤ 0`; the `M` obligation (`hM` of `hd_of_classes`)
then asks for a genuine unit-diagonal PSD point at `t + Rq/40000 ≥ 0`.  The identity matrix is one:
`(wMatrix G * 1).trace = tr (wMatrix G) = 0 ≤ t + Rq/40000`.  So `htop` never contradicts the
soundness half of the program's bit — the top slice is exactly the range where the trivial
certificate exists, which is why the shift `+Rq/40000` is in the template. -/

theorem trace_wMatrix (G : QuantumMaxCutEnergy.Input) :
    (QMCLeafB.wMatrix G).trace = 0 := by
  simp only [Matrix.trace, Matrix.diag_apply]
  exact Finset.sum_eq_zero fun i _ => QMCLeafB.wMatrix_apply_of_eq

theorem member_identity {G : QuantumMaxCutEnergy.Input} {t : ℚ}
    (h : (0 : ℝ) ≤ (t : ℝ) + (((QMCLeafB.EngineRuntime.Rq G / 40000 : ℚ)) : ℝ)) :
    MemberAt G t := by
  refine ⟨1, ⟨?_, fun i => by simp⟩, ?_⟩
  · exact Matrix.PosSemidef.one
  · rw [Matrix.mul_one, trace_wMatrix]
    simpa using h

/-! ## 8.  The assembly: `d9f601e5` from the six inputs with `hd` diffed down -/

/-- **The template with `hd` replaced by the three classes.**  Same six inputs, same types, same
statement as `QMCLeafB.UnionShallow.solution_union_shallow_final`; only the last slot is weaker:
instead of one `RunParts` per interior point it asks for
`hE` (bit false on empty bodies), `hMemb` (bit true ⟹ a member at `t + Rq/40000`) and `hC`
(`RunParts` at body-non-empty, bit-false points — the campaign's thin band). -/
theorem solution_of_classes {σ : Type} [Coding σ]
    (k : ℕ) (hk : 20 ≤ 2 ^ k)
    (init : QMCLeafB.FuelWire.Pkg → σ) (round : σ → σ) (verdict : σ → Bool)
    (hinit : Poly init) (hr : Poly round) (hv : Poly verdict)
    (M : σ → ℕ) (C₀ c kr : ℕ) (hkr : 1 ≤ kr)
    (hMinv : ∀ s, M (round s) ≤ M s + c)
    (hstep : ∀ s, (enc (round s)).length ≤ max ((enc s).length + c) (M s))
    (hMsz : ∀ s, M s ≤ C₀ * ((enc s).length + 1) ^ kr)
    (hinitTape : ∀ p : QMCLeafB.FuelWire.Pkg,
      init p = init (QMCLeafB.FinalStroke.noTape p.1.1 p.2))
    (htop : ∀ (G : QuantumMaxCutEnergy.Input) (t : ℚ), 2 ≤ G.n →
      -(((QMCLeafB.EngineRuntime.Rq G / 40000 : ℚ)) : ℝ) ≤ (t : ℝ) → t ≤ 0 →
      QMCLeafB.FinalStroke.loopBit init round verdict Tbc2 G t = true)
    (hE : ∀ (G : QuantumMaxCutEnergy.Input) (t : ℚ), 2 ≤ G.n → Interior G t →
      EmptyBody G t (QMCLeafB.UnionShallow.paramsKbc2 G) →
      QMCLeafB.FinalStroke.loopBit init round verdict Tbc2 G t = false)
    (hMemb : ∀ (G : QuantumMaxCutEnergy.Input) (t : ℚ), 2 ≤ G.n → Interior G t →
      QMCLeafB.FinalStroke.loopBit init round verdict Tbc2 G t = true → MemberAt G t)
    (hC : ∀ (G : QuantumMaxCutEnergy.Input) (t : ℚ), 2 ≤ G.n → Interior G t →
      ¬ EmptyBody G t (QMCLeafB.UnionShallow.paramsKbc2 G) →
      QMCLeafB.FinalStroke.loopBit init round verdict Tbc2 G t = false →
      QMCLeafB.FinalStroke.RunParts
        (QMCLeafB.FinalStroke.loopBit init round verdict Tbc2) G t
        (QMCLeafB.UnionShallow.paramsKbc2 G)) :
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
  QMCLeafB.UnionShallow.solution_union_shallow_final k hk init round verdict
    hinit hr hv M C₀ c kr hkr hMinv hstep hMsz hinitTape htop
    (hd_of_classes hE hMemb hC)


/-! ## 9.  The sharpest form of the residual: the bit IS the body-nonemptiness bit

With §3/§4 in hand, the C class of `hd_of_classes` disappears as a *record* obligation and becomes a
*semantics* obligation: if the program's bit is `false` exactly at the empty-body points, then every
interior point is either an `E` point (bit false, banked record) or a non-empty-body point with the
bit `true` (member record), and `hd` is free.  The only remaining analytic input is then
`hbm : ¬EmptyBody → MemberAt`: the *rounding bridge*, "a non-empty relaxed body at level `t - eps`
carries a genuine unit-diagonal PSD point at level `t + eps`".  That bridge is the only place where
geometry survives in the template. -/

/-- **`hd` from the bit split.**  Two named residual slots and nothing else:

* `hbit` — the program's bit is `false` exactly at the empty-body interior points;
* `hbm` — a non-empty relaxed body at level `t - eps` carries a genuine unit-diagonal PSD point at
  level `t + eps` (the rounding bridge, independent of the program). -/
noncomputable def hd_of_bit_split {o : QuantumMaxCutEnergy.Input → ℚ → Bool}
    (hbit : ∀ (G : QuantumMaxCutEnergy.Input) (t : ℚ), 2 ≤ G.n → Interior G t →
      (o G t = false ↔ EmptyBody G t (QMCLeafB.UnionShallow.paramsKbc2 G)))
    (hbm : ∀ (G : QuantumMaxCutEnergy.Input) (t : ℚ), 2 ≤ G.n → Interior G t →
      ¬ EmptyBody G t (QMCLeafB.UnionShallow.paramsKbc2 G) → MemberAt G t) :
    ∀ (G : QuantumMaxCutEnergy.Input) (t : ℚ), 2 ≤ G.n →
      -QMCLeafB.EngineRuntime.Rq G ≤ t →
      (t : ℝ) < -(((QMCLeafB.EngineRuntime.Rq G / 40000 : ℚ)) : ℝ) →
      QMCLeafB.FinalStroke.RunParts o G t (QMCLeafB.UnionShallow.paramsKbc2 G) := by
  intro G t hn hlo hhi
  have hint : Interior G t := ⟨hlo, hhi⟩
  by_cases hb : o G t = true
  · have hne : ¬ EmptyBody G t (QMCLeafB.UnionShallow.paramsKbc2 G) := by
      intro he
      have hf : o G t = false := (hbit G t hn hint).mpr he
      rw [hf] at hb
      exact absurd hb (by simp)
    exact runParts_of_member (QMCLeafB.UnionShallow.paramsKbc2 G) hn
      (QMCLeafB.UnionShallow.one_le_Kbc2_mul G) hb (hbm G t hn hint hne)
  · have hbf : o G t = false := by
      cases h : o G t with
      | false => rfl
      | true => exact absurd h hb
    exact runParts_of_emptyBody (QMCLeafB.UnionShallow.paramsKbc2 G) hn hbf
      ((hbit G t hn hint).mp hbf)

/-- **The template with `hd` replaced by the bit split + the rounding bridge.**  Same six inputs,
same verbatim `d9f601e5` conclusion as `SubM1.solution`. -/
theorem solution_of_bit_split {σ : Type} [Coding σ]
    (k : ℕ) (hk : 20 ≤ 2 ^ k)
    (init : QMCLeafB.FuelWire.Pkg → σ) (round : σ → σ) (verdict : σ → Bool)
    (hinit : Poly init) (hr : Poly round) (hv : Poly verdict)
    (M : σ → ℕ) (C₀ c kr : ℕ) (hkr : 1 ≤ kr)
    (hMinv : ∀ s, M (round s) ≤ M s + c)
    (hstep : ∀ s, (enc (round s)).length ≤ max ((enc s).length + c) (M s))
    (hMsz : ∀ s, M s ≤ C₀ * ((enc s).length + 1) ^ kr)
    (hinitTape : ∀ p : QMCLeafB.FuelWire.Pkg,
      init p = init (QMCLeafB.FinalStroke.noTape p.1.1 p.2))
    (htop : ∀ (G : QuantumMaxCutEnergy.Input) (t : ℚ), 2 ≤ G.n →
      -(((QMCLeafB.EngineRuntime.Rq G / 40000 : ℚ)) : ℝ) ≤ (t : ℝ) → t ≤ 0 →
      QMCLeafB.FinalStroke.loopBit init round verdict Tbc2 G t = true)
    (hbit : ∀ (G : QuantumMaxCutEnergy.Input) (t : ℚ), 2 ≤ G.n → Interior G t →
      (QMCLeafB.FinalStroke.loopBit init round verdict Tbc2 G t = false ↔
        EmptyBody G t (QMCLeafB.UnionShallow.paramsKbc2 G)))
    (hbm : ∀ (G : QuantumMaxCutEnergy.Input) (t : ℚ), 2 ≤ G.n → Interior G t →
      ¬ EmptyBody G t (QMCLeafB.UnionShallow.paramsKbc2 G) → MemberAt G t) :
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
  solution_of_classes k hk init round verdict hinit hr hv M C₀ c kr hkr hMinv hstep hMsz
    hinitTape htop
    (fun G t hn hint he => (hbit G t hn hint).mpr he)
    (fun G t hn hint hb => hbm G t hn hint (by
      intro he
      have hf : QMCLeafB.FinalStroke.loopBit init round verdict Tbc2 G t = false :=
        (hbit G t hn hint).mpr he
      rw [hf] at hb
      exact absurd hb (by simp)))
    (fun G t hn hint hne hbf =>
      hd_of_bit_split hbit hbm G t hn hint.1 hint.2)


/-! ## 10.  Site receipts: the single-edge input `G₀` (`Rq = 1`)

`hd` is not vacuous at the reduction's own classes: at `G₀` the whole interior bracket is an `M`
class point (the banked witness `Z₀ = !![1,-1;-1,1]` has `tr (wMatrix G₀ · Z₀) = -1 = -Rq G₀`), so
every bit-true program's `hd` is discharged there with no new mathematics.  At the other end,
`(G₀, t₀)` has an empty body (`RefutedM3.body_empty_G₀`), where `RefutedM3.runParts_G₀_of_bitFalse`
discharges `hd` for every bit-false program at the template's own `paramsKbc2`. -/

/-- **`MemberAt` holds all over the interior at `G₀`.** -/
theorem memberAt_G₀ {t : ℚ} (ht : -1 ≤ t) : MemberAt QMCLeafB.ResidRefute.G₀ t := by
  refine ⟨QMCLeafB.ResidRefute.Z₀, QMCLeafB.ResidRefute.Z₀_isUnitDiagPSD, ?_⟩
  rw [QMCLeafB.ResidRefute.trace_G₀_Z₀, QMCLeafB.ResidRefute.Rq_G₀]
  have h1 : ((-1 : ℚ) : ℝ) ≤ (t : ℝ) := by exact_mod_cast ht
  have h1' : (-1 : ℝ) ≤ (t : ℝ) := by simpa using h1
  have h2 : (((1 : ℚ) / 40000 : ℚ) : ℝ) = 1 / 40000 := by norm_num
  rw [h2]
  linarith

/-- **`hd` is FREE at `G₀` for every bit-true program.** -/
noncomputable def hd_G₀_of_bit_true {σ : Type} [Coding σ]
    (init : QMCLeafB.FuelWire.Pkg → σ) (round : σ → σ) (verdict : σ → Bool) (t : ℚ)
    (hint : Interior QMCLeafB.ResidRefute.G₀ t)
    (hb : QMCLeafB.FinalStroke.loopBit init round verdict Tbc2 QMCLeafB.ResidRefute.G₀ t = true) :
    QMCLeafB.FinalStroke.RunParts
      (QMCLeafB.FinalStroke.loopBit init round verdict Tbc2) QMCLeafB.ResidRefute.G₀ t
      (QMCLeafB.UnionShallow.paramsKbc2 QMCLeafB.ResidRefute.G₀) := by
  have ht : -1 ≤ t := by
    have h1 := hint.1
    rw [QMCLeafB.ResidRefute.Rq_G₀] at h1
    exact h1
  exact runParts_of_member (P := QMCLeafB.UnionShallow.paramsKbc2 QMCLeafB.ResidRefute.G₀)
    QMCLeafB.ResidKill.hnG₀ (QMCLeafB.UnionShallow.one_le_Kbc2_mul _) hb (memberAt_G₀ ht)

/-- **`hd` is FREE at `G₀` for every bit-false program at the empty-body point** — banked. -/
noncomputable def hd_G₀_at_empty (o : QuantumMaxCutEnergy.Input → ℚ → Bool)
    (hb : o QMCLeafB.ResidRefute.G₀ QMCLeafB.EmptyBodyM5.t₀ = false) :
    QMCLeafB.FinalStroke.RunParts o QMCLeafB.ResidRefute.G₀ QMCLeafB.EmptyBodyM5.t₀
      (QMCLeafB.UnionShallow.paramsKbc2 QMCLeafB.ResidRefute.G₀) :=
  QMCLeafB.RefutedM3.runParts_G₀_of_bitFalse o hb

end AsmM8




/-! ## Axiom audit -/

#print axioms AsmM8.anyOk_const_true
#print axioms AsmM8.runParts_of_member
#print axioms AsmM8.runParts_of_emptyBody
#print axioms AsmM8.member_of_runParts
#print axioms AsmM8.trace_wMatrix
#print axioms AsmM8.member_identity
#print axioms AsmM8.solution_of_classes
#print axioms AsmM8.hd_of_classes
#print axioms AsmM8.hd_of_bit_split
#print axioms AsmM8.solution_of_bit_split
#print axioms AsmM8.memberAt_G₀
#print axioms AsmM8.hd_G₀_of_bit_true
#print axioms AsmM8.hd_G₀_at_empty


