-- Prove2me | Definitions.Def_QMCLeafB_hokupper34
-- name    : QMCLeafB_hokupper34
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-05T12:13:34.483289+00:00
-- url     : https://prove2.me/theorems/a3137e6d-5768-43ec-9716-913d7414b87d
-- title:
--   QMCLeafB hokupper34
-- statement:
--   # `Check_hokupper34_m8` — phase 34, member m8, direction d9 `upper-side`
--
--   Published as part of the QMCLeafB library mirror supporting the quantum max-cut campaign's polynomial-time SDP-value certificate (AGM20, TQC 2020, arXiv 2003.14394).

import Mathlib
import Definitions.Def_QMCLeafB_conformance_m8
import Definitions.Def_QMCLeafB_asm_m8
import Definitions.Def_QMCLeafB_topSlice
import Definitions.Def_QMCLeafB_asm2
import Definitions.Def_QMCLeafB_centre_adm_m1
import Definitions.Def_QMCLeafB_pivexact
import Definitions.Def_QMCLeafB_stateDiag
import Definitions.Def_QMCLeafB_htop_oklower_m7
import Definitions.Def_QMCLeafB_finalization
import Definitions.Def_QMCLeafB_sim_loop_m6
import Definitions.Def_QMCLeafB_runparams_shallow_m5
import Definitions.Def_QMCLeafB_ldltcert2_m5
/-
# `Check_hokupper34_m8` — phase 34, member m8, direction d9 `upper-side`

**The upper side of leaf B, at the released gate: `ok` at the *relaxed* test ⇒ the symmetric
rational `RelaxMem` that `hok` asks for.**

Phase 33 left the whole 0.53/0.526 leaf as two slots at the concrete campaign bit
(`Check_pbit33_m6`):

    hok    : o33 G t = true  ⟹  ∃ cX, cXᵀ = cX ∧ RelaxMem (wMatrixQ G) cX (t − eps G) (dqShallow G)
    hfalse : o33 G t = false ⟹  RunParts o33 G t (P33 G)

and this file closes the *upper* one **as an implication from the gate data at the ok round**, i.e.
in the form every released-gate programme can instantiate and no programme-shape can get around:

* §1 the state's `dvR` bounds each diagonal deviation — `|Xᵢᵢ − 1| ≤ dvR s` at every coordinate.
  This is what makes a **sum** gate (`dvR s ≤ dq/4`) a *sound* diagonal clause for `RelaxMem`,
  whose `diag_near` is per-coordinate.
* §2 **the released-gate soundness** (`relaxMem_diagPinch_of_gate`): a zero-diagonal weight matrix
  and a rational centre `Q` with

      Q ⪰ 0  (EXACT PSD — the descent's `false`),   |Qᵢᵢ − 1| ≤ dq/4  (tolerance, not exact unit
      diagonal),   ⟪A,Q⟫ ≤ u + dq/2

  have the **pinched** centre `diagPinch Q dq` as a `RelaxMem A · u dq` member.  This is
  `CentreAdm.relaxMem_diagPinch` with the unit-diagonal hypothesis replaced by the campaign's
  released tolerance — the exact weakening the exact-diagonal gate retired in phase 32 needs
  (`Check_refute32_m4`: the exact gate never fires at `(G₀,−1/2)`).
* §3 **the state form** (`relaxMem_of_stateGate`): the same at a run state `s`, reading
  `dvR s ≤ dq/4`, the pivot answer `runPiv … = false` (PSD by `PivExact.psd_of_false`), the trace
  clause `fvR s ≤ (t − eps) + dq/2`, the state/weight-matrix coherence `stMat G.n (stA s) = wMatrixQ G`
  and the orbit symmetry.  Conclusion: the symmetric rational `diagPinch (stMat …) dq` is a member.
* §4 **the bit form** (`exists_relaxMem_of_okStream`): along ANY state stream `σ` whose `ok` test
  reports `true` only with the §3 data, and with the level/tolerance coherence
  `stT (σ k) − epsOf (σ k) = t − eps G`, `dqOf (σ k) = dq`, a `true` loop bit (`anyOk`) yields the
  member.  No hypothesis on the round, the descent, the count or the record — this is `hok`'s
  content, programme-free.
* §5 the **`hok` slot verbatim** (`hokShape_of_releasedGate`, `HokShape`): at the campaign
  parameters, `dq := dqShallow G`, level `t − eps G`, with `0 < dqShallow G` and `dqShallow G ≤ 4`
  discharged from the banked `RundataParams.dqShallow_pos` / `CentreAdm.dqShallow_le_four`.

What is *not* claimed here: that the campaign bit `o33` (`roundGT`'s own flag, which tests
`fvR ≤ stT + epsOf` / `¬(oracleR s).1` — the *upper* event) satisfies §4's `hok` test slot; the
released programme has to supply the test.  `Automatic.Poly` of the released test is likewise not
built here: the PSD clause is carried in `∃ acc, runPiv … = false` form (the engine's own pivot
answer at some accumulator suffices; `RoundProgram.pivAns` is the canonical one and
`RoundProgram.poly_pivAns` its `Poly` proof).

Discipline: `set_option autoImplicit false`; no `sorry`/`admit`/`axiom`/`native_decide`/`unsafe`;
`#print axioms` after every declaration (closures below are exactly
`[propext, Classical.choice, Quot.sound]`).
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option linter.unusedVariables false

noncomputable section
open scoped BigOperators
open Matrix

namespace HokUpper34M8

open QuantumMaxCutEnergy

/-! ## 0.  List-sum helpers (a single term is at most the sum of non-negative terms) -/

theorem list_sum_nonneg {l : List ℚ} (h : ∀ x ∈ l, 0 ≤ x) : 0 ≤ l.sum := by
  induction l with
  | nil => exact le_refl 0
  | cons a as ih =>
      rw [List.sum_cons]
      have ha : 0 ≤ a := h a (List.mem_cons_self ..)
      have hs : 0 ≤ as.sum := ih (fun x hx => h x (List.mem_cons_of_mem _ hx))
      linarith

theorem le_list_sum {l : List ℚ} (hnn : ∀ x ∈ l, 0 ≤ x) {a : ℚ} (ha : a ∈ l) : a ≤ l.sum := by
  induction l with
  | nil => exact absurd ha (List.not_mem_nil)
  | cons b bs ih =>
      rw [List.sum_cons]
      rcases List.mem_cons.mp ha with rfl | hmem
      · have hs : 0 ≤ bs.sum := list_sum_nonneg (fun x hx => hnn x (List.mem_cons_of_mem _ hx))
        linarith
      · have hb : 0 ≤ b := hnn b (List.mem_cons_self ..)
        have := ih (fun x hx => hnn x (List.mem_cons_of_mem _ hx)) hmem
        linarith

/-! ## 1.  `dvR` bounds every diagonal deviation -/

/-- **The sum gate is a sound diagonal clause.**  At a state whose code is long enough, each
deviation `|Xᵢᵢ − 1|` is at most the engine's own read-out `dvR s = ∑ᵢ |Xᵢᵢ − 1|`.  Hence
`dvR s ≤ dq/4` implies `RelaxMem`'s per-coordinate `diag_near` at tolerance `dq` — the direction
phase 32's `Check_rtest32_m8` leaves open (its `diag_of_dsum_le` is the matrix-level twin). -/
theorem abs_stMat_diag_le_dvR {n : ℕ} {s : QMCLeafB.RoundProgram.RSt}
    (hN : QMCLeafB.RoundProgram.stN s = n)
    (hlenX : n ≤ (QMCLeafB.RoundProgram.stX s).length) (i : Fin n) :
    |QMCLeafB.StateDiag.stMat n (QMCLeafB.RoundProgram.stX s) i i - 1|
      ≤ QMCLeafB.RoundProgram.dvR s := by
  have hsum : QMCLeafB.RoundProgram.dvR s
      = ((List.range n).map
          (fun k => |QMCLeafB.RoundProgram.entV (n, QMCLeafB.RoundProgram.stX s) k k - 1|)).sum := by
    unfold QMCLeafB.RoundProgram.dvR QMCLeafB.RoundProgram.diagSumV
    rw [hN, QMCLeafB.StateDiag.idxs_of_le hlenX]
    exact congrArg List.sum
      (List.map_congr_left (fun k _ => QMCLeafB.RoundProgram.absq_eq _))
  rw [hsum]
  show |QMCLeafB.RoundProgram.entV (n, QMCLeafB.RoundProgram.stX s) i.1 i.1 - 1| ≤ _
  refine le_list_sum (fun x hx => ?_) ?_
  · obtain ⟨k, -, rfl⟩ := List.mem_map.mp hx
    exact abs_nonneg _
  · exact List.mem_map.mpr ⟨i.1, List.mem_range.mpr i.2, rfl⟩

#print axioms HokUpper34M8.abs_stMat_diag_le_dvR

/-! ## 2.  The released gate is sound for the `ok` test (matrix form) -/

/-- **`relaxMem_diagPinch_of_gate`** — the released gate's soundness.  Exact PSD plus the
*per-coordinate* diagonal tolerance `dq/4` (implied by the engine's sum gate `dvR ≤ dq/4`, §1) plus
the trace clause put the **pinched** centre inside the relaxation.  Compare
`CentreAdm.relaxMem_diagPinch`, which needs the exact unit diagonal: the tolerance is what the
phase-32 refutation `Check_refute32_m4` forces, since a body with no unit-diagonal member is
non-empty at `(G₀,−1/2)` and the exact gate never fires there. -/
theorem relaxMem_diagPinch_of_gate {n : ℕ} {A Q : Matrix (Fin n) (Fin n) ℚ} {u dq : ℚ}
    (hA : ∀ i, A i i = 0) (hdq : 0 < dq) (hdq4 : dq ≤ 4)
    (hpsd : ∀ x : Fin n → ℚ, 0 ≤ QMCLeafB.SepOracle.qf Q x)
    (hdiag : ∀ i, |Q i i - 1| ≤ dq / 4)
    (htrace : QMCLeafB.SepOracle.frob A Q ≤ u + dq / 2) :
    QMCLeafB.RelaxOracle.RelaxMem A (QMCLeafB.CentreAdm.diagPinch Q dq) u dq := by
  refine ⟨hdq, ?_, fun i => QMCLeafB.CentreAdm.abs_diagPinch Q hdq hdq4 i, ?_⟩
  · intro x
    rw [QMCLeafB.CentreAdm.qf_diagPinch]
    have hterm : ∀ i : Fin n, (-(dq / 2)) * x i ^ 2 ≤ ((1 - dq / 4) - Q i i) * x i ^ 2 := by
      intro i
      have h1 : -(dq / 2) ≤ (1 - dq / 4) - Q i i := by
        have h2 := abs_le.mp (hdiag i)
        linarith [h2.1, h2.2]
      exact mul_le_mul_of_nonneg_right h1 (sq_nonneg (x i))
    have hsum : (-(dq / 2)) * (∑ i, x i ^ 2)
        ≤ ∑ i, ((1 - dq / 4) - Q i i) * x i ^ 2 := by
      rw [Finset.mul_sum]
      exact Finset.sum_le_sum (fun i _ => hterm i)
    have hp := hpsd x
    linarith
  · rw [QMCLeafB.CentreAdm.frob_diagPinch hA]
    exact htrace

#print axioms HokUpper34M8.relaxMem_diagPinch_of_gate

/-! ## 3.  The same at a run state -/

/-- **`relaxMem_of_stateGate`** — the released gate read off the engine's own state.  The PSD clause
is the pivot answer (`PivExact.psd_of_false`), the diagonal clause is the engine's sum gate, the
trace clause is the engine's `fvR ≤ level`, and the level is the caller's `t − eps G`.  The witness
is the pinched centre — symmetric (orbit symmetry) and rational by construction. -/
theorem relaxMem_of_stateGate {G : QuantumMaxCutEnergy.Input} {t dq : ℚ}
    {s : QMCLeafB.RoundProgram.RSt} {acc : QMCLeafB.PivotProgram.Acc}
    (hN : QMCLeafB.RoundProgram.stN s = G.n)
    (hlenA : G.n ≤ (QMCLeafB.RoundProgram.stA s).length)
    (hlenX : G.n ≤ (QMCLeafB.RoundProgram.stX s).length)
    (hA : QMCLeafB.StateDiag.stMat G.n (QMCLeafB.RoundProgram.stA s)
      = QMCLeafB.Finalization.wMatrixQ G)
    (hsym : ∀ i j, QMCLeafB.StateDiag.stMat G.n (QMCLeafB.RoundProgram.stX s) i j
      = QMCLeafB.StateDiag.stMat G.n (QMCLeafB.RoundProgram.stX s) j i)
    (hpiv : (QMCLeafB.PivotProgram.runPiv
      (QMCLeafB.RoundProgram.toRows (G.n, QMCLeafB.RoundProgram.stX s), acc)).1 = false)
    (hdv : QMCLeafB.RoundProgram.dvR s ≤ dq / 4)
    (hfv : QMCLeafB.RoundProgram.fvR s ≤ t - QMCLeafB.RundataCert.eps G + dq / 2)
    (hdq : 0 < dq) (hdq4 : dq ≤ 4) :
    ∃ cX : Matrix (Fin G.n) (Fin G.n) ℚ, cXᵀ = cX ∧
      QMCLeafB.RelaxOracle.RelaxMem (QMCLeafB.Finalization.wMatrixQ G) cX
        (t - QMCLeafB.RundataCert.eps G) dq := by
  have hpsd : ∀ x : Fin G.n → ℚ,
      0 ≤ QMCLeafB.SepOracle.qf
        (QMCLeafB.StateDiag.stMat G.n (QMCLeafB.RoundProgram.stX s)) x :=
    QMCLeafB.PivExact.psd_of_false (X := QMCLeafB.RoundProgram.stX s) (acc := acc)
      hlenX (fun i j => hsym i j) hpiv
  have hdiag : ∀ i : Fin G.n,
      |QMCLeafB.StateDiag.stMat G.n (QMCLeafB.RoundProgram.stX s) i i - 1| ≤ dq / 4 :=
    fun i => le_trans (abs_stMat_diag_le_dvR hN hlenX i) hdv
  have htrace : QMCLeafB.SepOracle.frob (QMCLeafB.Finalization.wMatrixQ G)
      (QMCLeafB.StateDiag.stMat G.n (QMCLeafB.RoundProgram.stX s))
      ≤ (t - QMCLeafB.RundataCert.eps G) + dq / 2 := by
    rw [← hA, ← QMCLeafB.StateDiag.fvR_eq_frob hN hlenA hlenX]
    exact hfv
  refine ⟨QMCLeafB.CentreAdm.diagPinch
    (QMCLeafB.StateDiag.stMat G.n (QMCLeafB.RoundProgram.stX s)) dq, ?_, ?_⟩
  · funext i j
    rw [Matrix.transpose_apply]
    by_cases hij : i = j
    · subst hij
      rfl
    · rw [QMCLeafB.CentreAdm.diagPinch_off (Ne.symm hij), QMCLeafB.CentreAdm.diagPinch_off hij]
      exact hsym j i
  · exact relaxMem_diagPinch_of_gate (A := QMCLeafB.Finalization.wMatrixQ G)
      (fun i => QMCLeafB.Finalization.wMatrixQ_apply_of_eq) hdq hdq4 hpsd hdiag htrace

#print axioms HokUpper34M8.relaxMem_of_stateGate

/-! ## 4.  The bit form: a `true` loop bit whose ok test is the gate gives the member -/

/-- **`exists_relaxMem_of_okStream`** — `hok`'s content, programme-free.  Along any state stream
`σ` with the campaign's level and tolerance at every `ok`-reporting round
(`stT − epsOf = t − eps G`, `dqOf = dq`) and the gate data of §3 there, a `true` loop bit yields the
symmetric rational member.  Nothing is assumed about the round map, the descent, the count or the
record: the only content is the ok test's semantics. -/
theorem exists_relaxMem_of_okStream {G : QuantumMaxCutEnergy.Input} {t dq : ℚ} {T : ℕ}
    {σ : ℕ → QMCLeafB.RoundProgram.RSt} {o : QuantumMaxCutEnergy.Input → ℚ → Bool}
    {okT : QMCLeafB.RoundProgram.RSt → Bool}
    (hbit : o G t = QMCLeafB.SimLoop.anyOk (fun k => okT (σ k)) T)
    (hbt : o G t = true)
    (hdat : ∀ k, k < T → okT (σ k) = true →
      QMCLeafB.RoundProgram.stN (σ k) = G.n ∧
      G.n ≤ (QMCLeafB.RoundProgram.stA (σ k)).length ∧
      G.n ≤ (QMCLeafB.RoundProgram.stX (σ k)).length ∧
      QMCLeafB.StateDiag.stMat G.n (QMCLeafB.RoundProgram.stA (σ k))
        = QMCLeafB.Finalization.wMatrixQ G ∧
      (∀ i j, QMCLeafB.StateDiag.stMat G.n (QMCLeafB.RoundProgram.stX (σ k)) i j
        = QMCLeafB.StateDiag.stMat G.n (QMCLeafB.RoundProgram.stX (σ k)) j i))
    (hpiv : ∀ k, k < T → okT (σ k) = true → ∃ acc : QMCLeafB.PivotProgram.Acc,
      (QMCLeafB.PivotProgram.runPiv
        (QMCLeafB.RoundProgram.toRows (G.n, QMCLeafB.RoundProgram.stX (σ k)), acc)).1 = false)
    (hdv : ∀ k, k < T → okT (σ k) = true → QMCLeafB.RoundProgram.dvR (σ k) ≤ dq / 4)
    (hfv : ∀ k, k < T → okT (σ k) = true →
      QMCLeafB.RoundProgram.fvR (σ k)
        ≤ QMCLeafB.RoundProgram.stT (σ k) - QMCLeafB.RoundT.epsOf (σ k)
          + QMCLeafB.OkLower.dqOf (σ k) / 2)
    (hlev : ∀ k, k < T → okT (σ k) = true →
      QMCLeafB.RoundProgram.stT (σ k) - QMCLeafB.RoundT.epsOf (σ k)
        = t - QMCLeafB.RundataCert.eps G)
    (hdqv : ∀ k, k < T → okT (σ k) = true → QMCLeafB.OkLower.dqOf (σ k) = dq)
    (hdq : 0 < dq) (hdq4 : dq ≤ 4) :
    ∃ cX : Matrix (Fin G.n) (Fin G.n) ℚ, cXᵀ = cX ∧
      QMCLeafB.RelaxOracle.RelaxMem (QMCLeafB.Finalization.wMatrixQ G) cX
        (t - QMCLeafB.RundataCert.eps G) dq := by
  have hany : QMCLeafB.SimLoop.anyOk (fun k => okT (σ k)) T = true := by
    rw [← hbit]
    exact hbt
  obtain ⟨k, hk, hok⟩ := (QMCLeafB.SimLoop.anyOk_eq_true_iff (fun k => okT (σ k)) T).mp hany
  obtain ⟨hN, hlenA, hlenX, hA, hsym⟩ := hdat k hk hok
  obtain ⟨acc, hpivk⟩ := hpiv k hk hok
  have hfv' : QMCLeafB.RoundProgram.fvR (σ k)
      ≤ (t - QMCLeafB.RundataCert.eps G) + dq / 2 := by
    have h := hfv k hk hok
    rw [hlev k hk hok, hdqv k hk hok] at h
    exact h
  exact relaxMem_of_stateGate hN hlenA hlenX hA hsym hpivk (hdv k hk hok) hfv' hdq hdq4

#print axioms HokUpper34M8.exists_relaxMem_of_okStream

/-! ## 5.  The `hok` slot verbatim, at the campaign's level and tolerance -/

/-- **`hok`'s conclusion shape** — exactly the first argument of `Pbit33.Hd33_of_relaxMem`, i.e.
`∃ cX, cXᵀ = cX ∧ RelaxMem (wMatrixQ G) cX (t − eps G) (dqShallow G)`. -/
def HokShape (G : QuantumMaxCutEnergy.Input) (t : ℚ) : Prop :=
  ∃ cX : Matrix (Fin G.n) (Fin G.n) ℚ, cXᵀ = cX ∧
    QMCLeafB.RelaxOracle.RelaxMem (QMCLeafB.Finalization.wMatrixQ G) cX
      (t - QMCLeafB.RundataCert.eps G) (QMCLeafB.RundataParams.dqShallow G)

/-- **The released gate closes the upper side.**  At the campaign tolerance `dqShallow G` (positive
and `≤ 4` from the banked `RundataParams.dqShallow_pos` / `CentreAdm.dqShallow_le_four`), a loop bit
whose `ok` test reports only with the §3 gate data at the campaign's own level has `hok`'s
conclusion.  This is the slot `Pbit33.Hd33_of_relaxMem`/`Res33M4.solution_of_slots` assume. -/
theorem hokShape_of_releasedGate {G : QuantumMaxCutEnergy.Input} {t : ℚ} {T : ℕ}
    {σ : ℕ → QMCLeafB.RoundProgram.RSt} {o : QuantumMaxCutEnergy.Input → ℚ → Bool}
    {okT : QMCLeafB.RoundProgram.RSt → Bool}
    (hRq : 0 < QMCLeafB.EngineRuntime.Rq G)
    (hbit : o G t = QMCLeafB.SimLoop.anyOk (fun k => okT (σ k)) T)
    (hbt : o G t = true)
    (hdat : ∀ k, k < T → okT (σ k) = true →
      QMCLeafB.RoundProgram.stN (σ k) = G.n ∧
      G.n ≤ (QMCLeafB.RoundProgram.stA (σ k)).length ∧
      G.n ≤ (QMCLeafB.RoundProgram.stX (σ k)).length ∧
      QMCLeafB.StateDiag.stMat G.n (QMCLeafB.RoundProgram.stA (σ k))
        = QMCLeafB.Finalization.wMatrixQ G ∧
      (∀ i j, QMCLeafB.StateDiag.stMat G.n (QMCLeafB.RoundProgram.stX (σ k)) i j
        = QMCLeafB.StateDiag.stMat G.n (QMCLeafB.RoundProgram.stX (σ k)) j i))
    (hpiv : ∀ k, k < T → okT (σ k) = true → ∃ acc : QMCLeafB.PivotProgram.Acc,
      (QMCLeafB.PivotProgram.runPiv
        (QMCLeafB.RoundProgram.toRows (G.n, QMCLeafB.RoundProgram.stX (σ k)), acc)).1 = false)
    (hdv : ∀ k, k < T → okT (σ k) = true →
      QMCLeafB.RoundProgram.dvR (σ k) ≤ QMCLeafB.RundataParams.dqShallow G / 4)
    (hfv : ∀ k, k < T → okT (σ k) = true →
      QMCLeafB.RoundProgram.fvR (σ k)
        ≤ QMCLeafB.RoundProgram.stT (σ k) - QMCLeafB.RoundT.epsOf (σ k)
          + QMCLeafB.OkLower.dqOf (σ k) / 2)
    (hlev : ∀ k, k < T → okT (σ k) = true →
      QMCLeafB.RoundProgram.stT (σ k) - QMCLeafB.RoundT.epsOf (σ k)
        = t - QMCLeafB.RundataCert.eps G)
    (hdqv : ∀ k, k < T → okT (σ k) = true →
      QMCLeafB.OkLower.dqOf (σ k) = QMCLeafB.RundataParams.dqShallow G) :
    HokShape G t :=
  exists_relaxMem_of_okStream hbit hbt hdat hpiv hdv hfv hlev hdqv
    (QMCLeafB.RundataParams.dqShallow_pos G)
    (QMCLeafB.CentreAdm.dqShallow_le_four G hRq)

#print axioms HokUpper34M8.hokShape_of_releasedGate

/-- **The upper side in the `Hd33_of_relaxMem` binder shape.**  Same content as
`hokShape_of_releasedGate`, quantified exactly as the slot `Pbit33.Hd33_of_relaxMem` consumes it
(`2 ≤ G.n`, the bracket `−Rq ≤ t`, `t < −eps`), so it plugs in with no adaptation. -/
theorem hok_of_releasedGate (o : QuantumMaxCutEnergy.Input → ℚ → Bool)
    (okT : QMCLeafB.RoundProgram.RSt → Bool)
    (σ : QuantumMaxCutEnergy.Input → ℚ → ℕ → QMCLeafB.RoundProgram.RSt)
    (T : QuantumMaxCutEnergy.Input → ℕ)
    (hRq : ∀ G : QuantumMaxCutEnergy.Input, 0 < QMCLeafB.EngineRuntime.Rq G)
    (hbit : ∀ (G : QuantumMaxCutEnergy.Input) (t : ℚ),
      o G t = QMCLeafB.SimLoop.anyOk (fun k => okT (σ G t k)) (T G))
    (hdat : ∀ (G : QuantumMaxCutEnergy.Input) (t : ℚ) (k : ℕ), k < T G →
      okT (σ G t k) = true →
      QMCLeafB.RoundProgram.stN (σ G t k) = G.n ∧
      G.n ≤ (QMCLeafB.RoundProgram.stA (σ G t k)).length ∧
      G.n ≤ (QMCLeafB.RoundProgram.stX (σ G t k)).length ∧
      QMCLeafB.StateDiag.stMat G.n (QMCLeafB.RoundProgram.stA (σ G t k))
        = QMCLeafB.Finalization.wMatrixQ G ∧
      (∀ i j, QMCLeafB.StateDiag.stMat G.n (QMCLeafB.RoundProgram.stX (σ G t k)) i j
        = QMCLeafB.StateDiag.stMat G.n (QMCLeafB.RoundProgram.stX (σ G t k)) j i))
    (hpiv : ∀ (G : QuantumMaxCutEnergy.Input) (t : ℚ) (k : ℕ), k < T G →
      okT (σ G t k) = true → ∃ acc : QMCLeafB.PivotProgram.Acc,
      (QMCLeafB.PivotProgram.runPiv
        (QMCLeafB.RoundProgram.toRows (G.n, QMCLeafB.RoundProgram.stX (σ G t k)), acc)).1 = false)
    (hdv : ∀ (G : QuantumMaxCutEnergy.Input) (t : ℚ) (k : ℕ), k < T G →
      okT (σ G t k) = true →
      QMCLeafB.RoundProgram.dvR (σ G t k) ≤ QMCLeafB.RundataParams.dqShallow G / 4)
    (hfv : ∀ (G : QuantumMaxCutEnergy.Input) (t : ℚ) (k : ℕ), k < T G →
      okT (σ G t k) = true →
      QMCLeafB.RoundProgram.fvR (σ G t k)
        ≤ QMCLeafB.RoundProgram.stT (σ G t k) - QMCLeafB.RoundT.epsOf (σ G t k)
          + QMCLeafB.OkLower.dqOf (σ G t k) / 2)
    (hlev : ∀ (G : QuantumMaxCutEnergy.Input) (t : ℚ) (k : ℕ), k < T G →
      okT (σ G t k) = true →
      QMCLeafB.RoundProgram.stT (σ G t k) - QMCLeafB.RoundT.epsOf (σ G t k)
        = t - QMCLeafB.RundataCert.eps G)
    (hdqv : ∀ (G : QuantumMaxCutEnergy.Input) (t : ℚ) (k : ℕ), k < T G →
      okT (σ G t k) = true →
      QMCLeafB.OkLower.dqOf (σ G t k) = QMCLeafB.RundataParams.dqShallow G) :
    ∀ (G : QuantumMaxCutEnergy.Input) (t : ℚ), 2 ≤ G.n →
      -QMCLeafB.EngineRuntime.Rq G ≤ t →
      (t : ℝ) < -(((QMCLeafB.RundataCert.eps G : ℚ)) : ℝ) →
      o G t = true → HokShape G t := by
  intro G t _ _ _ hb
  exact hokShape_of_releasedGate (hRq G) (hbit G t) hb (fun k hk hok => hdat G t k hk hok)
    (fun k hk hok => hpiv G t k hk hok) (fun k hk hok => hdv G t k hk hok)
    (fun k hk hok => hfv G t k hk hok) (fun k hk hok => hlev G t k hk hok)
    (fun k hk hok => hdqv G t k hk hok)

#print axioms HokUpper34M8.hok_of_releasedGate


/-! ## 6.  The concrete released test: the certified-run gate -/

/-- The engine's own certified-run check at a state: `EvRunB` is a `Bool` (verifiable pointwise,
`LdltCertM5.evRun_of_evRunB`), and at radius `0` it says the descent's trajectory *is* the exact
rational LDLᵀ trajectory — which is what turns `pivAns = false` into exact PSD
(`LdltCertM5.psd_of_exactRun`). -/
def evGate (s : QMCLeafB.RoundProgram.RSt) : Bool :=
  QMCLeafB.LdltCertM5.EvRunB (QMCLeafB.RoundProgram.stMu s) (QMCLeafB.RoundProgram.stD s) 0
    (QMCLeafB.RoundProgram.stN s)
    ((QMCLeafB.RoundProgram.stMu s, QMCLeafB.RoundProgram.stD s),
      (QMCLeafB.RoundProgram.toRows (QMCLeafB.RoundProgram.stN s, QMCLeafB.RoundProgram.stX s),
        ([] : QMCLeafB.PivotProgram.Acc)))

/-- **The released `ok` test**, at the state: the certified exact run, the released diagonal gate
`dvR ≤ dqOf/4`, the exact pivot answer, and the lower-body trace test.  Every component is a
`Bool`-valued state read-out (`Automatic.Poly` of `dvR`, `dqOf`, `fvR`, `levelOf`, `pivAns`,
`EvRunB` are the banked `poly_*` slots / a fuel induction), and it is *sound for membership* by
`relaxMem_diagPinch_of_gate` below. -/
def okRel (s : QMCLeafB.RoundProgram.RSt) : Bool :=
  (evGate s && decide (QMCLeafB.RoundProgram.dvR s ≤ QMCLeafB.OkLower.dqOf s / 4))
    && (decide ((QMCLeafB.RoundProgram.pivAns s).1 = false)
      && decide (QMCLeafB.RoundProgram.fvR s ≤ QMCLeafB.OkLower.levelOf s))

/-- **What the released test certifies.** -/
theorem okRel_spec {s : QMCLeafB.RoundProgram.RSt} (h : okRel s = true) :
    evGate s = true ∧ QMCLeafB.RoundProgram.dvR s ≤ QMCLeafB.OkLower.dqOf s / 4 ∧
      (QMCLeafB.RoundProgram.pivAns s).1 = false ∧
      QMCLeafB.RoundProgram.fvR s ≤ QMCLeafB.OkLower.levelOf s := by
  simp only [okRel, Bool.and_eq_true, decide_eq_true_eq] at h
  exact ⟨h.1.1, h.1.2, h.2.1, h.2.2⟩

#print axioms HokUpper34M8.okRel_spec

/-- The diagonal overwrite preserves symmetry. -/
theorem diagPinch_symm {n : ℕ} {Q : Matrix (Fin n) (Fin n) ℚ} {dq : ℚ}
    (hsym : ∀ i j, Q i j = Q j i) :
    (QMCLeafB.CentreAdm.diagPinch Q dq)ᵀ = QMCLeafB.CentreAdm.diagPinch Q dq := by
  funext i j
  rw [Matrix.transpose_apply]
  by_cases hij : i = j
  · subst hij
    rfl
  · rw [QMCLeafB.CentreAdm.diagPinch_off (Ne.symm hij), QMCLeafB.CentreAdm.diagPinch_off hij]
    exact hsym j i

#print axioms HokUpper34M8.diagPinch_symm

/-- **The released test at a run state gives the member.**  `okRel s = true` discharges every clause
of §2 — the PSD clause through the certified exact run, the diagonal clause through `dvR ≤ dq/4`
(§1), the trace clause through the engine's own `fvR ≤ levelOf` — so the pinched centre is a
symmetric rational `RelaxMem` at the level `stT s − epsOf s` and tolerance `dqOf s`. -/
theorem relaxMem_of_okRel {G : QuantumMaxCutEnergy.Input} {t dq : ℚ}
    {s : QMCLeafB.RoundProgram.RSt}
    (hN : QMCLeafB.RoundProgram.stN s = G.n)
    (hlenA : G.n ≤ (QMCLeafB.RoundProgram.stA s).length)
    (hlenX : G.n ≤ (QMCLeafB.RoundProgram.stX s).length)
    (hA : QMCLeafB.StateDiag.stMat G.n (QMCLeafB.RoundProgram.stA s)
      = QMCLeafB.Finalization.wMatrixQ G)
    (hsym : ∀ i j, QMCLeafB.StateDiag.stMat G.n (QMCLeafB.RoundProgram.stX s) i j
      = QMCLeafB.StateDiag.stMat G.n (QMCLeafB.RoundProgram.stX s) j i)
    (hok : okRel s = true)
    (hlev : QMCLeafB.RoundProgram.stT s - QMCLeafB.RoundT.epsOf s
      = t - QMCLeafB.RundataCert.eps G)
    (hdqv : QMCLeafB.OkLower.dqOf s = dq)
    (hdq : 0 < dq) (hdq4 : dq ≤ 4) :
    ∃ cX : Matrix (Fin G.n) (Fin G.n) ℚ, cXᵀ = cX ∧
      QMCLeafB.RelaxOracle.RelaxMem (QMCLeafB.Finalization.wMatrixQ G) cX
        (t - QMCLeafB.RundataCert.eps G) dq := by
  obtain ⟨hevB, hdv, hpiv, hfv⟩ := okRel_spec hok
  have hlen' : QMCLeafB.RoundProgram.stN s ≤ (QMCLeafB.RoundProgram.stX s).length :=
    hN.symm ▸ hlenX
  have hsym' : ∀ i j, QMCLeafB.PivExact.matOf (QMCLeafB.RoundProgram.stN s)
        (QMCLeafB.RoundProgram.stX s) i j
      = QMCLeafB.PivExact.matOf (QMCLeafB.RoundProgram.stN s)
        (QMCLeafB.RoundProgram.stX s) j i :=
    hN.symm ▸ hsym
  have hev : QMCLeafB.LdltCertM5.EvRun (QMCLeafB.RoundProgram.stMu s)
      (QMCLeafB.RoundProgram.stD s) 0 (QMCLeafB.RoundProgram.stN s)
      ((QMCLeafB.RoundProgram.stMu s, QMCLeafB.RoundProgram.stD s),
        (QMCLeafB.RoundProgram.toRows (QMCLeafB.RoundProgram.stN s,
            QMCLeafB.RoundProgram.stX s),
          ([] : QMCLeafB.PivotProgram.Acc))) :=
    QMCLeafB.LdltCertM5.evRun_of_evRunB (le_refl (0 : ℚ)) _ _ hevB
  have hpsd : ∀ x : Fin G.n → ℚ,
      0 ≤ QMCLeafB.SepOracle.qf
        (QMCLeafB.StateDiag.stMat G.n (QMCLeafB.RoundProgram.stX s)) x :=
    hN ▸ QMCLeafB.LdltCertM5.psd_of_exactRun s hlen' hsym' hev hpiv
  have hdiag : ∀ i : Fin G.n,
      |QMCLeafB.StateDiag.stMat G.n (QMCLeafB.RoundProgram.stX s) i i - 1| ≤ dq / 4 := by
    intro i
    have h1 : |QMCLeafB.StateDiag.stMat G.n (QMCLeafB.RoundProgram.stX s) i i - 1|
        ≤ QMCLeafB.RoundProgram.dvR s := abs_stMat_diag_le_dvR hN hlenX i
    have h2 : QMCLeafB.RoundProgram.dvR s ≤ dq / 4 := by
      rw [← hdqv]
      exact hdv
    linarith
  have htrace : QMCLeafB.SepOracle.frob (QMCLeafB.Finalization.wMatrixQ G)
      (QMCLeafB.StateDiag.stMat G.n (QMCLeafB.RoundProgram.stX s))
      ≤ (t - QMCLeafB.RundataCert.eps G) + dq / 2 := by
    have h := hfv
    rw [QMCLeafB.OkLower.levelOf, hlev, hdqv] at h
    rwa [← hA, ← QMCLeafB.StateDiag.fvR_eq_frob hN hlenA hlenX]
  exact ⟨QMCLeafB.CentreAdm.diagPinch
      (QMCLeafB.StateDiag.stMat G.n (QMCLeafB.RoundProgram.stX s)) dq,
    diagPinch_symm hsym,
    relaxMem_diagPinch_of_gate (A := QMCLeafB.Finalization.wMatrixQ G)
      (fun i => QMCLeafB.Finalization.wMatrixQ_apply_of_eq) hdq hdq4 hpsd hdiag htrace⟩

#print axioms HokUpper34M8.relaxMem_of_okRel

/-- **`hok`'s conclusion at the concrete released test.**  Same stream bookkeeping as §4, with the
`ok` test now the *compiled* `okRel` (certified run + released diagonal gate + exact pivot + lower
level) instead of abstract gate data. -/
theorem exists_relaxMem_of_okRelStream {G : QuantumMaxCutEnergy.Input} {t : ℚ} {T : ℕ}
    {σ : ℕ → QMCLeafB.RoundProgram.RSt} {o : QuantumMaxCutEnergy.Input → ℚ → Bool}
    (hbit : o G t = QMCLeafB.SimLoop.anyOk (fun k => okRel (σ k)) T)
    (hbt : o G t = true)
    (hdat : ∀ k, k < T → okRel (σ k) = true →
      QMCLeafB.RoundProgram.stN (σ k) = G.n ∧
      G.n ≤ (QMCLeafB.RoundProgram.stA (σ k)).length ∧
      G.n ≤ (QMCLeafB.RoundProgram.stX (σ k)).length ∧
      QMCLeafB.StateDiag.stMat G.n (QMCLeafB.RoundProgram.stA (σ k))
        = QMCLeafB.Finalization.wMatrixQ G ∧
      (∀ i j, QMCLeafB.StateDiag.stMat G.n (QMCLeafB.RoundProgram.stX (σ k)) i j
        = QMCLeafB.StateDiag.stMat G.n (QMCLeafB.RoundProgram.stX (σ k)) j i))
    (hlev : ∀ k, k < T → okRel (σ k) = true →
      QMCLeafB.RoundProgram.stT (σ k) - QMCLeafB.RoundT.epsOf (σ k)
        = t - QMCLeafB.RundataCert.eps G)
    (hdqv : ∀ k, k < T → okRel (σ k) = true →
      QMCLeafB.OkLower.dqOf (σ k) = QMCLeafB.RundataParams.dqShallow G)
    (hRq : 0 < QMCLeafB.EngineRuntime.Rq G) :
    HokShape G t := by
  have hany : QMCLeafB.SimLoop.anyOk (fun k => okRel (σ k)) T = true := by
    rw [← hbit]
    exact hbt
  obtain ⟨k, hk, hok⟩ := (QMCLeafB.SimLoop.anyOk_eq_true_iff (fun k => okRel (σ k)) T).mp hany
  obtain ⟨hN, hlenA, hlenX, hA, hsym⟩ := hdat k hk hok
  exact relaxMem_of_okRel hN hlenA hlenX hA hsym hok (hlev k hk hok) (hdqv k hk hok)
    (QMCLeafB.RundataParams.dqShallow_pos G) (QMCLeafB.CentreAdm.dqShallow_le_four G hRq)

#print axioms HokUpper34M8.exists_relaxMem_of_okRelStream

end HokUpper34M8


