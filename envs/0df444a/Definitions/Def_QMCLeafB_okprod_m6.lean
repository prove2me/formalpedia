-- Prove2me | Definitions.Def_QMCLeafB_okprod_m6
-- name    : QMCLeafB_okprod_m6
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-04T06:09:57.195553+00:00
-- url     : https://prove2.me/theorems/47afdb70-b8ed-4d39-8d24-0ea4cfd2cb3c
-- title:
--   QMCLeafB okprod_m6
-- statement:
--   # leaf B phase 21 — direction `ok-production` (swarm `smw1m5nkm`, member m6, direction d4)
--
--   Published as part of the QMCLeafB library mirror supporting the quantum max-cut campaign's polynomial-time SDP-value certificate (AGM20, TQC 2020, arXiv 2003.14394).

import Mathlib
import Definitions.Def_QMCLeafB_records_m2
/-
# leaf B phase 21 — direction `ok-production` (swarm `smw1m5nkm`, member m6, direction d4)

The phase-20 residual is `QMCLeafB.RecordsM2.CoreDataF` (and `ResidFinite`): at *every* interior
`(G, t)` a coded state stream, its symmetry, the finite-cut clause `hcutfin`, the two drift budgets at
the canonical stream and the verdict read-out.  This file settles **which of those slots carry
content**, by proving the two halves of a characterisation at a fixed interior point.

* §1 **necessity** — `CoreDataF` forces the *pinched* relaxed body to be inhabited somewhere:
  `exists_mem_of_coreDataF`.  The proof is `hcutfin` read at `k = K·m`: the canonical flag at the
  horizon round cannot be `false`, so its centre is a member.  No arithmetic, no symmetry, no
  budgets.  Corollaries: `not_coreDataF_of_emptyBody` and, uniformly, `not_residFinite_of_emptyBody`
  — `ResidFinite` is refuted by any single interior point whose pinched body is empty.  (Supplying
  that point is the falsification direction's job; this is the shape-level reduction.)
* §2 **sufficiency at an all-`ok` point** — `coreDataF_of_allOk`: a *single* coded state which is
  symmetric, unit-diagonal, exactly PSD and inside the programme's `dq/2` band at the round's level
  already gives `CoreDataF`, with **both drift slots vacuous**: the constant stream has every flag
  `true`, so there is no cut round to budget for.  No stream bookkeeping, no horizon, no
  multipliers.
* §3 **what that means for the residual** — `coreDataF_of_okRound` composes §2 with
  `flag_cXst_of_ok`: the *programme's own `ok` round* supplies the coded state, so on the branch
  where the verdict bit is `true` the residual is discharged from the ok test's certificate alone.
  The two drift budgets — the phase-20 "named residual (a)" — are needed **only** where the verdict
  bit is `false` (`drifts_needed_only_below_verdict`).
* §4 **anchors** — `coreDataF_G₀_interval`: `CoreDataF` at `G₀` is inhabited for **every** `t` whose
  level passes the objective band, i.e. on an interval of interior thresholds, not only at the
  banked `t = −1/2`; the two explicit interior points `−1/2` and `−1/1000` are recorded.
* §5 **the verdict leg** — `loopBit_Tbc2_eq_anyOk` + `verdict_true_of_okRound`: one round the
  programme's test accepts already forces the leaf's own bit.  With the `hon` bridge this closes the
  `ok` branch with no stream data at all.
* §6 **where the budgets *are* read** — `flags_false_below_of_verdict_false`: a `false` verdict bit
  makes every round below the horizon a cut round.
* §7 **⚠ a defect in the canonicalisation** — `RelaxCut.separates` is one-sided, so the trivial
  record works at *every* centre (`relaxCut_trivial`, `relaxMem_or_cut_vacuous`,
  `defaultCut_satisfies_cutOf_spec`): `FlagsM5.cutOf`'s cut branch is `Classical.choice` over an
  always-inhabited `Nonempty`, so `nrmOf`/`margOf` have **no** usable properties and the two drift
  slots are not provable at `cutOf`.  `nrmOf_of_mem`/`margOf_of_mem` record the one case that is
  determined.
* §8 **which rounds are cut rounds** — `flag_cXst_false_iff` (at a pinched centre `diag_near` is
  free, so a cut round is exactly PSD-violation or objective-excess) and `trace_test_cXst`.
* §9 **the fix, compiled** — `cutOfC`: the same member test, the cut side taken from the *choice-free*
  `RelaxOracle.relaxOracle`.  Same `cutOf_spec` clauses (`cutOfC_spec`), same member-side record
  (`cutOfC_of_mem`), and explicit normals (`cutOfC_trace`: `normal = -A`, `margin` = the excess).
* §10 **the fix, symmetry-free** — `cutOfC₀` has `FlagsM5.cutOf`'s own argument list plus `hδ`: the
  psd branch symmetrises internally (`qf_transpose_avg`: `qf` is blind to transposition), so
  `RecordsM2.nrmOf`/`margOf` can be redefined by threading `P.hdq` and **nothing else** in the cone
  changes type.  Same spec (`cutOfC₀_spec`), same member side (`cutOfC₀_of_mem`), same explicit trace
  branch (`cutOfC₀_trace`).

No `sorry`, no `admit`, no `axiom`, no `native_decide`, no `unsafe`; `set_option autoImplicit false`;
`#print axioms` audits at the end.
-/

open scoped BigOperators
open Matrix
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option linter.unusedVariables false

noncomputable section

namespace QMCLeafB.OkProdM6

attribute [local instance] Classical.propDecidable
open QuantumMaxCutEnergy
open QMCLeafB.SepOracle (qf frob)
open QMCLeafB.FlagsM5 (flagOf)
open QMCLeafB.RecordsM2 (CoreDataF ResidFinite cXst)

/-! ## 1.  Necessity: the residual forces the pinched body to be inhabited

`hcutfin` says: every round whose canonical flag is `false` lies below the horizon `K·m`.  Read at
`k = K·m` it says the flag at the horizon round is `true` — i.e. the pinched centre of that round is
a member of the relaxation.  Since the centre family is built from the supplied code, the *body* is
nonempty.  This is the only thing the horizon clause contributes, and it is a statement about `(G,t)`
alone — no hypothesis mentions `X`. -/

/-- **The horizon round's flag is `ok`.** -/
theorem flag_horizon_of_coreDataF {o : QuantumMaxCutEnergy.Input → ℚ → Bool}
    {G : QuantumMaxCutEnergy.Input} {t : ℚ} {P : QMCLeafB.FinalStroke.RunParams G}
    {hn : 2 ≤ G.n} (D : CoreDataF o G t P hn) :
    flagOf G t P (cXst G.n D.X P.dq) (P.K * P.m) = true := by
  by_contra hne
  have hf : flagOf G t P (cXst G.n D.X P.dq) (P.K * P.m) = false := by
    cases hv : flagOf G t P (cXst G.n D.X P.dq) (P.K * P.m) <;> simp_all
  exact absurd (D.hcutfin (P.K * P.m) hf) (lt_irrefl _)

#print axioms QMCLeafB.OkProdM6.flag_horizon_of_coreDataF

/-- **`CoreDataF` forces a member of the pinched relaxed body** at the round's own threshold
`t − ε`.  Nothing else in the record can produce one. -/
theorem exists_mem_of_coreDataF {o : QuantumMaxCutEnergy.Input → ℚ → Bool}
    {G : QuantumMaxCutEnergy.Input} {t : ℚ} {P : QMCLeafB.FinalStroke.RunParams G}
    {hn : 2 ≤ G.n} (D : CoreDataF o G t P hn) :
    ∃ Q : Matrix (Fin G.n) (Fin G.n) ℚ,
      QMCLeafB.RelaxOracle.RelaxMem (QMCLeafB.Finalization.wMatrixQ G) Q
        (t - QMCLeafB.RundataCert.eps G) P.dq := by
  by_contra h
  have hbody : ∀ Q : Matrix (Fin G.n) (Fin G.n) ℚ,
      ¬ QMCLeafB.RelaxOracle.RelaxMem (QMCLeafB.Finalization.wMatrixQ G) Q
        (t - QMCLeafB.RundataCert.eps G) P.dq := by
    intro Q hQ
    exact h ⟨Q, hQ⟩
  have hf := QMCLeafB.FlagsM5.flagOf_false_of_not_mem G t P (cXst G.n D.X P.dq)
    (P.K * P.m) (hbody _)
  exact absurd (D.hcutfin (P.K * P.m) hf) (lt_irrefl _)

#print axioms QMCLeafB.OkProdM6.exists_mem_of_coreDataF

/-- **An empty pinched body kills the record** — the horizon clause has no inhabitant. -/
theorem not_coreDataF_of_emptyBody {o : QuantumMaxCutEnergy.Input → ℚ → Bool}
    {G : QuantumMaxCutEnergy.Input} {t : ℚ} {P : QMCLeafB.FinalStroke.RunParams G}
    {hn : 2 ≤ G.n}
    (h : ∀ Q : Matrix (Fin G.n) (Fin G.n) ℚ,
      ¬ QMCLeafB.RelaxOracle.RelaxMem (QMCLeafB.Finalization.wMatrixQ G) Q
        (t - QMCLeafB.RundataCert.eps G) P.dq) :
    CoreDataF o G t P hn → False := by
  intro D
  obtain ⟨Q, hQ⟩ := exists_mem_of_coreDataF D
  exact h Q hQ

#print axioms QMCLeafB.OkProdM6.not_coreDataF_of_emptyBody

/-- **The same, uniformly in the bracket.**  `ResidFinite` forces the pinched body to be inhabited at
*every* interior `(G, t)`: one interior point with an empty body refutes the whole residual, whatever
the programme bit is. -/
theorem exists_mem_of_residFinite {o : QuantumMaxCutEnergy.Input → ℚ → Bool}
    {Pfam : (G : QuantumMaxCutEnergy.Input) → QMCLeafB.FinalStroke.RunParams G}
    (H : ResidFinite o Pfam) {G : QuantumMaxCutEnergy.Input} {t : ℚ} {hn : 2 ≤ G.n}
    (hlo : -QMCLeafB.EngineRuntime.Rq G ≤ t)
    (hhi : (t : ℝ) < -(((QMCLeafB.EngineRuntime.Rq G / 40000 : ℚ)) : ℝ)) :
    ∃ Q : Matrix (Fin G.n) (Fin G.n) ℚ,
      QMCLeafB.RelaxOracle.RelaxMem (QMCLeafB.Finalization.wMatrixQ G) Q
        (t - QMCLeafB.RundataCert.eps G) (Pfam G).dq :=
  exists_mem_of_coreDataF (H G t hn hlo hhi)

#print axioms QMCLeafB.OkProdM6.exists_mem_of_residFinite

/-- **`ResidFinite` is refuted by one interior empty-body point.** -/
theorem not_residFinite_of_emptyBody {o : QuantumMaxCutEnergy.Input → ℚ → Bool}
    {Pfam : (G : QuantumMaxCutEnergy.Input) → QMCLeafB.FinalStroke.RunParams G}
    {G : QuantumMaxCutEnergy.Input} {t : ℚ} {hn : 2 ≤ G.n}
    (hlo : -QMCLeafB.EngineRuntime.Rq G ≤ t)
    (hhi : (t : ℝ) < -(((QMCLeafB.EngineRuntime.Rq G / 40000 : ℚ)) : ℝ))
    (h : ∀ Q : Matrix (Fin G.n) (Fin G.n) ℚ,
      ¬ QMCLeafB.RelaxOracle.RelaxMem (QMCLeafB.Finalization.wMatrixQ G) Q
        (t - QMCLeafB.RundataCert.eps G) (Pfam G).dq) :
    ResidFinite o Pfam → False :=
  fun H => not_coreDataF_of_emptyBody h (H G t hn hlo hhi)

#print axioms QMCLeafB.OkProdM6.not_residFinite_of_emptyBody

/-! ## 2.  Sufficiency at an all-`ok` point: the drift slots are vacuous

The stream `X` is *data*, so at a point where one admissible centre is available the supplier takes
it at **every** round.  Then `flagOf` is `true` everywhere, `anyOk` reads `true`, both drift slots
have no round to speak about, and the whole record collapses to a single geometric obligation —
a coded state satisfying the `ok` test's three clauses. -/

/-- `anyOk` of the all-`ok` stream, at a positive count. -/
theorem anyOk_const_true : ∀ N : ℕ, 0 < N →
    QMCLeafB.SimLoop.anyOk (fun _ : ℕ => true) N = true
  | 0, h => absurd h (lt_irrefl 0)
  | (k + 1), _ => QMCLeafB.InhabitM5.anyOk_true_succ k

#print axioms QMCLeafB.OkProdM6.anyOk_const_true

/-- **`CoreDataF` from one admissible coded state.**  The hypotheses are exactly the `ok` test's,
plus the base's symmetry and a positive horizon; the two drift slots are discharged by the constant
stream having no cut round. -/
theorem coreDataF_of_allOk {o : QuantumMaxCutEnergy.Input → ℚ → Bool}
    {G : QuantumMaxCutEnergy.Input} {t : ℚ} {P : QMCLeafB.FinalStroke.RunParams G}
    {hn : 2 ≤ G.n} (X₀ : List ℚ) (hKm : 0 < P.K * P.m)
    (hdq : 0 < P.dq) (hdq4 : P.dq ≤ 4)
    (hsym₀ : (QMCLeafB.StateDiag.stMat G.n X₀)ᵀ = QMCLeafB.StateDiag.stMat G.n X₀)
    (hunit : ∀ i, QMCLeafB.StateDiag.stMat G.n X₀ i i = 1)
    (hpsd : ∀ x : Fin G.n → ℚ,
      0 ≤ qf (QMCLeafB.StateDiag.stMat G.n X₀) x)
    (htrace : frob (QMCLeafB.Finalization.wMatrixQ G) (QMCLeafB.StateDiag.stMat G.n X₀)
      ≤ (t - QMCLeafB.RundataCert.eps G) + P.dq / 2)
    (hverdict : o G t = true) :
    Nonempty (CoreDataF o G t P hn) := by
  have hflags : ∀ k, flagOf G t P (cXst G.n (fun _ => X₀) P.dq) k = true := fun k =>
    QMCLeafB.RecordsM2.flag_cXst_of_ok k hdq hdq4 hunit hpsd htrace
  have hfalse : ∀ k, flagOf G t P (cXst G.n (fun _ => X₀) P.dq) k = false → False := by
    intro k hk
    rw [hflags k] at hk
    exact absurd hk (by simp)
  refine ⟨{ X := fun _ => X₀
            hsym := fun _ => hsym₀
            hcutfin := fun k hk => (hfalse k hk).elim
            hdriftc := fun k _ hk => (hfalse k hk).elim
            hdriftd := fun k _ hk => (hfalse k hk).elim
            hverdict := ?_ }⟩
  rw [hverdict]
  have hstream : (flagOf G t P (cXst G.n (fun _ => X₀) P.dq)) = (fun _ : ℕ => true) :=
    funext hflags
  rw [hstream]
  exact (anyOk_const_true _ hKm).symm

#print axioms QMCLeafB.OkProdM6.coreDataF_of_allOk

/-! ## 3.  What that means for the residual: the `ok` branch is discharged by the ok test

`flag_cXst_of_ok` is the *programme's own* `ok` certificate: a round the test accepts gives a member
at the pinched centre.  Composed with §2, a run that reports `ok` within the horizon supplies its own
`CoreDataF`, with no budget and no multiplier anywhere.  Conversely (`coreDataF_drifts_vacuous_of_ok`)
the two drift slots are never *read*: they are needed only at points where the verdict bit is
`false`. -/

/-- **`CoreDataF` at a point where the programme says `ok`**, from the `ok` round's own state: a
coded state satisfying the test's three clauses is the only input. -/
theorem coreDataF_of_okRound {o : QuantumMaxCutEnergy.Input → ℚ → Bool}
    {G : QuantumMaxCutEnergy.Input} {t : ℚ} {P : QMCLeafB.FinalStroke.RunParams G}
    {hn : 2 ≤ G.n} (X : ℕ → List ℚ) (k₀ : ℕ)
    (hKm : 0 < P.K * P.m)
    (hdq : 0 < P.dq) (hdq4 : P.dq ≤ 4)
    (hsym₀ : (QMCLeafB.StateDiag.stMat G.n (X k₀))ᵀ
      = QMCLeafB.StateDiag.stMat G.n (X k₀))
    (hunit : ∀ i, QMCLeafB.StateDiag.stMat G.n (X k₀) i i = 1)
    (hpsd : ∀ x : Fin G.n → ℚ,
      0 ≤ qf (QMCLeafB.StateDiag.stMat G.n (X k₀)) x)
    (htrace : frob (QMCLeafB.Finalization.wMatrixQ G) (QMCLeafB.StateDiag.stMat G.n (X k₀))
      ≤ (t - QMCLeafB.RundataCert.eps G) + P.dq / 2)
    (hverdict : o G t = true) :
    Nonempty (CoreDataF o G t P hn) :=
  coreDataF_of_allOk (X k₀) hKm hdq hdq4 hsym₀ hunit hpsd htrace hverdict

#print axioms QMCLeafB.OkProdM6.coreDataF_of_okRound

/-- **The drift budgets are read only below a `false` verdict bit.**  If `o G t = true` then the
residual at `(G, t)` is discharged by *any* one admissible coded state — the two budget slots of
phase 20's "named residual (a)" carry no content on that branch.  (Restated as an implication so the
statement is a theorem about the record, not a proof-engineering remark: the `hdriftc`/`hdriftd`
fields are never used in `coreDataF_of_allOk`'s construction.) -/
theorem coreDataF_drifts_vacuous_of_ok {o : QuantumMaxCutEnergy.Input → ℚ → Bool}
    {G : QuantumMaxCutEnergy.Input} {t : ℚ} {P : QMCLeafB.FinalStroke.RunParams G}
    {hn : 2 ≤ G.n} (hverdict : o G t = true)
    (h : ∃ X₀ : List ℚ,
      (QMCLeafB.StateDiag.stMat G.n X₀)ᵀ = QMCLeafB.StateDiag.stMat G.n X₀ ∧
      (∀ i, QMCLeafB.StateDiag.stMat G.n X₀ i i = 1) ∧
      (∀ x : Fin G.n → ℚ, 0 ≤ qf (QMCLeafB.StateDiag.stMat G.n X₀) x) ∧
      frob (QMCLeafB.Finalization.wMatrixQ G) (QMCLeafB.StateDiag.stMat G.n X₀)
        ≤ (t - QMCLeafB.RundataCert.eps G) + P.dq / 2)
    (hKm : 0 < P.K * P.m) (hdq : 0 < P.dq) (hdq4 : P.dq ≤ 4) :
    Nonempty (CoreDataF o G t P hn) := by
  obtain ⟨X₀, hs, hu, hp, ht⟩ := h
  exact coreDataF_of_allOk X₀ hKm hdq hdq4 hs hu hp ht hverdict

#print axioms QMCLeafB.OkProdM6.coreDataF_drifts_vacuous_of_ok

/-! ## 4.  Anchors: `CoreDataF` at `G₀` is inhabited on an interval of interior thresholds

The banked anchor sits at the single point `t = −1/2`.  §2 makes the whole band explicit: the
constant `Q₀` stream is admissible as soon as the level `t − ε + dq/2` reaches the objective
`−3/4`, so every `t` in `[−3/4 + ε − dq/2, …)` works.  Two interior points are recorded, `−1/2` and
`−1/1000`; in particular the residual is not a single-point phenomenon. -/

/-- **`CoreDataF` at `G₀` for every threshold whose level clears the objective band.** -/
theorem coreDataF_G₀_interval {t : ℚ}
    (hfr : -(3 / 4) ≤ t - QMCLeafB.RundataCert.eps QMCLeafB.ResidRefute.G₀
      + (QMCLeafB.UnionShallow.paramsKbc2 QMCLeafB.ResidRefute.G₀).dq / 2) :
    Nonempty (CoreDataF (fun _ _ => true) QMCLeafB.ResidRefute.G₀ t
      (QMCLeafB.UnionShallow.paramsKbc2 QMCLeafB.ResidRefute.G₀)
      QMCLeafB.ResidKill.hnG₀) := by
  have hdq := QMCLeafB.RecordM2.dq_pos_paramsKbc2 QMCLeafB.ResidRefute.G₀
  have hdq4 : (QMCLeafB.UnionShallow.paramsKbc2 QMCLeafB.ResidRefute.G₀).dq ≤ 4 :=
    le_of_lt (QMCLeafB.RecordM2.dq_lt_four_paramsKbc2 QMCLeafB.ResidRefute.G₀)
  have hKm : 0 < (QMCLeafB.UnionShallow.paramsKbc2 QMCLeafB.ResidRefute.G₀).K
      * (QMCLeafB.UnionShallow.paramsKbc2 QMCLeafB.ResidRefute.G₀).m :=
    lt_of_lt_of_le Nat.zero_lt_one
      (QMCLeafB.UnionShallow.one_le_Kbc2_mul QMCLeafB.ResidRefute.G₀)
  refine coreDataF_of_allOk (o := fun _ _ => true) QMCLeafB.RecordsM2.Q₀code hKm hdq hdq4 ?_ ?_ ?_ ?_
    rfl
  · rw [QMCLeafB.RecordsM2.stMat_Q₀code]
    exact QMCLeafB.FlagsM5.Q₀_transpose
  · intro i
    rw [QMCLeafB.RecordsM2.stMat_Q₀code]
    exact QMCLeafB.FlagsM5.Q₀_diag i
  · intro x
    rw [QMCLeafB.RecordsM2.stMat_Q₀code]
    exact QMCLeafB.FlagsM5.Q₀_qf x
  · rw [QMCLeafB.RecordsM2.stMat_Q₀code, QMCLeafB.FlagsM5.frob_Q₀]
    exact hfr

#print axioms QMCLeafB.OkProdM6.coreDataF_G₀_interval

/-- **The banked anchor** `t = −1/2`, re-derived through §2. -/
theorem coreDataF_G₀_at_neg_half :
    Nonempty (CoreDataF (fun _ _ => true) QMCLeafB.ResidRefute.G₀ (-(1 / 2))
      (QMCLeafB.UnionShallow.paramsKbc2 QMCLeafB.ResidRefute.G₀)
      QMCLeafB.ResidKill.hnG₀) := by
  refine coreDataF_G₀_interval ?_
  rw [QMCLeafB.FlagsM5.eps_G₀]
  have hdq := QMCLeafB.RecordM2.dq_pos_paramsKbc2 QMCLeafB.ResidRefute.G₀
  linarith

#print axioms QMCLeafB.OkProdM6.coreDataF_G₀_at_neg_half

/-- **A second interior anchor**, `t = −1/1000` (inside `−1 ≤ t < −1/40000`). -/
theorem coreDataF_G₀_at_neg_thousandth :
    Nonempty (CoreDataF (fun _ _ => true) QMCLeafB.ResidRefute.G₀ (-(1 / 1000))
      (QMCLeafB.UnionShallow.paramsKbc2 QMCLeafB.ResidRefute.G₀)
      QMCLeafB.ResidKill.hnG₀) := by
  refine coreDataF_G₀_interval ?_
  rw [QMCLeafB.FlagsM5.eps_G₀]
  have hdq := QMCLeafB.RecordM2.dq_pos_paramsKbc2 QMCLeafB.ResidRefute.G₀
  linarith

#print axioms QMCLeafB.OkProdM6.coreDataF_G₀_at_neg_thousandth

/-- `t = −1/1000` is inside the interior bracket at `G₀`: the second anchor is an *interior* point. -/
theorem neg_thousandth_mem_bracket :
    -(QMCLeafB.EngineRuntime.Rq QMCLeafB.ResidRefute.G₀) ≤ -(1 / 1000) ∧
      ((-(1 / 1000) : ℚ) : ℝ) <
        -(((QMCLeafB.EngineRuntime.Rq QMCLeafB.ResidRefute.G₀ / 40000 : ℚ)) : ℝ) := by
  rw [QMCLeafB.ResidRefute.Rq_G₀]
  constructor <;> norm_num

#print axioms QMCLeafB.OkProdM6.neg_thousandth_mem_bracket

/-! ## 5.  The verdict leg at the actual campaign loop

§3 leaves the verdict bit `o G t = true` as an input.  At the leaf's actual `o` — `loopBit init0 round
verdict Tbc2` — that bit is *not* an extra obligation: the loop's own ledger
(`RStInit.loopBit_eq_anyOk`) says it is `anyOk` of the round-by-round `ok` bits, so **one** round the
programme's test accepts already makes the verdict `true`.  Together with d2's `hon` (programme `ok` ⇒
member at the pinched centre) this closes the `ok` branch of the residual outright. -/

/-- **The campaign loop's bit is `anyOk` of the programme's own `ok` bits**, at the campaign count. -/
theorem loopBit_Tbc2_eq_anyOk (G : QuantumMaxCutEnergy.Input) (t : ℚ) :
    QMCLeafB.FinalStroke.loopBit QMCLeafB.InitDq.init0 QMCLeafB.RoundProgram.round
        QMCLeafB.RoundProgram.verdict QMCLeafB.ClosingAssembly.Tbc2 G t
      = QMCLeafB.SimLoop.anyOk
          (fun k => !((QMCLeafB.RoundProgram.oracleR (QMCLeafB.RoundProgram.round^[k]
            (QMCLeafB.InitDq.init0 (QMCLeafB.FinalStroke.noTape G t)))).1))
          ((QMCLeafB.UnionShallow.paramsKbc2 G).K
            * (QMCLeafB.UnionShallow.paramsKbc2 G).m) :=
  QMCLeafB.RStInit.verdict_iterate_eq_anyOk
    (QMCLeafB.InitDq.init0 (QMCLeafB.FinalStroke.noTape G t)) (by rfl)
    ((QMCLeafB.UnionShallow.paramsKbc2 G).K
      * (QMCLeafB.UnionShallow.paramsKbc2 G).m)

#print axioms QMCLeafB.OkProdM6.loopBit_Tbc2_eq_anyOk

/-- **One accepted round makes the verdict `true`.**  The `ok` bit of the programme's round `k` is
`!oracleR.fst`; a round below the campaign count where the test accepts therefore forces the leaf's
own bit. -/
theorem verdict_true_of_okRound (G : QuantumMaxCutEnergy.Input) (t : ℚ) (k₀ : ℕ)
    (hk₀ : k₀ < (QMCLeafB.UnionShallow.paramsKbc2 G).K
      * (QMCLeafB.UnionShallow.paramsKbc2 G).m)
    (hok : (QMCLeafB.RoundProgram.oracleR (QMCLeafB.RoundProgram.round^[k₀]
      (QMCLeafB.InitDq.init0 (QMCLeafB.FinalStroke.noTape G t)))).1 = false) :
    QMCLeafB.FinalStroke.loopBit QMCLeafB.InitDq.init0 QMCLeafB.RoundProgram.round
      QMCLeafB.RoundProgram.verdict QMCLeafB.ClosingAssembly.Tbc2 G t = true := by
  rw [loopBit_Tbc2_eq_anyOk, QMCLeafB.SimLoop.anyOk_eq_true_iff]
  exact ⟨k₀, hk₀, by simp [hok]⟩

#print axioms QMCLeafB.OkProdM6.verdict_true_of_okRound

/-! ## 6.  Where the drift budgets *are* read: below a `false` verdict bit

§3 shows the budgets carry no content at an `ok` point.  The complement pins phase 20's "named
residual (a)" exactly: at a point where the bit is `false`, `hverdict` forces the canonical flag to be
`false` at **every** round below the horizon, so every round below the horizon is a cut round and the
two drift slots are read on all of them.  `exists_mem_of_coreDataF` (§1) then sits alongside: the
record still needs a member — at the *horizon* round only. -/

/-- **A `false` verdict bit makes every round below the horizon a cut round.** -/
theorem flags_false_below_of_verdict_false {o : QuantumMaxCutEnergy.Input → ℚ → Bool}
    {G : QuantumMaxCutEnergy.Input} {t : ℚ} {P : QMCLeafB.FinalStroke.RunParams G}
    {hn : 2 ≤ G.n} (D : CoreDataF o G t P hn) (ho : o G t = false) :
    ∀ k, k < P.K * P.m → flagOf G t P (cXst G.n D.X P.dq) k = false := by
  have hany : QMCLeafB.SimLoop.anyOk (flagOf G t P (cXst G.n D.X P.dq)) (P.K * P.m) = false :=
    D.hverdict ▸ ho
  exact (QMCLeafB.SimLoop.anyOk_eq_false_iff _ _).1 hany

#print axioms QMCLeafB.OkProdM6.flags_false_below_of_verdict_false

/-- **The residual splits on the verdict bit.**  At a `false`-bit point the two drift slots are read
at *every* round below the horizon and the horizon round must still be a member; at a `true`-bit
point they are read nowhere (§3).  Both statements are about the record; together they say the
phase-21 residual's analytic content sits entirely at `false`-bit points. -/
theorem cut_rounds_exactly_below_horizon {o : QuantumMaxCutEnergy.Input → ℚ → Bool}
    {G : QuantumMaxCutEnergy.Input} {t : ℚ} {P : QMCLeafB.FinalStroke.RunParams G}
    {hn : 2 ≤ G.n} (D : CoreDataF o G t P hn) (ho : o G t = false) :
    (∀ k, k < P.K * P.m → flagOf G t P (cXst G.n D.X P.dq) k = false) ∧
      flagOf G t P (cXst G.n D.X P.dq) (P.K * P.m) = true :=
  ⟨flags_false_below_of_verdict_false D ho, flag_horizon_of_coreDataF D⟩

/-! ## 7.  ⚠ The canonical cut record carries **no** separation content

`FlagsM5.cutOf` decides the cut side by `Classical.choice` of `RelaxOracle.relaxMem_or_cut`'s second
disjunct, and phase 19 read that as "the stream is canonical, not an obligation".  The structure does
not support that reading: `RelaxCut.separates` is a **one-sided** inequality, so the trivial record
`normal = 0, margin = 1` satisfies it at *every* centre — indeed `FlagsM5.defaultCut` proves exactly
that.  Hence

* `relaxCut_trivial` — every centre admits a cut record, so the cut disjunct of the dichotomy is
  unconditional; `relaxMem_or_cut` is not a dichotomy and `relaxMem_or_cut_vacuous` records that;
* `defaultCut_satisfies_cutOf_spec` — the entire content of `cutOf_spec` is met by the trivial
  record, so **nothing** in the library bounds `nrmOf` or `margOf` at a cut round;
* at a *member* round `cutOf` **is** the trivial record, so `nrmOf k = 0` and `margOf k = 1`
  (`nrmOf_of_mem`, `margOf_of_mem`).

Consequence for the phase-21 residual: the two drift slots of `CoreDataF` are statements about
`Classical.choice`'s witness.  A cut record's only hypothesis is `separates`, and at a refuted
(empty-body) point the body is empty, so `separates` is vacuous there — exactly where the bounded
restate reads the budgets.  The budgets cannot be analysed at `cutOf`; the cut records must be
*supplied* (the phase-18 `RunParts` shape) or derived from the choice-free constructive oracle
`RelaxOracle.relaxOracle`, whose branch normals are explicit (`v vᵀ`, `sign·e_i e_iᵀ`, `−A`). -/

/-- **Every centre admits a cut record** — the trivial one.  So `Nonempty (RelaxCut A cX u δ)` is a
theorem at every `(A, cX, u, δ)`, with no side condition. -/
theorem relaxCut_trivial {n : ℕ} (A cX : Matrix (Fin n) (Fin n) ℚ) (u δ : ℚ) :
    Nonempty (QMCLeafB.RelaxOracle.RelaxCut A cX u δ) :=
  ⟨QMCLeafB.FlagsM5.defaultCut A cX u δ⟩

#print axioms QMCLeafB.OkProdM6.relaxCut_trivial

/-- **The dichotomy's cut disjunct is unconditional.** -/
theorem relaxMem_or_cut_vacuous {n : ℕ} (A cX : Matrix (Fin n) (Fin n) ℚ) (u δ : ℚ) :
    QMCLeafB.RelaxOracle.RelaxMem A cX u δ
      ∨ Nonempty (QMCLeafB.RelaxOracle.RelaxCut A cX u δ) :=
  Or.inr (relaxCut_trivial A cX u δ)

#print axioms QMCLeafB.OkProdM6.relaxMem_or_cut_vacuous

/-- The trivial record's normal is `0` and its margin is `1`. -/
theorem defaultCut_spec {n : ℕ} (A cX : Matrix (Fin n) (Fin n) ℚ) (u δ : ℚ) :
    (QMCLeafB.FlagsM5.defaultCut A cX u δ).normal = 0
      ∧ (QMCLeafB.FlagsM5.defaultCut A cX u δ).margin = 1 :=
  ⟨rfl, rfl⟩

#print axioms QMCLeafB.OkProdM6.defaultCut_spec

/-- **`cutOf_spec` does not pin `cutOf` down**: the trivial record satisfies both of its clauses at
every centre.  So no proof may read more out of `nrmOf`/`margOf` than `0 < margin` and (vacuous, at an
empty body) `separates`. -/
theorem defaultCut_satisfies_cutOf_spec {n : ℕ} (A cX : Matrix (Fin n) (Fin n) ℚ) (u δ : ℚ) :
    0 < (QMCLeafB.FlagsM5.defaultCut A cX u δ).margin ∧
      ∀ X : Matrix (Fin n) (Fin n) ℝ,
        QMCLeafB.BallFloor.relaxBodyLE (QMCLeafB.SepOracle.castMat A) ((u : ℚ) : ℝ)
            ((δ : ℚ) : ℝ) X →
          -((((QMCLeafB.FlagsM5.defaultCut A cX u δ).margin : ℚ)) : ℝ) ≤
            frob (QMCLeafB.SepOracle.castMat (QMCLeafB.FlagsM5.defaultCut A cX u δ).normal)
              (X - QMCLeafB.SepOracle.castMat cX) :=
  ⟨(QMCLeafB.FlagsM5.defaultCut A cX u δ).margin_pos,
    fun X hX => (QMCLeafB.FlagsM5.defaultCut A cX u δ).separates X hX⟩

#print axioms QMCLeafB.OkProdM6.defaultCut_satisfies_cutOf_spec

/-- **At a member round the canonical margin is `1`.** -/
theorem margOf_of_mem {G : QuantumMaxCutEnergy.Input} {t : ℚ}
    {P : QMCLeafB.FinalStroke.RunParams G}
    {cX : ℕ → Matrix (Fin G.n) (Fin G.n) ℚ} {k : ℕ}
    (h : QMCLeafB.RelaxOracle.RelaxMem (QMCLeafB.Finalization.wMatrixQ G) (cX k)
      (t - QMCLeafB.RundataCert.eps G) P.dq) :
    QMCLeafB.RecordsM2.margOf G t P cX k = 1 := by
  simp only [QMCLeafB.RecordsM2.margOf, QMCLeafB.FlagsM5.cutOf, dif_pos h,
    QMCLeafB.FlagsM5.defaultCut]

#print axioms QMCLeafB.OkProdM6.margOf_of_mem

/-- **At a member round the canonical normal vanishes**, so the dilated normal of that round is
`λ_k • u₀` — a multiple of the trace direction alone. -/
theorem nrmOf_of_mem {G : QuantumMaxCutEnergy.Input} {t : ℚ}
    {P : QMCLeafB.FinalStroke.RunParams G}
    {cX : ℕ → Matrix (Fin G.n) (Fin G.n) ℚ} {k : ℕ}
    (h : QMCLeafB.RelaxOracle.RelaxMem (QMCLeafB.Finalization.wMatrixQ G) (cX k)
      (t - QMCLeafB.RundataCert.eps G) P.dq) :
    QMCLeafB.RecordsM2.nrmOf G t P cX k = 0 := by
  unfold QMCLeafB.RecordsM2.nrmOf
  rw [show (QMCLeafB.FlagsM5.cutOf G t P cX k).normal = 0 from by
    simp only [QMCLeafB.FlagsM5.cutOf, dif_pos h, QMCLeafB.FlagsM5.defaultCut]]
  rfl

#print axioms QMCLeafB.OkProdM6.nrmOf_of_mem

/-! ## 8.  Which rounds are cut rounds, at the run's own centres

`diagPinch` fixes the diagonal at `1 − dq/4` exactly, so the `diag_near` clause of `RelaxMem` can
never fail at a centre of the form `cXst`.  A round is therefore a cut round exactly when its pinched
centre is PSD-violating or above the objective band — the two branches the constructive oracle
produces, and the two a campaign check has to look at. -/

/-- **The cut-round test at a pinched centre.** -/
theorem flag_cXst_false_iff {G : QuantumMaxCutEnergy.Input} {t : ℚ}
    {P : QMCLeafB.FinalStroke.RunParams G} {X : ℕ → List ℚ} (k : ℕ)
    (hdq : 0 < P.dq) (hdq4 : P.dq ≤ 4) :
    flagOf G t P (cXst G.n X P.dq) k = false ↔
      (∃ x : Fin G.n → ℚ,
          qf (cXst G.n X P.dq k) x < -(P.dq / 2) * ∑ i, x i ^ 2)
        ∨ (t - QMCLeafB.RundataCert.eps G + P.dq / 2
            < frob (QMCLeafB.Finalization.wMatrixQ G) (cXst G.n X P.dq k)) := by
  have hdiag : ∀ i, |cXst G.n X P.dq k i i - 1| ≤ P.dq / 4 := fun i =>
    QMCLeafB.CentreAdm.abs_diagPinch (QMCLeafB.StateDiag.stMat G.n (X k)) hdq hdq4 i
  constructor
  · intro hf
    have hnot : ¬ QMCLeafB.RelaxOracle.RelaxMem (QMCLeafB.Finalization.wMatrixQ G)
        (cXst G.n X P.dq k) (t - QMCLeafB.RundataCert.eps G) P.dq := by
      intro hM
      rw [QMCLeafB.RecordsM2.flagOf_eq_true_of_mem hM] at hf
      exact absurd hf (by simp)
    by_cases hpsd : ∃ x : Fin G.n → ℚ,
        qf (cXst G.n X P.dq k) x < -(P.dq / 2) * ∑ i, x i ^ 2
    · exact Or.inl hpsd
    · refine Or.inr ?_
      by_contra htr
      push Not at htr
      push Not at hpsd
      exact hnot ⟨hdq, hpsd, hdiag, htr⟩
  · rintro (⟨x, hx⟩ | htr)
    · exact QMCLeafB.RecordsM2.flag_false_of_psdMargin ⟨x, hx⟩
    · exact QMCLeafB.FlagsM5.flagOf_false_of_not_mem G t P (cXst G.n X P.dq) k
        (QMCLeafB.RecordsM2.notMem_of_trace htr)

#print axioms QMCLeafB.OkProdM6.flag_cXst_false_iff

/-- **The objective test at a pinched centre is the state's own test** — the overwrite is invisible
to `frob` because `wMatrixQ` has zero diagonal. -/
theorem trace_test_cXst {G : QuantumMaxCutEnergy.Input} (X : ℕ → List ℚ) (dq : ℚ) (k : ℕ) :
    frob (QMCLeafB.Finalization.wMatrixQ G) (cXst G.n X dq k)
      = frob (QMCLeafB.Finalization.wMatrixQ G)
          (QMCLeafB.StateDiag.stMat G.n (X k)) :=
  QMCLeafB.RecordsM2.frob_cXst (QMCLeafB.RecordsM2.wMatrixQ_diag G)

#print axioms QMCLeafB.OkProdM6.trace_test_cXst

/-! ## 9.  The fix: a **constructive** canonical cut with the same flags and explicit normals

§7 shows the drift slots are unprovable at `FlagsM5.cutOf` because its cut branch is
`Classical.choice` of an always-inhabited `Nonempty`.  The repair is surgical: keep the *member* test
exactly (`if h : RelaxMem …`), but on the cut side return the **choice-free** oracle
`RelaxOracle.relaxOracle`'s record instead of a `Classical.choice`.  Then

* the flag classification is **unchanged by construction** (`cutOfC_of_mem` is `dif_pos`, and on the
  cut side both definitions test the same `RelaxMem`), so every `flagOf`-shaped slot of the whole
  cone — `hverdict`, `hcutfin`, `flag_cXst_of_ok`, `cut_rounds_exactly_below_horizon` — transfers
  verbatim;
* the normals and margins become **explicit**: `cutOfC_trace` names them at a trace-excess round
  (`normal = -A`, `margin` = the excess), and the oracle's other two branches are
  `diagonal (diagNormalSum cX δ)` and `vecMulVec v v` (`RelaxOracle.diagSumCut`, `psdCutOf`).

So swapping `cutOf` for `cutOfC` in `RecordsM2.nrmOf`/`margOf` makes phase-20's named residual (a)
a statement about named rational data. -/

/-- **The constructive canonical cut record.**  Member side: the trivial record, exactly as
`FlagsM5.cutOf`.  Cut side: the choice-free oracle's own separating record. -/
noncomputable def cutOfC {n : ℕ} (A cX : Matrix (Fin n) (Fin n) ℚ) (u δ : ℚ)
    (hδ : 0 < δ) (hs : cXᵀ = cX) : QMCLeafB.RelaxOracle.RelaxCut A cX u δ :=
  if h : QMCLeafB.RelaxOracle.RelaxMem A cX u δ then QMCLeafB.FlagsM5.defaultCut A cX u δ
  else
    match QMCLeafB.RelaxOracle.relaxOracle A cX u δ hδ hs with
    | .mem h' => absurd h' h
    | .cut C => C

/-- **The member side is `defaultCut`** — so `nrmOf = 0` and `margOf = 1` exactly as for `cutOf`
(`nrmOf_of_mem`, `margOf_of_mem` transfer verbatim). -/
theorem cutOfC_of_mem {n : ℕ} {A cX : Matrix (Fin n) (Fin n) ℚ} {u δ : ℚ}
    (hδ : 0 < δ) (hs : cXᵀ = cX)
    (h : QMCLeafB.RelaxOracle.RelaxMem A cX u δ) :
    cutOfC A cX u δ hδ hs = QMCLeafB.FlagsM5.defaultCut A cX u δ :=
  dif_pos h

#print axioms QMCLeafB.OkProdM6.cutOfC_of_mem

/-- **`cutOfC` has `cutOf_spec`'s two clauses** — the drop-in requirement. -/
theorem cutOfC_spec {n : ℕ} (A cX : Matrix (Fin n) (Fin n) ℚ) (u δ : ℚ)
    (hδ : 0 < δ) (hs : cXᵀ = cX) :
    0 < (cutOfC A cX u δ hδ hs).margin ∧
      ∀ X : Matrix (Fin n) (Fin n) ℝ,
        QMCLeafB.BallFloor.relaxBodyLE (QMCLeafB.SepOracle.castMat A) ((u : ℚ) : ℝ)
            ((δ : ℚ) : ℝ) X →
          -((((cutOfC A cX u δ hδ hs).margin : ℚ)) : ℝ) ≤
            frob (QMCLeafB.SepOracle.castMat (cutOfC A cX u δ hδ hs).normal)
              (X - QMCLeafB.SepOracle.castMat cX) := by
  unfold cutOfC
  by_cases h : QMCLeafB.RelaxOracle.RelaxMem A cX u δ
  · rw [dif_pos h]
    exact ⟨(QMCLeafB.FlagsM5.defaultCut A cX u δ).margin_pos,
      fun X hX => (QMCLeafB.FlagsM5.defaultCut A cX u δ).separates X hX⟩
  · rw [dif_neg h]
    cases hr : QMCLeafB.RelaxOracle.relaxOracle A cX u δ hδ hs with
    | mem h' => exact absurd h' h
    | cut C => exact ⟨C.margin_pos, fun X hX => C.separates X hX⟩

#print axioms QMCLeafB.OkProdM6.cutOfC_spec

/-- **At a trace-excess round the constructive record is `(-A, excess)`** — the explicit normal that
the drift slots need.  (The other two branches are equally explicit: `diagonal (diagNormalSum cX δ)`
and `vecMulVec v v`.) -/
theorem cutOfC_trace {n : ℕ} {A cX : Matrix (Fin n) (Fin n) ℚ} {u δ : ℚ}
    (hδ : 0 < δ) (hs : cXᵀ = cX) (h : u + δ / 2 < frob A cX) :
    (cutOfC A cX u δ hδ hs).normal = -A
      ∧ (cutOfC A cX u δ hδ hs).margin = frob A cX - (u + δ / 2) := by
  have hnot : ¬ QMCLeafB.RelaxOracle.RelaxMem A cX u δ :=
    QMCLeafB.RecordsM2.notMem_of_trace h
  unfold cutOfC
  rw [dif_neg hnot]
  have htr : ¬ (frob A cX ≤ u + δ / 2) := not_le_of_gt h
  unfold QMCLeafB.RelaxOracle.relaxOracle
  rw [dif_neg htr]
  exact ⟨rfl, rfl⟩

#print axioms QMCLeafB.OkProdM6.cutOfC_trace

/-! ## 10.  The symmetry-free version: a drop-in with `FlagsM5.cutOf`'s own argument list

§9's `cutOfC` needs the centre's symmetry (`RelaxOracle.relaxOracle` splits `cX + (δ/2)·1`), so
`RecordsM2.nrmOf`/`margOf` would have to carry an extra hypothesis and every drift slot would change
type.  Symmetrising inside the psd branch removes even that: `qf` only sees the symmetric part
(`qf_transpose_avg`), so splitting `((cX + cXᵀ)/2) + (δ/2)·1` — symmetric by construction — decides
the same psd clause.  `cutOfC₀` therefore takes exactly `cutOf`'s arguments plus `hδ`, and
`RecordsM2.nrmOf`/`margOf` can be redefined by threading `P.hdq` and **nothing else** changes. -/

/-- `qf` is blind to transposition. -/
theorem qf_transpose {n : ℕ} (M : Matrix (Fin n) (Fin n) ℚ) (x : Fin n → ℚ) :
    qf Mᵀ x = qf M x := by
  unfold QMCLeafB.SepOracle.qf
  rw [Matrix.dotProduct_mulVec, Matrix.vecMul_transpose, dotProduct_comm]

#print axioms QMCLeafB.OkProdM6.qf_transpose

/-- **`qf` only sees the symmetric part.** -/
theorem qf_transpose_avg {n : ℕ} (M : Matrix (Fin n) (Fin n) ℚ) (x : Fin n → ℚ) :
    qf ((1 / 2 : ℚ) • (M + Mᵀ)) x = qf M x := by
  rw [QMCLeafB.SepOracle.qf_smulQ, QMCLeafB.SepOracle.qf_add, qf_transpose]
  ring

#print axioms QMCLeafB.OkProdM6.qf_transpose_avg

/-- The symmetrised shifted matrix is symmetric. -/
theorem symm_avg_shift {n : ℕ} (cX : Matrix (Fin n) (Fin n) ℚ) (δ : ℚ) :
    (((1 / 2 : ℚ) • (cX + cXᵀ)) + (δ / 2) • (1 : Matrix (Fin n) (Fin n) ℚ))ᵀ
      = ((1 / 2 : ℚ) • (cX + cXᵀ)) + (δ / 2) • (1 : Matrix (Fin n) (Fin n) ℚ) := by
  rw [Matrix.transpose_add, Matrix.transpose_smul, Matrix.transpose_add,
    Matrix.transpose_transpose, Matrix.transpose_smul, Matrix.transpose_one, add_comm cXᵀ cX]

#print axioms QMCLeafB.OkProdM6.symm_avg_shift

/-- **The symmetry-free constructive canonical cut.**  Same member test as `FlagsM5.cutOf`, same
argument list plus `hδ`, and every branch is the choice-free oracle's own record. -/
noncomputable def cutOfC₀ {n : ℕ} (A cX : Matrix (Fin n) (Fin n) ℚ) (u δ : ℚ) (hδ : 0 < δ) :
    QMCLeafB.RelaxOracle.RelaxCut A cX u δ :=
  if h : QMCLeafB.RelaxOracle.RelaxMem A cX u δ then QMCLeafB.FlagsM5.defaultCut A cX u δ
  else if htr : frob A cX ≤ u + δ / 2 then
    if hdg : QMCLeafB.RelaxOracle.diagMarginSum cX δ = 0 then
      match QMCLeafB.SepOracle.splitOfTranspose n
          (((1 / 2 : ℚ) • (cX + cXᵀ)) + (δ / 2) • (1 : Matrix (Fin n) (Fin n) ℚ))
          (symm_avg_shift cX δ) with
      | .psd _ _ _ => QMCLeafB.FlagsM5.defaultCut A cX u δ
      | .violated v hv =>
          QMCLeafB.RelaxOracle.psdCutOf (A := A) (cX := cX) (u := u) (δ := δ) (v := v) (by
            have h1 : qf (((1 / 2 : ℚ) • (cX + cXᵀ))
                  + (δ / 2) • (1 : Matrix (Fin n) (Fin n) ℚ)) v
                = qf cX v + (δ / 2) * ∑ i, v i ^ 2 := by
              rw [QMCLeafB.SepOracle.qf_add, qf_transpose_avg,
                QMCLeafB.SepOracle.qf_smulQ, QMCLeafB.RelaxOracle.qf_one]
            linarith)
    else QMCLeafB.RelaxOracle.diagSumCut (A := A) (cX := cX) (u := u) (δ := δ)
      (lt_of_le_of_ne (QMCLeafB.RelaxOracle.diagMarginSum_nonneg cX δ) (Ne.symm hdg))
  else QMCLeafB.RelaxOracle.traceHighCutOf (A := A) (cX := cX) (u := u) (δ := δ)
    (lt_of_not_ge htr)

/-- **The member side is `defaultCut`**, exactly as for `FlagsM5.cutOf` and `cutOfC`. -/
theorem cutOfC₀_of_mem {n : ℕ} {A cX : Matrix (Fin n) (Fin n) ℚ} {u δ : ℚ} (hδ : 0 < δ)
    (h : QMCLeafB.RelaxOracle.RelaxMem A cX u δ) :
    cutOfC₀ A cX u δ hδ = QMCLeafB.FlagsM5.defaultCut A cX u δ :=
  dif_pos h

#print axioms QMCLeafB.OkProdM6.cutOfC₀_of_mem

/-- **`cutOfC₀` satisfies `cutOf_spec`** — the drop-in requirement. -/
theorem cutOfC₀_spec {n : ℕ} (A cX : Matrix (Fin n) (Fin n) ℚ) (u δ : ℚ) (hδ : 0 < δ) :
    0 < (cutOfC₀ A cX u δ hδ).margin ∧
      ∀ X : Matrix (Fin n) (Fin n) ℝ,
        QMCLeafB.BallFloor.relaxBodyLE (QMCLeafB.SepOracle.castMat A) ((u : ℚ) : ℝ)
            ((δ : ℚ) : ℝ) X →
          -((((cutOfC₀ A cX u δ hδ).margin : ℚ)) : ℝ) ≤
            frob (QMCLeafB.SepOracle.castMat (cutOfC₀ A cX u δ hδ).normal)
              (X - QMCLeafB.SepOracle.castMat cX) := by
  unfold cutOfC₀
  by_cases h : QMCLeafB.RelaxOracle.RelaxMem A cX u δ
  · rw [dif_pos h]
    exact ⟨(QMCLeafB.FlagsM5.defaultCut A cX u δ).margin_pos,
      fun X hX => (QMCLeafB.FlagsM5.defaultCut A cX u δ).separates X hX⟩
  · rw [dif_neg h]
    by_cases htr : frob A cX ≤ u + δ / 2
    · rw [dif_pos htr]
      by_cases hdg : QMCLeafB.RelaxOracle.diagMarginSum cX δ = 0
      · rw [dif_pos hdg]
        cases QMCLeafB.SepOracle.splitOfTranspose n
            (((1 / 2 : ℚ) • (cX + cXᵀ)) + (δ / 2) • (1 : Matrix (Fin n) (Fin n) ℚ))
            (symm_avg_shift cX δ) with
        | psd m C hC =>
            exact ⟨(QMCLeafB.FlagsM5.defaultCut A cX u δ).margin_pos,
              fun X hX => (QMCLeafB.FlagsM5.defaultCut A cX u δ).separates X hX⟩
        | violated v hv =>
            exact ⟨(QMCLeafB.RelaxOracle.psdCutOf (A := A) (cX := cX) (u := u) (δ := δ)
                (v := v) _).margin_pos,
              fun X hX => (QMCLeafB.RelaxOracle.psdCutOf (A := A) (cX := cX) (u := u)
                (δ := δ) (v := v) _).separates X hX⟩
      · rw [dif_neg hdg]
        exact ⟨(QMCLeafB.RelaxOracle.diagSumCut (A := A) (cX := cX) (u := u) (δ := δ) _).margin_pos,
          fun X hX => (QMCLeafB.RelaxOracle.diagSumCut (A := A) (cX := cX) (u := u) (δ := δ)
            _).separates X hX⟩
    · rw [dif_neg htr]
      exact ⟨(QMCLeafB.RelaxOracle.traceHighCutOf (A := A) (cX := cX) (u := u) (δ := δ) _).margin_pos,
        fun X hX => (QMCLeafB.RelaxOracle.traceHighCutOf (A := A) (cX := cX) (u := u) (δ := δ)
          _).separates X hX⟩

#print axioms QMCLeafB.OkProdM6.cutOfC₀_spec

/-- **At a trace-excess round the symmetry-free record is `(-A, excess)`** — the explicit normal the
drift slots need, with no symmetry hypothesis anywhere. -/
theorem cutOfC₀_trace {n : ℕ} {A cX : Matrix (Fin n) (Fin n) ℚ} {u δ : ℚ} (hδ : 0 < δ)
    (h : u + δ / 2 < frob A cX) :
    (cutOfC₀ A cX u δ hδ).normal = -A
      ∧ (cutOfC₀ A cX u δ hδ).margin = frob A cX - (u + δ / 2) := by
  have hnot : ¬ QMCLeafB.RelaxOracle.RelaxMem A cX u δ :=
    QMCLeafB.RecordsM2.notMem_of_trace h
  unfold cutOfC₀
  rw [dif_neg hnot, dif_neg (not_le_of_gt h)]
  exact ⟨rfl, rfl⟩

#print axioms QMCLeafB.OkProdM6.cutOfC₀_trace

/-! ## 11.  The run-level abbreviations for the swap, and their two known cases

Copy-paste replacement for `RecordsM2.nrmOf`/`margOf` (same argument list, `P.hdq` supplied
internally), together with the two values that are pinned down: the member case (`0`, `1`) and the
trace-excess case (`-flatQ A`, the excess).  Everything built on `nrmOf`/`margOf` — `lamOf`, `cnOf`,
`cutStream`, and therefore the whole drift side — becomes a function of named rational data. -/

/-- The constructive canonical normal of round `k`. -/
abbrev nrmOfC (G : QuantumMaxCutEnergy.Input) (t : ℚ)
    (P : QMCLeafB.FinalStroke.RunParams G)
    (cX : ℕ → Matrix (Fin G.n) (Fin G.n) ℚ) (k : ℕ) : Fin (G.n * G.n) → ℚ :=
  QMCLeafB.RelaxOracle.flatQ
    (cutOfC₀ (QMCLeafB.Finalization.wMatrixQ G) (cX k)
      (t - QMCLeafB.RundataCert.eps G) P.dq P.hdq).normal

/-- The constructive canonical margin of round `k`. -/
abbrev margOfC (G : QuantumMaxCutEnergy.Input) (t : ℚ)
    (P : QMCLeafB.FinalStroke.RunParams G)
    (cX : ℕ → Matrix (Fin G.n) (Fin G.n) ℚ) (k : ℕ) : ℚ :=
  (cutOfC₀ (QMCLeafB.Finalization.wMatrixQ G) (cX k)
    (t - QMCLeafB.RundataCert.eps G) P.dq P.hdq).margin

/-- **Member round**: the constructive normal vanishes — exactly as for `nrmOf`. -/
theorem nrmOfC_of_mem {G : QuantumMaxCutEnergy.Input} {t : ℚ}
    {P : QMCLeafB.FinalStroke.RunParams G}
    {cX : ℕ → Matrix (Fin G.n) (Fin G.n) ℚ} {k : ℕ}
    (h : QMCLeafB.RelaxOracle.RelaxMem (QMCLeafB.Finalization.wMatrixQ G) (cX k)
      (t - QMCLeafB.RundataCert.eps G) P.dq) :
    nrmOfC G t P cX k = 0 := by
  unfold nrmOfC
  rw [cutOfC₀_of_mem P.hdq h]
  rfl

#print axioms QMCLeafB.OkProdM6.nrmOfC_of_mem

/-- **Member round**: the constructive margin is `1`. -/
theorem margOfC_of_mem {G : QuantumMaxCutEnergy.Input} {t : ℚ}
    {P : QMCLeafB.FinalStroke.RunParams G}
    {cX : ℕ → Matrix (Fin G.n) (Fin G.n) ℚ} {k : ℕ}
    (h : QMCLeafB.RelaxOracle.RelaxMem (QMCLeafB.Finalization.wMatrixQ G) (cX k)
      (t - QMCLeafB.RundataCert.eps G) P.dq) :
    margOfC G t P cX k = 1 := by
  unfold margOfC
  rw [cutOfC₀_of_mem P.hdq h]
  rfl

#print axioms QMCLeafB.OkProdM6.margOfC_of_mem

/-- **Trace-excess round**: the constructive normal is the *fixed* vector `-flatQ A`, independent of
the round and of the centre. -/
theorem nrmOfC_trace {G : QuantumMaxCutEnergy.Input} {t : ℚ}
    {P : QMCLeafB.FinalStroke.RunParams G}
    {cX : ℕ → Matrix (Fin G.n) (Fin G.n) ℚ} {k : ℕ}
    (h : t - QMCLeafB.RundataCert.eps G + P.dq / 2
      < frob (QMCLeafB.Finalization.wMatrixQ G) (cX k)) :
    nrmOfC G t P cX k = -QMCLeafB.RelaxOracle.flatQ (QMCLeafB.Finalization.wMatrixQ G) := by
  unfold nrmOfC
  rw [(cutOfC₀_trace P.hdq h).1]
  funext i
  simp [QMCLeafB.RelaxOracle.flatQ, Matrix.neg_apply]

#print axioms QMCLeafB.OkProdM6.nrmOfC_trace

/-- **Trace-excess round**: the constructive margin is the excess. -/
theorem margOfC_trace {G : QuantumMaxCutEnergy.Input} {t : ℚ}
    {P : QMCLeafB.FinalStroke.RunParams G}
    {cX : ℕ → Matrix (Fin G.n) (Fin G.n) ℚ} {k : ℕ}
    (h : t - QMCLeafB.RundataCert.eps G + P.dq / 2
      < frob (QMCLeafB.Finalization.wMatrixQ G) (cX k)) :
    margOfC G t P cX k
      = frob (QMCLeafB.Finalization.wMatrixQ G) (cX k)
        - (t - QMCLeafB.RundataCert.eps G + P.dq / 2) := by
  unfold margOfC
  rw [(cutOfC₀_trace P.hdq h).2]

#print axioms QMCLeafB.OkProdM6.margOfC_trace

end QMCLeafB.OkProdM6


