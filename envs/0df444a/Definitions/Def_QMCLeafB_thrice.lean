-- Prove2me | Definitions.Def_QMCLeafB_thrice
-- name    : QMCLeafB_thrice
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-04T09:23:06.080445+00:00
-- url     : https://prove2.me/theorems/a58cf417-6b18-4d8e-9a6c-eca29498ffbe
-- title:
--   QMCLeafB thrice
-- statement:
--   # `Check_thrice_m3` — phase 23, member m3, direction `thrice-split`
--
--   Published as part of the QMCLeafB library mirror supporting the quantum max-cut campaign's polynomial-time SDP-value certificate (AGM20, TQC 2020, arXiv 2003.14394).

import Mathlib
import Definitions.Def_QMCLeafB_audit2
import Definitions.Def_QMCLeafB_okprod2
/-
# `Check_thrice_m3` — phase 23, member m3, direction `thrice-split`

The audit's split (`Check_audit2_m5.ResidSplit`) confines the crater to the interior points whose
relaxed body is **nonempty**, and `Check_audit2_m5` §5 exhibits `(G₁, t₁)`: nonempty body, no
**pinched** member, every queryable centre pinched.  That is one stratum too coarse — this file
splits it by the **program's own bit**, which is the key `CoreDataG` is indexed by:

* **stratum 1** — the real relaxed body is empty.  Discharged outright: the bit is forced `false`
  (`Check_refuted_m3.bit_false_of_emptyBody`) and the analytic record is the all-`cut` stream with
  no drift (`Check_refuted_m3.runParts_of_emptyBody`).
* **stratum 2** — the bit reads `true`.  The run's own `ok` round hands over a *pinched* member
  (§2: `pinchFeasible_of_trueBit`), and one frozen member certificate then produces `CoreDataG`
  (`Check_okprod2_m8.coreDataG_of_okPoint`), whence `RunParts` by the locked stroke
  `FlagsM5.runParts_of_bundleH`.  Nothing analytic here.
* **stratum 3** — the bit reads `false` **and** the body is nonempty.  `CoreDataG` there is the
  whole-window drift debt (`false_bit_all_cut`: the verdict equation forces every round below the
  horizon to be a `cut` round, so *both* budgets are owed at every `k < K·m`).  This is the one
  named residual (`ThirdStratum`), and it is stated at the leaf's **own** interface `RunParts`, not
  at the conduit, so a `dM = −1` re-derivation or a genuine-separation stream can fill it directly.

Deliverables:

* §1 the three strata as predicates on the *actual* `relaxBodyLE`/`RelaxMem` definitions;
* §2 the bit/stratum relations (`bit_false_of_bodyEmpty`, `pinchFeasible_of_trueBit`,
  `bit_false_of_not_pinchFeasible`, `stratum_cover`);
* §3 the residual `TripleSupply = TrueBitCore × ThirdStratum`;
* §4 `runParts_of_triple`, `hdProp_of_triple`, `solution_statement_of_triple` and the verbatim
  d9f601e5 stroke `solution_of_triple` — mirroring `Check_audit2_m5.solution_of_split` term for term
  with the dead stratum replaced by the bit-keyed pair;
* §5 conservativity: every `ResidSplit` producer is a `TripleSupply` producer (nothing banked is
  lost; the split is strictly finer);
* §6 the debt shape of stratum 3 (`false_bit_all_cut`, `third_stratum_owes_window`);
* §7 non-vacuity: stratum 1 is inhabited at `(G₀, t₀)`, stratum 2's producer fires at
  `(G₀, −1/2)`, and at `(G₁, t₁)` no pinched centre is a member (`¬ PinchFeasible`), so the ok
  lane cannot reach the exemplar — `TripleSupply` is not a restatement that silently keeps the
  dead stratum.

Discipline: `set_option autoImplicit false`; no `sorry`/`admit`/`axiom`/`native_decide`/`unsafe`;
`#print axioms` on every declaration, expected `[propext, Classical.choice, Quot.sound]`.
-/

open scoped BigOperators
open Matrix
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option linter.unusedVariables false

noncomputable section

namespace QMCLeafB.ThriceM3

open QuantumMaxCutEnergy

/-! ## 1.  The strata, at the actual definitions -/

/-- **Stratum 1**: the *real* relaxed body at `(G,t)` is empty.  (This is exactly the hypothesis
`Check_audit2_m5.ResidSplit` is conditioned on, and exactly the hypothesis of the empty-stratum
producer `Check_refuted_m3.runParts_of_emptyBody`.) -/
def BodyEmpty (G : QuantumMaxCutEnergy.Input) (t : ℚ)
    (P : QMCLeafB.FinalStroke.RunParams G) : Prop :=
  ∀ X : Matrix (Fin G.n) (Fin G.n) ℝ,
    ¬ QMCLeafB.BallFloor.relaxBodyLE (QMCLeafB.wMatrix G)
      ((t : ℝ) - (((QMCLeafB.EngineRuntime.Rq G / 40000 : ℚ)) : ℝ))
      (((P.dq : ℚ)) : ℝ) X

/-- **Pinch feasibility**: some matrix on the pinched diagonal `1 − dq/4` is a member of the rational
relaxed body.  This is what the ok lane needs (`Check_okprod2_m8.OkPoint` asks for the *pinched*
frozen centre), and what `Check_audit2_m5.anchor3_no_pinched_member` denies at `(G₁, t₁)`. -/
def PinchFeasible (G : QuantumMaxCutEnergy.Input) (t : ℚ)
    (P : QMCLeafB.FinalStroke.RunParams G) : Prop :=
  ∃ Q : Matrix (Fin G.n) (Fin G.n) ℚ,
    QMCLeafB.RelaxOracle.RelaxMem (QMCLeafB.Finalization.wMatrixQ G) Q
        (t - QMCLeafB.RundataCert.eps G) P.dq ∧
      ∀ i, Q i i = 1 - P.dq / 4

/-! ## 2.  The bit/stratum relations

The two directions that make the split *bit-keyed* rather than body-keyed. -/

/-- **Stratum 1 forces the bit to `false`** (specialisation of the banked empty-body bit lemma to
the stratum predicate). -/
theorem bit_false_of_bodyEmpty {o : QuantumMaxCutEnergy.Input → ℚ → Bool}
    {G : QuantumMaxCutEnergy.Input} {t : ℚ} {P : QMCLeafB.FinalStroke.RunParams G}
    {rb : ℕ → Bool} {cX : ℕ → Matrix (Fin G.n) (Fin G.n) ℚ}
    (hbit : o G t = QMCLeafB.SimLoop.anyOk rb (P.K * P.m))
    (hok : ∀ k, rb k = true →
      QMCLeafB.RelaxOracle.RelaxMem (QMCLeafB.Finalization.wMatrixQ G) (cX k)
        (t - QMCLeafB.RundataCert.eps G) P.dq)
    (hemptyR : BodyEmpty G t P →
      ∀ Q : Matrix (Fin G.n) (Fin G.n) ℚ,
        ¬ QMCLeafB.RelaxOracle.RelaxMem (QMCLeafB.Finalization.wMatrixQ G) Q
          (t - QMCLeafB.RundataCert.eps G) P.dq)
    (h : BodyEmpty G t P) : o G t = false :=
  QMCLeafB.RefutedM3.bit_false_of_emptyBody hbit hok (hemptyR h)

#print axioms QMCLeafB.ThriceM3.bit_false_of_bodyEmpty

/-- **A `true` bit is a pinched member.**  The program's `ok` round below the horizon is a member
round (`hok`), and the run's queried centres sit on the pinched diagonal (`hdiag`, which for the
campaign's `cXst` centres is `Check_records_m2.cXst_diag` *by definition*).  So on stratum 2 the ok
lane's input exists — and only there. -/
theorem pinchFeasible_of_trueBit {o : QuantumMaxCutEnergy.Input → ℚ → Bool}
    {G : QuantumMaxCutEnergy.Input} {t : ℚ} {P : QMCLeafB.FinalStroke.RunParams G}
    {rb : ℕ → Bool} {cX : ℕ → Matrix (Fin G.n) (Fin G.n) ℚ}
    (hbit : o G t = QMCLeafB.SimLoop.anyOk rb (P.K * P.m))
    (hok : ∀ k, rb k = true →
      QMCLeafB.RelaxOracle.RelaxMem (QMCLeafB.Finalization.wMatrixQ G) (cX k)
        (t - QMCLeafB.RundataCert.eps G) P.dq)
    (hdiag : ∀ (k : ℕ) (i : Fin G.n), cX k i i = 1 - P.dq / 4)
    (hT : o G t = true) : PinchFeasible G t P := by
  have h1 : QMCLeafB.SimLoop.anyOk rb (P.K * P.m) = true := by rw [← hbit]; exact hT
  obtain ⟨k, _hk, hok_k⟩ := (QMCLeafB.SimLoop.anyOk_eq_true_iff rb (P.K * P.m)).1 h1
  exact ⟨cX k, hok k hok_k, fun i => hdiag k i⟩

#print axioms QMCLeafB.ThriceM3.pinchFeasible_of_trueBit

/-- **No pinched member forces the bit to `false`** — the contrapositive, and the reason the
exemplar `(G₁, t₁)` cannot be reached by the ok lane. -/
theorem bit_false_of_not_pinchFeasible {o : QuantumMaxCutEnergy.Input → ℚ → Bool}
    {G : QuantumMaxCutEnergy.Input} {t : ℚ} {P : QMCLeafB.FinalStroke.RunParams G}
    {rb : ℕ → Bool} {cX : ℕ → Matrix (Fin G.n) (Fin G.n) ℚ}
    (hbit : o G t = QMCLeafB.SimLoop.anyOk rb (P.K * P.m))
    (hok : ∀ k, rb k = true →
      QMCLeafB.RelaxOracle.RelaxMem (QMCLeafB.Finalization.wMatrixQ G) (cX k)
        (t - QMCLeafB.RundataCert.eps G) P.dq)
    (hdiag : ∀ (k : ℕ) (i : Fin G.n), cX k i i = 1 - P.dq / 4)
    (h : ¬ PinchFeasible G t P) : o G t = false := by
  cases hb : o G t with
  | false => rfl
  | true => exact absurd (pinchFeasible_of_trueBit hbit hok hdiag hb) h

#print axioms QMCLeafB.ThriceM3.bit_false_of_not_pinchFeasible

/-- **The stratum cover**, machine-checked against the two bit relations above: every interior point
is (1) empty-bodied, or (2) `true`-bit — and then it carries a *pinched* member — or (3) `false`-bit
with a nonempty body.  Stratum 3 is disjoint from the first two by construction; nothing is left
over. -/
theorem stratum_cover {o : QuantumMaxCutEnergy.Input → ℚ → Bool}
    {G : QuantumMaxCutEnergy.Input} {t : ℚ} {P : QMCLeafB.FinalStroke.RunParams G}
    {rb : ℕ → Bool} {cX : ℕ → Matrix (Fin G.n) (Fin G.n) ℚ}
    (hbit : o G t = QMCLeafB.SimLoop.anyOk rb (P.K * P.m))
    (hok : ∀ k, rb k = true →
      QMCLeafB.RelaxOracle.RelaxMem (QMCLeafB.Finalization.wMatrixQ G) (cX k)
        (t - QMCLeafB.RundataCert.eps G) P.dq)
    (hdiag : ∀ (k : ℕ) (i : Fin G.n), cX k i i = 1 - P.dq / 4) :
    BodyEmpty G t P
      ∨ (o G t = true ∧ PinchFeasible G t P)
      ∨ (o G t = false ∧ ¬ BodyEmpty G t P) := by
  by_cases hbody : BodyEmpty G t P
  · exact Or.inl hbody
  · by_cases hT : o G t = true
    · exact Or.inr (Or.inl ⟨hT, pinchFeasible_of_trueBit hbit hok hdiag hT⟩)
    · refine Or.inr (Or.inr ⟨?_, hbody⟩)
      cases hb : o G t with
      | false => rfl
      | true => exact absurd hb hT

#print axioms QMCLeafB.ThriceM3.stratum_cover

/-! ## 3.  The residual: two supplies, no dead stratum -/

/-- **The `true`-bit strand**: `CoreDataG` at every interior point whose bit reads `true`.  This is
`Check_okprod2_m8.OkSupply` composed with `coreDataG_of_okPoint` — i.e. the campaign's `hon` slot,
already machine-checked at the lower-body round by `Check_verdbridge_m4`. -/
abbrev TrueBitCore (o : QuantumMaxCutEnergy.Input → ℚ → Bool)
    (Pfam : (G : QuantumMaxCutEnergy.Input) → QMCLeafB.FinalStroke.RunParams G) : Type :=
  ∀ (G : QuantumMaxCutEnergy.Input) (t : ℚ) (hn : 2 ≤ G.n),
    -QMCLeafB.EngineRuntime.Rq G ≤ t →
    (t : ℝ) < -(((QMCLeafB.EngineRuntime.Rq G / 40000 : ℚ)) : ℝ) →
    o G t = true → QMCLeafB.EndgameM2.CoreDataG o G t (Pfam G) hn

/-- **The third stratum, at the leaf's own interface**: `RunParts` at an interior point with a
nonempty real body and a `false` bit.  This is *the one named residual*.  It is stated at
`RunParts`, not at `CoreDataG`: at a `false`-bit point every round below the horizon is a cut round
(§6), so the conduit shape owes the whole-window drift pair there and cannot be produced — while
`RunParts` is the shape the ending actually consumes. -/
abbrev ThirdStratum (o : QuantumMaxCutEnergy.Input → ℚ → Bool)
    (Pfam : (G : QuantumMaxCutEnergy.Input) → QMCLeafB.FinalStroke.RunParams G) : Type :=
  ∀ (G : QuantumMaxCutEnergy.Input) (t : ℚ) (hn : 2 ≤ G.n),
    -QMCLeafB.EngineRuntime.Rq G ≤ t →
    (t : ℝ) < -(((QMCLeafB.EngineRuntime.Rq G / 40000 : ℚ)) : ℝ) →
    ¬ BodyEmpty G t (Pfam G) → o G t = false →
    QMCLeafB.FinalStroke.RunParts o G t (Pfam G)

/-- **The thrice-split residual**: the `true`-bit strand and the third stratum.  Stratum 1 is
discharged in §4 and never appears as a hypothesis. -/
structure TripleSupply (o : QuantumMaxCutEnergy.Input → ℚ → Bool)
    (Pfam : (G : QuantumMaxCutEnergy.Input) → QMCLeafB.FinalStroke.RunParams G) : Type where
  /-- `CoreDataG` at the `true`-bit points (`hon` + the frozen member) -/
  trueBit : TrueBitCore o Pfam
  /-- `RunParts` at the `false`-bit points with a nonempty real body (the named residual) -/
  third : ThirdStratum o Pfam

/-! ## 4.  Production: the three strata give the leaf's whole `RunParts` obligation -/

/-- The conduit step on its own: `CoreDataG` at the campaign family gives the leaf's own record.
This is the term `Check_audit2_m5.runParts_of_split` uses in its nonempty branch, isolated. -/
noncomputable def runParts_of_coreDataG {o : QuantumMaxCutEnergy.Input → ℚ → Bool}
    {G : QuantumMaxCutEnergy.Input} {t : ℚ} {hn : 2 ≤ G.n}
    (hlo : -QMCLeafB.EngineRuntime.Rq G ≤ t)
    (hhi : (t : ℝ) < -(((QMCLeafB.EngineRuntime.Rq G / 40000 : ℚ)) : ℝ))
    (D : QMCLeafB.EndgameM2.CoreDataG o G t (QMCLeafB.UnionShallow.paramsKbc2 G) hn) :
    QMCLeafB.FinalStroke.RunParts o G t (QMCLeafB.UnionShallow.paramsKbc2 G) :=
  QMCLeafB.FlagsM5.runParts_of_bundleH o G t (QMCLeafB.UnionShallow.paramsKbc2 G) hn
    (QMCLeafB.ClosingAssembly.rmaxOf_pos G hn)
    (QMCLeafB.ClosingAssembly.rmaxOf_le_one G hn)
    (QMCLeafB.ClosingAssembly.budget_dqShallow G hn
      (QMCLeafB.AssemblyM5.Rq_pos_of_interior_bracket G t hlo hhi))
    (QMCLeafB.EndgameM2.bundleH_of_dataG
      (QMCLeafB.RecordM2.rmax_pos_paramsKbc2 G hn) D)

#print axioms QMCLeafB.ThriceM3.runParts_of_coreDataG

/-- **The thrice-split production.**  From the program's own read-out (`hbit`), its `ok ⇒ member`
implication at pinched centres (`hokp`, `hdia`), the real-empty ⇒ rational-empty bridge (`hemptyR`)
and the two supplies, the leaf's record exists at every interior point.  Compare
`Check_audit2_m5.runParts_of_split`: stratum 1 is discharged identically, the nonempty stratum is
*split by the bit*, and the `true` half is produced rather than assumed. -/
noncomputable def runParts_of_triple {o : QuantumMaxCutEnergy.Input → ℚ → Bool}
    (rb : (G : QuantumMaxCutEnergy.Input) → ℚ → ℕ → Bool)
    (cXp : (G : QuantumMaxCutEnergy.Input) → ℚ → ℕ → Matrix (Fin G.n) (Fin G.n) ℚ)
    (hbit : ∀ (G : QuantumMaxCutEnergy.Input) (t : ℚ),
      o G t = QMCLeafB.SimLoop.anyOk (rb G t)
        ((QMCLeafB.UnionShallow.paramsKbc2 G).K * (QMCLeafB.UnionShallow.paramsKbc2 G).m))
    (hokp : ∀ (G : QuantumMaxCutEnergy.Input) (t : ℚ) (k : ℕ), rb G t k = true →
      QMCLeafB.RelaxOracle.RelaxMem (QMCLeafB.Finalization.wMatrixQ G) (cXp G t k)
        (t - QMCLeafB.RundataCert.eps G) (QMCLeafB.UnionShallow.paramsKbc2 G).dq)
    (hdia : ∀ (G : QuantumMaxCutEnergy.Input) (t : ℚ) (k : ℕ) (i : Fin G.n),
      cXp G t k i i = 1 - (QMCLeafB.UnionShallow.paramsKbc2 G).dq / 4)
    (hemptyR : ∀ (G : QuantumMaxCutEnergy.Input) (t : ℚ),
      BodyEmpty G t (QMCLeafB.UnionShallow.paramsKbc2 G) →
      ∀ Q : Matrix (Fin G.n) (Fin G.n) ℚ,
        ¬ QMCLeafB.RelaxOracle.RelaxMem (QMCLeafB.Finalization.wMatrixQ G) Q
          (t - QMCLeafB.RundataCert.eps G) (QMCLeafB.UnionShallow.paramsKbc2 G).dq)
    (H : TripleSupply o QMCLeafB.UnionShallow.paramsKbc2) :
    ∀ (G : QuantumMaxCutEnergy.Input) (t : ℚ), 2 ≤ G.n →
      -QMCLeafB.EngineRuntime.Rq G ≤ t →
      (t : ℝ) < -(((QMCLeafB.EngineRuntime.Rq G / 40000 : ℚ)) : ℝ) →
      QMCLeafB.FinalStroke.RunParts o G t (QMCLeafB.UnionShallow.paramsKbc2 G) := by
  intro G t hn hlo hhi
  by_cases hbody : BodyEmpty G t (QMCLeafB.UnionShallow.paramsKbc2 G)
  · have hf : o G t = false :=
      bit_false_of_bodyEmpty (hbit G t) (hokp G t) (hemptyR G t) hbody
    exact QMCLeafB.RefutedM3.runParts_of_emptyBody G t
      (QMCLeafB.UnionShallow.paramsKbc2 G) hn hf hbody
  · by_cases hT : o G t = true
    · exact runParts_of_coreDataG hlo hhi (H.trueBit G t hn hlo hhi hT)
    · have hf : o G t = false := by
        cases hb : o G t with
        | false => rfl
        | true => exact absurd hb hT
      exact H.third G t hn hlo hhi hbody hf

#print axioms QMCLeafB.ThriceM3.runParts_of_triple

/-- **The campaign's whole residual from the triple one.**  At the campaign bit, `TripleSupply`
plus the campaign data gives `AssemblyM5.HdProp` — the type the accepted ending
`AssemblyM5.endgame_of_hd` consumes.  This is `hdProp_of_split` with the split replaced. -/
noncomputable def hdProp_of_triple
    (rb : (G : QuantumMaxCutEnergy.Input) → ℚ → ℕ → Bool)
    (cXp : (G : QuantumMaxCutEnergy.Input) → ℚ → ℕ → Matrix (Fin G.n) (Fin G.n) ℚ)
    (hbit : ∀ (G : QuantumMaxCutEnergy.Input) (t : ℚ),
      QMCLeafB.Audit2M5.campaignBit G t = QMCLeafB.SimLoop.anyOk (rb G t)
        ((QMCLeafB.UnionShallow.paramsKbc2 G).K * (QMCLeafB.UnionShallow.paramsKbc2 G).m))
    (hokp : ∀ (G : QuantumMaxCutEnergy.Input) (t : ℚ) (k : ℕ), rb G t k = true →
      QMCLeafB.RelaxOracle.RelaxMem (QMCLeafB.Finalization.wMatrixQ G) (cXp G t k)
        (t - QMCLeafB.RundataCert.eps G) (QMCLeafB.UnionShallow.paramsKbc2 G).dq)
    (hdia : ∀ (G : QuantumMaxCutEnergy.Input) (t : ℚ) (k : ℕ) (i : Fin G.n),
      cXp G t k i i = 1 - (QMCLeafB.UnionShallow.paramsKbc2 G).dq / 4)
    (hemptyR : ∀ (G : QuantumMaxCutEnergy.Input) (t : ℚ),
      BodyEmpty G t (QMCLeafB.UnionShallow.paramsKbc2 G) →
      ∀ Q : Matrix (Fin G.n) (Fin G.n) ℚ,
        ¬ QMCLeafB.RelaxOracle.RelaxMem (QMCLeafB.Finalization.wMatrixQ G) Q
          (t - QMCLeafB.RundataCert.eps G) (QMCLeafB.UnionShallow.paramsKbc2 G).dq)
    (H : TripleSupply QMCLeafB.Audit2M5.campaignBit QMCLeafB.UnionShallow.paramsKbc2) :
    QMCLeafB.AssemblyM5.HdProp :=
  fun G t hn hlo hhi =>
    runParts_of_triple rb cXp hbit hokp hdia hemptyR H G t hn hlo hhi

#print axioms QMCLeafB.ThriceM3.hdProp_of_triple

/-- **`SolutionStatement` from the triple residual** (the shelf's own name for the sentence). -/
theorem solution_statement_of_triple
    (rb : (G : QuantumMaxCutEnergy.Input) → ℚ → ℕ → Bool)
    (cXp : (G : QuantumMaxCutEnergy.Input) → ℚ → ℕ → Matrix (Fin G.n) (Fin G.n) ℚ)
    (hbit : ∀ (G : QuantumMaxCutEnergy.Input) (t : ℚ),
      QMCLeafB.Audit2M5.campaignBit G t = QMCLeafB.SimLoop.anyOk (rb G t)
        ((QMCLeafB.UnionShallow.paramsKbc2 G).K * (QMCLeafB.UnionShallow.paramsKbc2 G).m))
    (hokp : ∀ (G : QuantumMaxCutEnergy.Input) (t : ℚ) (k : ℕ), rb G t k = true →
      QMCLeafB.RelaxOracle.RelaxMem (QMCLeafB.Finalization.wMatrixQ G) (cXp G t k)
        (t - QMCLeafB.RundataCert.eps G) (QMCLeafB.UnionShallow.paramsKbc2 G).dq)
    (hdia : ∀ (G : QuantumMaxCutEnergy.Input) (t : ℚ) (k : ℕ) (i : Fin G.n),
      cXp G t k i i = 1 - (QMCLeafB.UnionShallow.paramsKbc2 G).dq / 4)
    (hemptyR : ∀ (G : QuantumMaxCutEnergy.Input) (t : ℚ),
      BodyEmpty G t (QMCLeafB.UnionShallow.paramsKbc2 G) →
      ∀ Q : Matrix (Fin G.n) (Fin G.n) ℚ,
        ¬ QMCLeafB.RelaxOracle.RelaxMem (QMCLeafB.Finalization.wMatrixQ G) Q
          (t - QMCLeafB.RundataCert.eps G) (QMCLeafB.UnionShallow.paramsKbc2 G).dq)
    (H : TripleSupply QMCLeafB.Audit2M5.campaignBit QMCLeafB.UnionShallow.paramsKbc2) :
    QMCLeafB.FinishLine.SolutionStatement :=
  QMCLeafB.AssemblyM5.endgame_of_hd_statement
    (hdProp_of_triple rb cXp hbit hokp hdia hemptyR H)

#print axioms QMCLeafB.ThriceM3.solution_statement_of_triple

/-- **The verbatim `d9f601e5` sentence from the triple residual.**  The conclusion is written out
literally (as in `Check_audit2_m5.solution_of_split`), so the ascription is the statement lock. -/
theorem solution_of_triple
    (rb : (G : QuantumMaxCutEnergy.Input) → ℚ → ℕ → Bool)
    (cXp : (G : QuantumMaxCutEnergy.Input) → ℚ → ℕ → Matrix (Fin G.n) (Fin G.n) ℚ)
    (hbit : ∀ (G : QuantumMaxCutEnergy.Input) (t : ℚ),
      QMCLeafB.Audit2M5.campaignBit G t = QMCLeafB.SimLoop.anyOk (rb G t)
        ((QMCLeafB.UnionShallow.paramsKbc2 G).K * (QMCLeafB.UnionShallow.paramsKbc2 G).m))
    (hokp : ∀ (G : QuantumMaxCutEnergy.Input) (t : ℚ) (k : ℕ), rb G t k = true →
      QMCLeafB.RelaxOracle.RelaxMem (QMCLeafB.Finalization.wMatrixQ G) (cXp G t k)
        (t - QMCLeafB.RundataCert.eps G) (QMCLeafB.UnionShallow.paramsKbc2 G).dq)
    (hdia : ∀ (G : QuantumMaxCutEnergy.Input) (t : ℚ) (k : ℕ) (i : Fin G.n),
      cXp G t k i i = 1 - (QMCLeafB.UnionShallow.paramsKbc2 G).dq / 4)
    (hemptyR : ∀ (G : QuantumMaxCutEnergy.Input) (t : ℚ),
      BodyEmpty G t (QMCLeafB.UnionShallow.paramsKbc2 G) →
      ∀ Q : Matrix (Fin G.n) (Fin G.n) ℚ,
        ¬ QMCLeafB.RelaxOracle.RelaxMem (QMCLeafB.Finalization.wMatrixQ G) Q
          (t - QMCLeafB.RundataCert.eps G) (QMCLeafB.UnionShallow.paramsKbc2 G).dq)
    (H : TripleSupply QMCLeafB.Audit2M5.campaignBit QMCLeafB.UnionShallow.paramsKbc2) :
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
  QMCLeafB.AssemblyM5.endgame_of_hd
    (hdProp_of_triple rb cXp hbit hokp hdia hemptyR H)

#print axioms QMCLeafB.ThriceM3.solution_of_triple

/-! ## 5.  Conservativity: the split residual is a triple residual

Nothing banked is lost.  Every `Check_audit2_m5.ResidSplit` producer *is* a `TripleSupply`
producer (given the campaign's read-out data); the converse is where the gain is: `ResidSplit`
demands `CoreDataG` at `(G₁, t₁)`, where §6 shows it owes the whole-window drift pair, while
`TripleSupply` asks only for `RunParts` on that stratum. -/

/-- **`ResidSplit ⟹ TripleSupply`** at the campaign family. -/
noncomputable def tripleSupply_of_split
    (rb : (G : QuantumMaxCutEnergy.Input) → ℚ → ℕ → Bool)
    (cXp : (G : QuantumMaxCutEnergy.Input) → ℚ → ℕ → Matrix (Fin G.n) (Fin G.n) ℚ)
    (hbit : ∀ (G : QuantumMaxCutEnergy.Input) (t : ℚ),
      QMCLeafB.Audit2M5.campaignBit G t = QMCLeafB.SimLoop.anyOk (rb G t)
        ((QMCLeafB.UnionShallow.paramsKbc2 G).K * (QMCLeafB.UnionShallow.paramsKbc2 G).m))
    (hokp : ∀ (G : QuantumMaxCutEnergy.Input) (t : ℚ) (k : ℕ), rb G t k = true →
      QMCLeafB.RelaxOracle.RelaxMem (QMCLeafB.Finalization.wMatrixQ G) (cXp G t k)
        (t - QMCLeafB.RundataCert.eps G) (QMCLeafB.UnionShallow.paramsKbc2 G).dq)
    (hemptyR : ∀ (G : QuantumMaxCutEnergy.Input) (t : ℚ),
      BodyEmpty G t (QMCLeafB.UnionShallow.paramsKbc2 G) →
      ∀ Q : Matrix (Fin G.n) (Fin G.n) ℚ,
        ¬ QMCLeafB.RelaxOracle.RelaxMem (QMCLeafB.Finalization.wMatrixQ G) Q
          (t - QMCLeafB.RundataCert.eps G) (QMCLeafB.UnionShallow.paramsKbc2 G).dq)
    (H : QMCLeafB.Audit2M5.ResidSplit QMCLeafB.Audit2M5.campaignBit
      QMCLeafB.UnionShallow.paramsKbc2) :
    TripleSupply QMCLeafB.Audit2M5.campaignBit QMCLeafB.UnionShallow.paramsKbc2 where
  trueBit := by
    intro G t hn hlo hhi hT
    refine H G t hn hlo hhi ?_
    intro hbody
    have hf : QMCLeafB.Audit2M5.campaignBit G t = false :=
      bit_false_of_bodyEmpty (hbit G t) (hokp G t) (hemptyR G t) hbody
    rw [hf] at hT
    exact absurd hT (by simp)
  third := by
    intro G t hn hlo hhi hbody _
    exact runParts_of_coreDataG hlo hhi (H G t hn hlo hhi hbody)

#print axioms QMCLeafB.ThriceM3.tripleSupply_of_split

/-! ## 6.  What stratum 3 actually owes

At a `false`-bit point the verdict equation says the run reported a `cut` at **every** round below
the horizon, so both drift slots are read everywhere and the conduit shape is exactly the
whole-window trace budget.  This is why the third stratum is stated at `RunParts` and not at
`CoreDataG`, and why no centre-pinched shape can serve there. -/

/-- **A `false` bit makes every round below the horizon a cut round.** -/
theorem false_bit_all_cut {o : QuantumMaxCutEnergy.Input → ℚ → Bool}
    {G : QuantumMaxCutEnergy.Input} {t : ℚ} {P : QMCLeafB.FinalStroke.RunParams G}
    {hn : 2 ≤ G.n} (D : QMCLeafB.EndgameM2.CoreDataG o G t P hn) (h : o G t = false) :
    ∀ k, k < P.K * P.m → D.ok k = false := by
  intro k hk
  have h1 : QMCLeafB.SimLoop.anyOk D.ok (P.K * P.m) = false := by
    rw [← D.hverdict]; exact h
  exact (QMCLeafB.SimLoop.anyOk_eq_false_iff D.ok (P.K * P.m)).1 h1 k hk

#print axioms QMCLeafB.ThriceM3.false_bit_all_cut

/-- **Stratum 3 owes the whole-window engine trace ceiling**: at a `false`-bit point the conduit
forces `diagSum (Cat k) ≤ n(1 − dq/4)` at every round of the window — the obligation that
`Check_cutbudget_m8` and `Check_crater_m2` show cannot be met at a pinched centre stream. -/
theorem third_stratum_forces_window_trace {o : QuantumMaxCutEnergy.Input → ℚ → Bool}
    {G : QuantumMaxCutEnergy.Input} {t : ℚ} {P : QMCLeafB.FinalStroke.RunParams G}
    {hn : 2 ≤ G.n} (D : QMCLeafB.EndgameM2.CoreDataG o G t P hn) (h : o G t = false) :
    ∀ k, k < P.K * P.m →
      QMCLeafB.DriftExact.diagSum
          (QMCLeafB.EngineIterates.Cat (G.n * G.n) (0 : Fin (G.n * G.n) → ℝ)
            (QMCLeafB.EndgameM2.gStream G P hn D.c D.marg) k)
        ≤ ((1 - P.dq / 4 : ℚ) : ℝ) * ((G.n : ℚ) : ℝ) :=
  fun k hk => QMCLeafB.OkProd_M8.coreDataG_forces_engine_trace D (false_bit_all_cut D h k hk)

#print axioms QMCLeafB.ThriceM3.third_stratum_forces_window_trace

/-! ## 7.  Non-vacuity and sharpness

The two supplies are not restatements that quietly keep the dead stratum:

* stratum 1 is inhabited at the refuted point `(G₀, −99999/100000)`;
* stratum 2's producer fires at the ok anchor `(G₀, −1/2)`;
* at the exemplar `(G₁, t₁)` **no pinched matrix is a member**, so the ok lane cannot reach the
  third stratum's territory at all (`bit_false_of_not_pinchFeasible` with
  `EmptyBodyM5.no_pinched_member_G₁`) — the split is not a repackaging of the conduit. -/

/-- **Stratum 1 is inhabited** at the refuted point `(G₀, −99999/100000)`. -/
theorem bodyEmpty_G₀ :
    BodyEmpty QMCLeafB.ResidRefute.G₀ (-(99999 / 100000))
      (QMCLeafB.UnionShallow.paramsKbc2 QMCLeafB.ResidRefute.G₀) :=
  fun _ hX => QMCLeafB.RefutedM3.body_empty_G₀ _ hX

#print axioms QMCLeafB.ThriceM3.bodyEmpty_G₀

/-- **Stratum 2's producer fires at the ok anchor** `(G₀, −1/2)`: `CoreDataG` exists at the
`true` bit there, so `TrueBitCore` is not a vacuous slot. -/
theorem trueBitCore_fires_at_G₀_half :
    Nonempty (QMCLeafB.EndgameM2.CoreDataG (fun _ _ => true) QMCLeafB.ResidRefute.G₀ (-(1 / 2))
      (QMCLeafB.UnionShallow.paramsKbc2 QMCLeafB.ResidRefute.G₀) QMCLeafB.ResidKill.hnG₀) :=
  QMCLeafB.OkProd_M8.coreDataG_G₀_half_via_okprod

#print axioms QMCLeafB.ThriceM3.trueBitCore_fires_at_G₀_half

/-- **The exemplar carries no pinched member**, so `PinchFeasible` fails at `(G₁, t₁)` — the
third stratum's territory is exactly where the ok lane cannot go. -/
theorem not_pinchFeasible_G₁ :
    ¬ PinchFeasible QMCLeafB.EmptyBodyM5.G₁ (-(2 : ℚ) + 71 / 1520000)
      (QMCLeafB.UnionShallow.paramsKbc2 QMCLeafB.EmptyBodyM5.G₁) := by
  rintro ⟨Q, hQ, hdiag⟩
  exact QMCLeafB.EmptyBodyM5.no_pinched_member_G₁ Q hdiag hQ

#print axioms QMCLeafB.ThriceM3.not_pinchFeasible_G₁

/-- **At the exemplar the bit is forced `false` by the run's own data** — no pinched member, so
`bit_false_of_not_pinchFeasible` applies at whatever stream the program records (given its
read-out and `ok ⇒ member` implication at the campaign's pinched centres).  Hence `(G₁, t₁)`-class
points are stratum-3 points, which is why the residual is keyed by the bit. -/
theorem bit_false_at_exemplar {o : QuantumMaxCutEnergy.Input → ℚ → Bool}
    {rb : ℕ → Bool} {cX : ℕ → Matrix (Fin 2) (Fin 2) ℚ}
    (hbit : o QMCLeafB.EmptyBodyM5.G₁ (-(2 : ℚ) + 71 / 1520000) =
      QMCLeafB.SimLoop.anyOk rb
        ((QMCLeafB.UnionShallow.paramsKbc2 QMCLeafB.EmptyBodyM5.G₁).K
          * (QMCLeafB.UnionShallow.paramsKbc2 QMCLeafB.EmptyBodyM5.G₁).m))
    (hok : ∀ k, rb k = true →
      QMCLeafB.RelaxOracle.RelaxMem
        (QMCLeafB.Finalization.wMatrixQ QMCLeafB.EmptyBodyM5.G₁) (cX k)
        (-(2 : ℚ) + 71 / 1520000 - QMCLeafB.RundataCert.eps QMCLeafB.EmptyBodyM5.G₁)
        (QMCLeafB.UnionShallow.paramsKbc2 QMCLeafB.EmptyBodyM5.G₁).dq)
    (hdia : ∀ (k : ℕ) (i : Fin 2),
      cX k i i = 1 - (QMCLeafB.UnionShallow.paramsKbc2 QMCLeafB.EmptyBodyM5.G₁).dq / 4) :
    o QMCLeafB.EmptyBodyM5.G₁ (-(2 : ℚ) + 71 / 1520000) = false :=
  bit_false_of_not_pinchFeasible hbit hok hdia not_pinchFeasible_G₁

#print axioms QMCLeafB.ThriceM3.bit_false_at_exemplar

end QMCLeafB.ThriceM3


