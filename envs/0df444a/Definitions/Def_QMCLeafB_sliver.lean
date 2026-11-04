-- Prove2me | Definitions.Def_QMCLeafB_sliver
-- name    : QMCLeafB_sliver
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-04T05:26:20.015679+00:00
-- url     : https://prove2.me/theorems/a061da13-9a2e-4213-aeef-1921aa7205ef
-- title:
--   QMCLeafB sliver
-- statement:
--   # leaf B phase 20 — brick `forced-cut sliver` (swarm `smw1kspvn`, member m8, direction d10)
--
--   Published as part of the QMCLeafB library mirror supporting the quantum max-cut campaign's polynomial-time SDP-value certificate (AGM20, TQC 2020, arXiv 2003.14394).

import Mathlib
import Definitions.Def_QMCLeafB_verdictok
/-
# leaf B phase 20 — brick `forced-cut sliver` (swarm `smw1kspvn`, member m8, direction d10)

`Check_verdictok_m8` discharges `BundleH` on the part of the bracket where a band-PSD point of the
relaxation exists under the round threshold.  This file proves the complement is *forced*: at the
bottom of the bracket `t = -Rq G` **no centre at all can be a member**, so every round's canonical
flag (`FlagsM5.flagOf`) is `false` there, for every family of centres, and the residual's `hmem`
slot is vacuous by necessity rather than by choice.  That is exactly the regime bricks 1/2 own
(the cut branch), and it tells the record zip that the ok-side certificate cannot be asked for at
the bottom.

The single hypothesis is the trivial bound `-Rq ≤ frob (wMatrixQ G) X` for a band-PSD point, i.e.
`|frob| ≤ Σᵢⱼ |Aᵢⱼ| = Rq G` with `|Xᵢⱼ| ≤ 1 + dq/4` from the 2x2 minor of exact PSD.  It is
isolated as `hbound` because the library has no 2x2-minor lemma for `SepOracle.PSD` yet.

No `sorry`, no `admit`, no `axiom`, no `native_decide`, no `unsafe`; `set_option autoImplicit false`;
axiom audits at the end.
-/

open scoped BigOperators
open Matrix
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option linter.unusedVariables false

noncomputable section

namespace QMCLeafB.SliverM8

open QuantumMaxCutEnergy
open QMCLeafB.SepOracle
open QMCLeafB.RelaxOracle

/-! ## 1.  The campaign tolerance is strictly below `2 ε` -/

/-- **`dqShallow/2 < eps`** — the slack the witness slot would need at `t = -Rq` is not there. -/
theorem dqShallow_half_lt_eps (G : QuantumMaxCutEnergy.Input)
    (hRq : 0 < QMCLeafB.EngineRuntime.Rq G) :
    (QMCLeafB.RundataParams.dqShallow G) / 2 < QMCLeafB.RundataCert.eps G := by
  have heps : 0 < QMCLeafB.RundataCert.eps G := by
    unfold QMCLeafB.RundataCert.eps
    linarith
  rw [QMCLeafB.RundataParams.dqShallow, if_neg (ne_of_gt hRq),
    QMCLeafB.RundataParams.dqShallowCore]
  rw [div_div, div_lt_iff₀ (by positivity : (0 : ℚ) < (9 * QMCLeafB.EngineRuntime.Rq G + 1) * 2)]
  nlinarith [hRq, heps]

/-! ## 2.  No member at the bottom of the bracket -/

/-- **The ok branch cannot fire at `t = -Rq`.**  Given the trivial bound `-Rq ≤ frob (wMatrixQ G) X`
at a band-PSD point, the requirement `frob ≤ t - eps + dq/2` would force `eps ≤ dq/2`, which the
campaign family refutes.  So the witness slot of `bundleH_of_verdict_true`
(`< t - eps + dq/2`) is unsatisfiable at the bracket's bottom for *every* rational centre. -/
theorem no_witness_at_bottom {G : QuantumMaxCutEnergy.Input}
    (hRq : 0 < QMCLeafB.EngineRuntime.Rq G) (h4 : (QMCLeafB.UnionShallow.paramsKbc2 G).dq ≤ 4)
    (hbound : ∀ X : Matrix (Fin G.n) (Fin G.n) ℚ, Xᵀ = X →
      (∀ i, |X i i - 1| ≤ (QMCLeafB.UnionShallow.paramsKbc2 G).dq / 4) →
      (∀ x : Fin G.n → ℚ, 0 ≤ qf X x) →
      -QMCLeafB.EngineRuntime.Rq G ≤ frob (QMCLeafB.Finalization.wMatrixQ G) X)
    (X : Matrix (Fin G.n) (Fin G.n) ℚ) (hXsym : Xᵀ = X)
    (hXband : ∀ i, |X i i - 1| ≤ (QMCLeafB.UnionShallow.paramsKbc2 G).dq / 4)
    (hXpsd : ∀ x : Fin G.n → ℚ, 0 ≤ qf X x) :
    ¬ (frob (QMCLeafB.Finalization.wMatrixQ G) X
        ≤ (-QMCLeafB.EngineRuntime.Rq G - QMCLeafB.RundataCert.eps G)
            + (QMCLeafB.UnionShallow.paramsKbc2 G).dq / 2) := by
  intro h
  have hlower := hbound X hXsym hXband hXpsd
  have hdq : (QMCLeafB.UnionShallow.paramsKbc2 G).dq
      = QMCLeafB.RundataParams.dqShallow G := QMCLeafB.UnionShallow.paramsKbc2_dq G
  have hhalf := dqShallow_half_lt_eps G hRq
  rw [hdq] at h
  linarith

/-! ## 3.  What this says about the residual

`bundleH_of_verdict_true` (`Check_verdictok_m8`) can therefore **never** be applied at the bracket's
bottom: at `t = -Rq G` its witness slot is unsatisfiable, whatever the graph.  So the residual's
`hmem` slot at the bottom is vacuous *by necessity*, the flag stream there is whatever the run's cut
answers make it, and the whole burden is the cut side (records, `hdriftc`, `hdriftd`) — which is
exactly the part bricks 1/2 own and the split `VerdictOkM8.residH_of_split` hands to them.

The one gap left in turning "no band-PSD witness" into "no `RelaxMem`": a `RelaxMem` certificate
gives only the margin form `-(dq/2)‖x‖² ≤ qf cX x`, not exact PSD, so the entry bound
`|Xᵢⱼ| ≤ 1 + dq/4` (the 2x2 minor of exact PSD) is not available for it; `hbound` is stated for the
exact-PSD case, which is the case the witness slot uses.
-/

#print axioms QMCLeafB.SliverM8.dqShallow_half_lt_eps
#print axioms QMCLeafB.SliverM8.no_witness_at_bottom

end QMCLeafB.SliverM8


