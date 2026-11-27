-- Prove2me | Definitions.Def_FreeOrderEPTAS_Supplement_pandoraOPT
-- name    : FreeOrderEPTAS_Supplement_pandoraOPT
-- status  : Definition
-- author  : @iris
-- created : 2026-11-26T22:36:41.732772+00:00
-- url     : https://prove2.me/theorems/1dd26198-aacf-524d-865c-b0ee3b155e2a
-- title:
--   Solutions, expected utility and the optimum $\mathrm{OPT}(X,c)$
-- statement:
--   A solution of Pandora's Box with Commitment is a probing permutation $\sigma$ together with a stopping rule $\tau$, or the empty solution, which probes nothing. The solution $(\sigma,\tau)$ probes $X_{\sigma(1)},X_{\sigma(2)},\dots$ until $\tau$ stops and earns
--   $$X_{\sigma(\tau)}-\sum_{t\le\tau}c_{\sigma(t)}.$$
--   Its expected utility is the expectation of this quantity, and
--   $$\mathrm{OPT}(X,c)=\sup_{\text{solutions}}\ \mathbb E\Big[X_{\sigma(\tau)}-\sum_{t\le\tau}c_{\sigma(t)}\Big].$$
--
--   The empty solution earns $0$. If $\tau$ never stops, nothing is selected and all $n$ costs are paid.
--
--   **Formalization Note** `PBCPolicy n` is `Option (Equiv.Perm (Fin n) × StoppingRule n)`, with the base stopping rules (measurable decisions on the values seen so far) and the base convention that a rule that never stops earns $0$. The real supremum is over a nonempty set bounded above by $\sum_i\mathbb E|X_i|$.
-- source:
--   Segev & Singla, Efficient Approximation Schemes for Stochastic Probing and Selection-Stopping Problems, arXiv:2007.13121v3, §6.1, p.30 (problem) and p.31 (OPT(X, c))

import Mathlib
import Definitions.Def_FreeOrderEPTAS_Supplement_PandoraInstance
import Definitions.Def_FreeOrderEPTAS_StoppingRule

open MeasureTheory

namespace FreeOrderEPTAS.Supplement

variable {n : ℕ}

/-- A solution of Pandora's Box with Commitment (arXiv:2007.13121v3, p.30, "a probing permutation
σ and a stopping rule τ"): either `none`, which probes no box and earns `0`, or a probing
permutation `σ` (`σ t` is the box probed at time `t`, 0-based) with a stopping rule `τ`, which
selects the value it stops at. -/
abbrev PBCPolicy (n : ℕ) : Type := Option (Equiv.Perm (Fin n) × StoppingRule n)

/-- The probing costs paid by `(σ, τ)` on the outcome `x`: `∑_{t ≤ τ} c_{σ(t)}`, and all `n`
costs if `τ` never stops. -/
def costPaid (c : Fin n → ℝ) (σ : Equiv.Perm (Fin n)) (τ : StoppingRule n) (x : Fin n → ℝ) : ℝ :=
  match stopTime τ σ x with
  | some t => ∑ s ∈ Finset.Iic t, c (σ s)
  | none => ∑ s, c s

/-- The utility `X_{σ(τ)} − ∑_{t ≤ τ} c_{σ(t)}` of a solution on the outcome `x` (p.30). If `τ`
never stops, nothing is selected (the base `reward` is `0`) and every cost is paid; the empty
solution earns `0`. -/
def pandoraUtility (c : Fin n → ℝ) : PBCPolicy n → (Fin n → ℝ) → ℝ
  | none, _ => 0
  | some (σ, τ), x => reward τ σ x - costPaid c σ τ x

/-- The expected utility `E[X_{σ(τ)} − ∑_{t ≤ τ} c_{σ(t)}]` of a solution, the values being
independent with laws `μ_i`. -/
noncomputable def pandoraValue (P : PandoraInstance n) (π : PBCPolicy n) : ℝ :=
  ∫ x, pandoraUtility P.c π x ∂(Measure.pi P.X.μ)

/-- `OPT(X, c)` (arXiv:2007.13121v3, §6.1, pp.30–31): "the expected value of an optimal solution to
Pandora's Box with Commitment", the supremum of the expected utility over all solutions.

**Formalization Note.** The solutions are those of p.30 (a permutation and a stopping rule) and the
empty solution, which probes nothing; the proofs of Claims 6.2–6.3 skip boxes the optimal policy
does not probe, and skipping all of them is the empty solution. If the rule never stops, every cost
is paid and nothing is selected. The real supremum is over a nonempty set bounded above by
`∑ i, E|X_i|`, since every utility is at most `∑ i, |x i|`. -/
noncomputable def pandoraOPT (P : PandoraInstance n) : ℝ :=
  ⨆ π : PBCPolicy n, pandoraValue P π

end FreeOrderEPTAS.Supplement


