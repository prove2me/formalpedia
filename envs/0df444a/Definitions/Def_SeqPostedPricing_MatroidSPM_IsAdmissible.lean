-- Prove2me | Definitions.Def_SeqPostedPricing_MatroidSPM_IsAdmissible
-- name    : SeqPostedPricing_MatroidSPM_IsAdmissible
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-30T03:33:21.649227+00:00
-- url     : https://prove2.me/theorems/9e20d373-6dc8-4a83-91ff-2b3ee0a3c358
-- title:
--   Admissible mechanism: feasible, truthful, individually rational
-- statement:
--   Let $\mathcal J\subseteq 2^{[n]}$ be the feasibility constraint. A mechanism $M$ is **admissible** for $\mathcal J$ and independent values $v_i\sim\mu_i$ if
--
--   1. every allocation is feasible: $M(\mathbf v)\in\mathcal J$ for every $\mathbf v$;
--   2. $M$ is truthful;
--   3. $M$ is individually rational;
--   4. each event $\{\mathbf v: i\in M(\mathbf v)\}$ is measurable;
--   5. each payment $\mathbf v\mapsto\pi_i(\mathbf v)$ is integrable.
--
--   These are the mechanisms over which revenue is optimized.
--
--   **Formalization Note** Clauses 4 and 5 only make $q_i^M$ and $\mathcal R^M$ well defined; they exclude no mechanism of the paper.
-- source:
--   Chawla, Hartline, Malec, Sivan, Multi-parameter Mechanism Design and Sequential Posted Pricing, arXiv:0907.2435v2, §2.1, p. 4; Lemma 3, p. 5

import Mathlib
import Definitions.Def_SeqPostedPricing_MatroidSPM_IsTruthful
import Definitions.Def_SeqPostedPricing_MatroidSPM_IsIndividuallyRational
open MeasureTheory

namespace SeqPostedPricing.MatroidSPM

/-- **Admissible mechanism for the feasibility constraint `J`: feasible, truthful, individually
rational, with measurable allocation events and integrable payments.**
Chawla, Hartline, Malec, Sivan, *Multi-parameter Mechanism Design and Sequential Posted Pricing*, arXiv:0907.2435v2, §2.1, p. 4 (PDF p. 6): "A mechanism M for this problem is a function that maps a vector of
values v to an allocation M(v) ∈ J"; Lemma 3, p. 5 (PDF p. 7): "individually rational and
truthful".

`IsAdmissible Feas μ M` holds when every allocation is feasible (`Feas (M.alloc v)`), `M` is
truthful and individually rational, each event `{i ∈ M(v)}` is measurable and each payment
`v ↦ π_i(v)` is integrable under the product law.

**Formalization Note.** The set system `J` is the predicate `Feas` on `Finset (Fin n)`. The
measurability and integrability clauses only make `q_i^M` and `R^M` meaningful (a Bochner
integral of a non-integrable function is `0` in Lean); they exclude no mechanism the paper
considers. -/
def IsAdmissible {n : ℕ} (Feas : Finset (Fin n) → Prop) (μ : Fin n → Measure ℝ)
    [∀ i, SigmaFinite (μ i)] (M : Mechanism n) : Prop :=
  (∀ v, Feas (M.alloc v)) ∧ IsTruthful M ∧ IsIndividuallyRational M ∧
    (∀ i, MeasurableSet {v : Fin n → ℝ | i ∈ M.alloc v}) ∧
    (∀ i, Integrable (fun v => M.pay v i) (Measure.pi μ))

end SeqPostedPricing.MatroidSPM


