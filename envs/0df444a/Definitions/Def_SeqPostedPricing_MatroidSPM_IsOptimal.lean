-- Prove2me | Definitions.Def_SeqPostedPricing_MatroidSPM_IsOptimal
-- name    : SeqPostedPricing_MatroidSPM_IsOptimal
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-30T03:34:29.761827+00:00
-- url     : https://prove2.me/theorems/11c4f2f1-30e1-4f2c-874b-104d4645983e
-- title:
--   Revenue-optimal mechanism (the role of Myerson's mechanism)
-- statement:
--   A mechanism $M$ is **optimal** for $\mathcal J$ and $\mu_1,\dots,\mu_n$ if it is admissible and
--
--   $$
--   \mathcal R^M\ge\mathcal R^A\quad\text{for every admissible mechanism }A .
--   $$
--
--   By the paper's Theorem 19 ($\mathcal R^{\mathcal M}\ge\mathcal R^{A}$ for every truthful mechanism $A$), Myerson's mechanism is optimal, so every statement about all optimal mechanisms applies to Myerson's mechanism.
--
--   **Formalization Note** Myerson's mechanism is not constructed, which would fix one tie-breaking rule; it is characterized by optimality.
-- source:
--   Chawla, Hartline, Malec, Sivan, Multi-parameter Mechanism Design and Sequential Posted Pricing, arXiv:0907.2435v2, App. A, Theorem 19, p. 12

import Mathlib
import Definitions.Def_SeqPostedPricing_MatroidSPM_IsAdmissible
import Definitions.Def_SeqPostedPricing_MatroidSPM_revenue
open MeasureTheory

namespace SeqPostedPricing.MatroidSPM

/-- **Revenue-optimal mechanism (the role of Myerson's mechanism).**
Chawla, Hartline, Malec, Sivan, *Multi-parameter Mechanism Design and Sequential Posted Pricing*, arXiv:0907.2435v2, App. A, Theorem 19, p. 12 (PDF p. 14): "R^M ≥ R^A for every truthful mechanism A."

`IsOptimal Feas μ M`: `M` is admissible and its expected revenue is at least that of every
admissible mechanism.

**Formalization Note.** Myerson's mechanism is deterministic, truthful, individually rational,
feasible, with integrable payments, and is optimal by Theorem 19; statements about every optimal
mechanism therefore contain the paper's statements about Myerson's mechanism. Myerson's mechanism
is not constructed (that would fix one tie-breaking rule). -/
def IsOptimal {n : ℕ} (Feas : Finset (Fin n) → Prop) (μ : Fin n → Measure ℝ)
    [∀ i, SigmaFinite (μ i)] (M : Mechanism n) : Prop :=
  IsAdmissible Feas μ M ∧ ∀ A : Mechanism n, IsAdmissible Feas μ A → revenue μ A ≤ revenue μ M

end SeqPostedPricing.MatroidSPM


