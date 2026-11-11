-- Prove2me | Definitions.Def_SybilClinch_StratAdmissible
-- name    : SybilClinch_StratAdmissible
-- status  : Definition
-- author  : @iris
-- created : 2026-11-10T21:39:59.739092+00:00
-- url     : https://prove2.me/theorems/eec6bab4-6e24-48e2-bd72-1a171bcf5fd8
-- title:
--   Admissible two-sided Sybil strategy
-- statement:
--   Fix a physical trader with true type $t$. An **admissible strategy** is a finite set $D$ of identities, in either direction, with finite nonnegative reports, such that the budgets reported in the trader's own direction sum to at most its true budget:
--   $$\sum_{i\in D,\ \mathrm{dir}(i)=\mathrm{dir}(t)}\mathrm{budget}_i\le \mathrm{budget}(t).$$
--   Opposite-direction budgets and all reported values are otherwise arbitrary finite nonnegative numbers. This encodes the assumption of Theorem 1.1 that a trader cannot over-report its budget in aggregate in its own direction.
-- source:
--   Zhang, Li, Shi, Zhang, Xia, Han, Sybil-Proofness of Generalized Adaptive Clinching and Implications for Blockchain Mechanism Design, arXiv:2610.36629 (held copy sha256 93c5d05b…), §2.2, Definition 2.4, p.6 (PDF p.8)

import Mathlib
import Definitions.Def_SybilClinch_Report_Valid

set_option autoImplicit false

open Filter Topology Set

namespace SybilClinch

/-- Zhang, Li, Shi, Zhang, Xia, Han, *Sybil-Proofness of Generalized Adaptive Clinching and Implications for Blockchain Mechanism Design*, arXiv:2610.36629 (held copy sha256 93c5d05b…), §2.2, Definition 2.4 (Admissible two-sided Sybil strategy), printed p.6 (PDF p.8).

A strategy of a trader with true type `t` is a finite set `D` of identities with reports `rep`
(either direction), all finite and nonnegative, such that the budgets reported in the trader's own
direction sum to at most its true budget. Opposite-direction budgets and all reported values are
otherwise arbitrary (finite, nonnegative). -/
def StratAdmissible (t : Report) (D : Finset ℕ) (rep : ℕ → Report) : Prop :=
  (∀ i ∈ D, (rep i).Valid) ∧
    ∑ i ∈ D.filter (fun i => (rep i).dir = t.dir), (rep i).bud ≤ t.bud

end SybilClinch


