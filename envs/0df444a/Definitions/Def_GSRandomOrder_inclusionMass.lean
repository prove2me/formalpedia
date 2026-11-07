-- Prove2me | Definitions.Def_GSRandomOrder_inclusionMass
-- name    : GSRandomOrder_inclusionMass
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T17:02:04.849246+00:00
-- url     : https://prove2.me/theorems/073f3460-1033-4846-9216-22eaccfe7f25
-- title:
--   Inclusion mass $m^u_{Q,A}(t)=t^{|Q|}\,P[A\subseteq R]$, eq. (25)
-- statement:
--   For a valuation $u$, $Q\subseteq N$, $A\subseteq Q$ and $t\in[1/e,1]$,
--   $$
--   m^u_{Q,A}(t)=t^{|Q|}\,P[A\subseteq R],\qquad R\sim\mu^u_{Q,t}.
--   $$
--   The factor $t^{|Q|}$ is the volume of $[0,t]^Q$, so $m^u_{Q,A}(t)$ is the integral, rather than the average, over timestamps of the probability that $A\subseteq R$. These quantities satisfy the inclusion recursion that drives distribution matching.
--
--   **Formalization Note** $P[A\subseteq R]$ is the sum of $\mu^u_{Q,t}(C)$ over $A\subseteq C\subseteq Q$.
-- source:
--   Paes Leme, Pál, Patel, Gross Substitutes Welfare in Random Order, STOC 2027 submission (manuscript sha256 69787f50…), §B.2, p.25, eq. (25)

import Mathlib
import Definitions.Def_GSRandomOrder_survivalLaw

set_option autoImplicit false

namespace GSRandomOrder

/-- **Inclusion mass** (Paes Leme, Pál, Patel, *Gross Substitutes Welfare in Random Order*, STOC
2027 submission, manuscript sha256 69787f50…, §B.2, p.25, eq. (25)): for `Q ⊆ N`, `A ⊆ Q` and
`t ∈ [1/e, 1]`, `m^u_{Q,A}(t) = t^{|Q|} P[A ⊆ R]`, where `R` has law `μ^u_{Q,t}`.

**Formalization Note.** `P[A ⊆ R]` is the sum of `μ^u_{Q,t}(C)` over the sets `C ⊆ Q` with
`A ⊆ C`; `R ⊆ Q` always, so this is the event `A ⊆ R`. -/
noncomputable def inclusionMass {n : ℕ} (u : Finset (Fin n) → WithBot ℝ) (Q A : Finset (Fin n))
    (t : ℝ) : ℝ :=
  t ^ Q.card * ∑ C ∈ Q.powerset.filter (fun C => A ⊆ C), survivalLaw u Q t C

end GSRandomOrder


