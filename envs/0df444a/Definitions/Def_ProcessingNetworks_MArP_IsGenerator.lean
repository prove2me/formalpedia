-- Prove2me | Definitions.Def_ProcessingNetworks_MArP_IsGenerator
-- name    : ProcessingNetworks_MArP_IsGenerator
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T13:28:24.618245+00:00
-- url     : https://prove2.me/theorems/ebc4a915-0b6f-4542-b520-5fe52f894b2a
-- title:
--   Generator matrix with positive exit rates (Definition D.1 with property (D.2))
-- statement:
--   An $\mathcal S\times\mathcal S$ matrix $\Lambda$ on a countable set is a **generator matrix** if $\Lambda_{ij}\ge 0$ for $i\ne j$, each row is summable, and
--   $$
--   \Lambda_{ii}=-\sum_{j\ne i}\Lambda_{ij},
--   $$
--   and moreover $\lambda(i)=-\Lambda_{ii}>0$ for all $i$. This last property, (D.2), says that the chain has no absorbing state; the book assumes it throughout Appendices D and E whenever it refers to a generator matrix.
--
--   **Formalization Note** Summability is a separate field because a real `tsum` of a non-summable family is $0$. Property (D.2) excludes a one-point state space.
-- source:
--   Dai & Harrison, Processing Networks (pre-publication draft 2020-4-2, spnbook.org), Definition D.1, eq. (D.1), p.287 (PDF p.303); eq. (D.2), p.288 (PDF p.304)

import Mathlib

namespace ProcessingNetworks.MArP

/-- `Λ` is a generator matrix on the countable space `S` (Dai & Harrison, Processing Networks,
pre-publication draft 2020-4-2, Definition D.1, eq. (D.1), p.287, PDF p.303): `Λ_ij ≥ 0` for
`i ≠ j`, and `Λ_ii = -∑_{j ≠ i} Λ_ij`, with property (D.2), `λ(i) = -Λ_ii > 0` for all `i` (p.288,
PDF p.304), which the book assumes "throughout the remainder of this appendix, and throughout
Appendix E and the body of the book as well, whenever reference is made to a generator matrix".

**Formalization Note.** Summability of each row is a separate field, as the book's sentence after
(D.1) says, because `tsum` of a non-summable family is `0`. Because of (D.2), a generator on a
one-point space does not exist. -/
structure IsGenerator {S : Type*} (Λ : S → S → ℝ) : Prop where
  offDiag_nonneg : ∀ i j, i ≠ j → 0 ≤ Λ i j
  summable_offDiag : ∀ i, Summable (fun j : {j // j ≠ i} => Λ i j)
  diag_eq : ∀ i, Λ i i = -∑' j : {j // j ≠ i}, Λ i j
  exit_pos : ∀ i, 0 < -Λ i i

end ProcessingNetworks.MArP


