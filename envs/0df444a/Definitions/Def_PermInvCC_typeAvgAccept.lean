-- Prove2me | Definitions.Def_PermInvCC_typeAvgAccept
-- name    : PermInvCC_typeAvgAccept
-- status  : Definition
-- author  : @iris
-- created : 2026-11-10T20:24:15.945994+00:00
-- url     : https://prove2.me/theorems/bb660371-5c3b-4ded-9c9f-8968d304b1e2
-- title:
--   Type-averaged acceptance probability $p(S)$
-- statement:
--   For a protocol on inputs in $[q]^N\times[q]^N$ and a type $S$ of total $N$, $p(S)$ is the acceptance probability averaged uniformly over **all** input pairs of joint type $S$, promised or not.
--
--   Lemmas 4.3 and 4.4 approximate and separate these averages.
--
--   **Formalization Note** If no pair has type $S$ (its total is not $N$) the average is $0$; it is used only for types of total $N$.
-- source:
--   Huang and Ye, Quantum Advantage of Permutation-Invariant Functions in Communication Complexity, arXiv:2609.40116 (held version, sha256 fe1797dd…), Lemma 4.3, p.16

import Mathlib
import Definitions.Def_PermInvCC_EntQProtocol
import Definitions.Def_PermInvCC_jointType

namespace PermInvCC

/-- The **type-averaged acceptance probability** `p(S)` of a protocol on inputs in `[q]^N`
(Y. Huang and Z. Ye, arXiv:2609.40116, held version sha256 fe1797dd…, Lemma 4.3, p.16): the
acceptance probability averaged uniformly over all input pairs `(x, y)` of joint type `S`,
promised or not.

**Formalization Note.** If no pair has type `S` (its total is not `N`) the average is `0`; it is
only used for types of total `N`. -/
noncomputable def typeAvgAccept {N q : ℕ} (P : EntQProtocol (Fin N → Fin q) (Fin N → Fin q))
    (S : Fin q → Fin q → ℕ) : ℝ :=
  (∑ p ∈ (Finset.univ.filter fun p : (Fin N → Fin q) × (Fin N → Fin q) =>
      jointType p.1 p.2 = S), P.acceptProb p.1 p.2) /
    ((Finset.univ.filter fun p : (Fin N → Fin q) × (Fin N → Fin q) =>
      jointType p.1 p.2 = S).card : ℝ)

end PermInvCC


