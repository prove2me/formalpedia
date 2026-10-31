-- Prove2me | Definitions.Def_LegalAssign_legalSeq
-- name    : LegalAssign_legalSeq
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T20:20:57.05899+00:00
-- url     : https://prove2.me/theorems/fee6c87d-a2b9-4dab-9131-bdaa33159f63
-- title:
--   The operator $\mathcal L$ and the sequence $\mathcal L^i$
-- statement:
--   Let $\mathcal M=\mathcal M(G,q)$. For $\mathcal M'\subseteq\mathcal M$, the operator $\mathcal L$ returns the assignments not blocked by any assignment in $\mathcal M\setminus\mathcal I(\mathcal M')$:
--   $$\mathcal L(\mathcal M'):=\mathcal M\setminus\mathcal I\bigl(\mathcal M\setminus\mathcal I(\mathcal M')\bigr).$$
--   Its orbit from the stable assignments is $\mathcal L^0:=\mathcal S(G,<,q)$ and $\mathcal L^i:=\mathcal L(\mathcal L^{i-1})$.
--
--   The sequence is the route of the self-contained proof of the mission's goal: a set with the legal property is a fixed point of $\mathcal L$.
--
--   **Formalization Note** The source uses $\mathcal L$ for the operator, for the stable value of the sequence and for the legal set. In Lean these are `legalOp`, `legalSeq k` and a bound variable.
-- source:
--   Faenza–Zhang, arXiv:1809.08506v2, App. A, p.25 (operator 𝓛 and the sequence 𝓛^i)

import Mathlib
import Definitions.Def_LegalAssign_Instance

namespace LegalAssign

namespace Instance

variable {A B : Type*} [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B]

/-- The operator `𝓛(𝓜') := 𝓜 \ 𝓘(𝓜 \ 𝓘(𝓜'))` of arXiv:1809.08506v2, App. A, p.25: the
assignments not blocked by any assignment that `𝓜'` does not block. -/
def legalOp (G : Instance A B) (S : Set (Finset (A × B))) : Set (Finset (A × B)) :=
  G.assignments \ G.blockedBy (G.assignments \ G.blockedBy S)

/-- The sequence `𝓛^0 := 𝓢(G, <, q)`, `𝓛^i := 𝓛(𝓛^{i-1})` (arXiv:1809.08506v2, App. A, p.25).

**Formalization Note** The source writes `𝓛` for the operator, for this sequence's limit and for the
legal set; the Lean names are `legalOp`, `legalSeq k`, and a bound variable. -/
def legalSeq (G : Instance A B) : ℕ → Set (Finset (A × B))
  | 0 => G.stable
  | k + 1 => G.legalOp (G.legalSeq k)

end Instance

end LegalAssign


