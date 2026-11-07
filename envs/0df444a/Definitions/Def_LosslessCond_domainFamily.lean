-- Prove2me | Definitions.Def_LosslessCond_domainFamily
-- name    : LosslessCond_domainFamily
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T11:35:08.960171+00:00
-- url     : https://prove2.me/theorems/5beb2e7c-e5ba-41ed-ba07-7dcf302b356e
-- title:
--   The family $C_s$ of depth-$s$ protocol domains
-- statement:
--   For a fixed Boolean matrix $M:X\times Y\to\{0,1\}$ and a depth $s\ge 0$, let
--   $$
--   C_s=\{\,G_P(U):\ U\subseteq X,\ P \text{ a partial protocol of depth } s\,\},
--   $$
--   the family of all protocol domains of depth $s$, letting both the row set $U$ and Alice's maps vary. Its members are subsets of the original column set.
--
--   Lemma 4.3 bounds $|C_s|$ independently of $|X|$ and $|Y|$, which drives the hitting-set and cover arguments of §5.
--
--   **Formalization Note** $C_s$ is a set of subsets of $Y$. For finite $Y$ it is finite, so its cardinality (`Set.ncard`) is the true one.
-- source:
--   Mackenzie, Lossless Hardness Condensation in Deterministic Communication Complexity, arXiv:2609.28691 (held version, sha256 ce75e6d41cda6fdcdc55c619ab80e2b628e40845768cc3021cc0a0bfe7743fcf), §4.3, p.12 (PDF p.13)

import Mathlib
import Definitions.Def_LosslessCond_domain

namespace LosslessCond

/-- The family `C_s` of **all protocol domains of depth `s`** (Mackenzie, arXiv:2609.28691, held
version sha256 ce75e6d4…, §4.3, p.12): the sets `G_P(U)` obtained from depth-`s` partial protocols
`P`, letting both the row set `U ⊆ X` and Alice's maps vary, for the fixed matrix `M`.

**Formalization Note** `C_s` is a `Set (Set Y)`. For finite `Y` it is finite, so `Set.ncard` of it
is its true cardinality and never the junk value `0` of an infinite set. -/
def domainFamily {X Y : Type} (M : X → Y → Bool) (s : ℕ) : Set (Set Y) :=
  {G | ∃ (U : Set X) (P : PartialProtocol X s), G = domain M P U}

end LosslessCond


