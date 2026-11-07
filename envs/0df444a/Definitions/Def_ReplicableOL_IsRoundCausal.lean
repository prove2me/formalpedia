-- Prove2me | Definitions.Def_ReplicableOL_IsRoundCausal
-- name    : ReplicableOL_IsRoundCausal
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T05:46:17.06172+00:00
-- url     : https://prove2.me/theorems/96bd70ad-f39a-4af5-99d4-6243123fca6b
-- title:
--   Within-epoch causality
-- statement:
--   An epoch rule is **round-causal** if the action at position $i$ of the epoch reads only the bits at the earlier positions. Theorem 2 does not need this, but the fourth-moment bound for the noise term $N$ does, and without it the main theorem is false (Section 4.3).
--
--   **Formalization Note** The `i`-th action of the epoch string depends on the block only through its entries before `i`. Every learner's rule has this property.
-- source:
--   Lu, Replicable Online Learners Must Gamble: The Typical-Case Price of Replicability, STOC 2027 submission (held version, sha256 71ae0088…bbc2aa), Sec. 2.1, p.7 (H3)

import Mathlib
import Definitions.Def_ReplicableOL_EpochRule

namespace ReplicableOL

/-- **Within-epoch causality.** Lu, *Replicable Online Learners Must Gamble: The Typical-Case Price of Replicability*, STOC 2027 submission (held version), Sec. 2.1, p.7 (H3). (H3): "at reads only S_{<t}".

**Formalization Note.** The `i`-th action of the epoch string depends on the block only through its entries before `i`. Every learner's rule has this property. -/
def IsRoundCausal {k L : ℕ} (Φ : EpochRule k L) : Prop :=
  ∀ (j : Fin k) (h : Fin j → Block L) (s s' : Block L) (i : Fin L),
    (∀ i' : Fin L, i' < i → s i' = s' i') → Φ j h s i = Φ j h s' i

end ReplicableOL


