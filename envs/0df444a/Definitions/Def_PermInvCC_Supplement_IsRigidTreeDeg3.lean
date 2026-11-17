-- Prove2me | Definitions.Def_PermInvCC_Supplement_IsRigidTreeDeg3
-- name    : PermInvCC_Supplement_IsRigidTreeDeg3
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T06:55:43.191979+00:00
-- url     : https://prove2.me/theorems/fa5ec8f6-0237-4ac9-8071-58aa988d7866
-- title:
--   Rigid tree of maximum degree three
-- statement:
--   A simple graph $B$ on $[v]$ is a **rigid tree of maximum degree three** if
--
--   1. $B$ is a tree on all $v$ vertices;
--   2. every vertex has degree at most $3$, and some vertex has degree exactly $3$;
--   3. $B$ is rigid: its only automorphism is the identity.
--
--   Rigidity makes the relabelling in a labelled copy $\sigma B$ unique, which is what lets Theorem 1.3(ii) store a permutation in a labelled copy of a single tree.
--
--   **Formalization Note** "Maximum degree three" is read as "largest degree equal to $3$"; rigidity says every graph isomorphism from $B$ to itself fixes every vertex.
-- source:
--   Huang and Ye, Quantum Advantage of Permutation-Invariant Functions in Communication Complexity, arXiv:2609.40116 (held version, sha256 fe1797dd…), Theorem 1.3(ii), p.3 (PDF p.6); rigidity defined p.2 (PDF p.5); §5.3, p.25 (PDF p.28)

import Mathlib

namespace PermInvCC

namespace Supplement

open Classical in
/-- `B` is a **rigid tree of maximum degree three** on `[v]` (Y. Huang and Z. Ye, *Quantum Advantage of Permutation-Invariant Functions in Communication
Complexity*, arXiv:2609.40116, held version sha256 fe1797dd…, Theorem 1.3(ii),
p.3, and §5.3, p.25): a tree on all `v` vertices whose largest vertex degree is exactly `3`, and
rigid — "A rigid graph is one whose only automorphism is the identity" (p.2).

**Formalization Note.** "Maximum degree three" is read as: every degree is at most `3` and some
vertex has degree `3`. Rigidity: every graph isomorphism `B ≃g B` fixes every vertex. -/
def IsRigidTreeDeg3 {v : ℕ} (B : SimpleGraph (Fin v)) : Prop :=
  B.IsTree ∧ (∀ u, B.degree u ≤ 3) ∧ (∃ u, B.degree u = 3) ∧ ∀ φ : B ≃g B, ∀ u, φ u = u

end Supplement

end PermInvCC


