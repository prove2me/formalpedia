-- Prove2me | Definitions.Def_MonoTestDAG_Reach
-- name    : MonoTestDAG_Reach
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T21:07:26.938306+00:00
-- url     : https://prove2.me/theorems/58261981-4d8d-4f94-9491-b125befcad1a
-- title:
--   Reflexive reachability $u \leadsto v$ and acyclicity of a directed graph
-- statement:
--   Let $G=(V,E)$ be a directed graph, with $E$ a binary relation on $V$. We write $u\leadsto v$ if $u=v$ or there is a directed path of positive length from $u$ to $v$. Thus $\leadsto$ is reflexive reachability, the reflexive–transitive closure of $E$. The graph is a **DAG** if no vertex reaches itself by a directed path of positive length.
--
--   Every notion of this mission (monotonicity, the transitive closure, the transitive reduction) depends on $G$ only through $\leadsto$.
--
--   **Formalization Note.** A graph is a relation `E : V → V → Prop`. The module also defines `IsDAG`.
-- source:
--   Yoshida, Testing Monotonicity of Real-Valued Functions on DAGs, arXiv:2602.15341 (sha256 454609db…), §2.1, p.10 and §1.1, p.1

import Mathlib

namespace MonoTestDAG

/-- Reflexive reachability `u ⇝ v` in a directed graph `G = (V, E)`: either `u = v` or there is a
directed path of positive length from `u` to `v`.

Yoshida, *Testing Monotonicity of Real-Valued Functions on DAGs*, arXiv:2602.15341
(sha256 454609db…), §2.1, p.10.

**Formalization Note.** The graph is a relation `E : V → V → Prop` (`E u v` means `(u, v)` is a
directed edge); `⇝` is its reflexive–transitive closure `Relation.ReflTransGen E`. -/
def Reach {V : Type} (E : V → V → Prop) : V → V → Prop :=
  Relation.ReflTransGen E

/-- The directed graph `(V, E)` is acyclic (a DAG): no vertex reaches itself by a directed path of
positive length.

Yoshida, arXiv:2602.15341 (sha256 454609db…), §1.1, p.1 and §2.1, p.10. -/
def IsDAG {V : Type} (E : V → V → Prop) : Prop :=
  ∀ v, ¬ Relation.TransGen E v v

end MonoTestDAG


