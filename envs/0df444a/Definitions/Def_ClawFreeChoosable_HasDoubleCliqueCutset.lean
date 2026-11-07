-- Prove2me | Definitions.Def_ClawFreeChoosable_HasDoubleCliqueCutset
-- name    : ClawFreeChoosable_HasDoubleCliqueCutset
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T22:44:43.184816+00:00
-- url     : https://prove2.me/theorems/45f7e91f-c7be-4ef4-b273-c658dec2df06
-- title:
--   Double clique cutset
-- statement:
--   A **double clique cutset** of a graph $G$ is a quadruple $(V_1, C_1, C_2, V_2)$ of pairwise disjoint vertex sets covering $V(G)$ such that
--
--   1. $V_1 \ne \emptyset$ and $V_2 \ne \emptyset$;
--   2. $D = C_1 \cup C_2$ is a clique ($C_1$ or $C_2$ may be empty);
--   3. $V_1$ is anticomplete to $C_2 \cup V_2$, and $V_2$ is anticomplete to $C_1$.
--
--   Then $D$ is a clique cutset and $G$ is the **double clique-sum** of $G[V_1 \cup D]$ and $G[V_2 \cup D]$. A graph **admits a double clique cutset** if such a quadruple exists.
--
--   Double clique sums preserve the precolouring-extension property (Lemma 12.1).
-- source:
--   Mishra, Narayanan N, Shankar, Claw-free perfect graphs are chromatic-choosable, arXiv:2611.01068v1, §12.1 p.32, "double clique cutset", "double clique-sum"

import Mathlib
import Definitions.Def_ClawFreeChoosable_IsAnticomplete

set_option autoImplicit false

namespace ClawFreeChoosable

/-- **Double clique cutset** (arXiv:2611.01068v1, §12.1 p.32): a clique cutset `D = C₁ ∪ C₂`
(disjoint union) for which `V(G) = V₁ ∪ C₁ ∪ C₂ ∪ V₂` (pairwise disjoint), `V₁, V₂ ≠ ∅`, `V₁` is
anticomplete to `C₂ ∪ V₂` and `V₂` is anticomplete to `C₁`. Then `G` is the double clique-sum
of `G[V₁ ∪ D]` and `G[V₂ ∪ D]`. `C₁` or `C₂` may be empty.

**Formalization Note.** The data is the ordered quadruple `(V₁, C₁, C₂, V₂)`. That `D` is a
clique is required; that `D` is a cutset follows from the other conditions (the sides `V₁`,
`V₂` are nonempty and anticomplete). -/
def IsDoubleCliqueCutset {V : Type} (G : SimpleGraph V) (V₁ C₁ C₂ V₂ : Set V) : Prop :=
  Disjoint V₁ C₁ ∧ Disjoint V₁ C₂ ∧ Disjoint V₁ V₂ ∧ Disjoint C₁ C₂ ∧ Disjoint C₁ V₂ ∧
    Disjoint C₂ V₂ ∧ V₁ ∪ C₁ ∪ C₂ ∪ V₂ = Set.univ ∧ V₁.Nonempty ∧ V₂.Nonempty ∧
    G.IsClique (C₁ ∪ C₂) ∧ IsAnticomplete G V₁ (C₂ ∪ V₂) ∧ IsAnticomplete G V₂ C₁

/-- `G` **admits a double clique cutset** (arXiv:2611.01068v1, §12.1 p.32, Theorem 12.2). -/
def HasDoubleCliqueCutset {V : Type} (G : SimpleGraph V) : Prop :=
  ∃ V₁ C₁ C₂ V₂ : Set V, IsDoubleCliqueCutset G V₁ C₁ C₂ V₂

end ClawFreeChoosable


