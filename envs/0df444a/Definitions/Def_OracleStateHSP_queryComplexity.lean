-- Prove2me | Definitions.Def_OracleStateHSP_queryComplexity
-- name    : OracleStateHSP_queryComplexity
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T11:34:19.402842+00:00
-- url     : https://prove2.me/theorems/b85c1889-18b3-42cd-8615-a0c2d66b6527
-- title:
--   Bounded-error query complexity $Q(s, \{O_x\})$
-- statement:
--   The **bounded-error query complexity** $Q(s, \{O_x\})$ is the smallest $T$ such that some $T$-query algorithm of Definition 4.1 (forward and inverse queries, controlled access through the direct sum) evaluates $s$ with bounded error on the family $\{O_x\}$; it is $\infty$ if there is none.
--
--   **Formalization Note** The value lies in $\mathbb N \cup \{\infty\}$ (`ℕ∞`), so that "no algorithm" is $\infty$ rather than a junk $0$. The algorithm's spaces are $S = \mathbb C^a$ and $W = \mathbb C^b$ for arbitrary $a, b$; only their dimensions matter. The oracles are arbitrary matrices in the definition; theorems add unitarity as a hypothesis.
-- source:
--   Liu–Carrasco–Eisert–Bellante, The power of oracle access, arXiv:2609.35656, Definition 4.3, p.35

import Mathlib
import Definitions.Def_OracleStateHSP_EvaluatesWithBoundedError

namespace OracleStateHSP

/-- The bounded-error query complexity `Q(s, {O_x})` (Liu–Carrasco–Eisert–Bellante, *The power of oracle access*, arXiv:2609.35656, Definition 4.3, p.35): the
smallest `T` such that some `T`-query algorithm of Definition 4.1 (forward and inverse queries,
with the direct sum `S ⊕ (H_S ⊗ W)` giving controlled access) evaluates `s` with bounded error;
`⊤` if there is none.

**Formalization Note.** Values in `ℕ∞`, so that "no algorithm exists" is `⊤` rather than a junk
`0`. The spaces `S` and `W` of an algorithm are `Fin a` and `Fin b` for arbitrary `a b : ℕ`; only
their dimensions matter. The oracles `O_x` are arbitrary matrices here; the paper's unitarity is a
hypothesis of the theorems that use this quantity. -/
noncomputable def queryComplexity {X E Q : Type*} [Fintype Q] [DecidableEq Q]
    (O : X → Matrix Q Q ℂ) (s : X → E) : ℕ∞ :=
  sInf ((fun T : ℕ => (T : ℕ∞)) ''
    {T | ∃ (a b : ℕ) (A : QueryAlgorithm Q (Fin a) (Fin b) T), A.IsDef41 ∧
      ∃ (ψ₀ : EuclideanSpace ℂ (Fin a ⊕ (Q × Fin b))) (out : Fin a ⊕ (Q × Fin b) → E),
        EvaluatesWithBoundedError A ψ₀ out O s})

end OracleStateHSP


