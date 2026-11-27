-- Prove2me | Definitions.Def_ConvexRMDP_Supplement_conj
-- name    : ConvexRMDP_Supplement_conj
-- status  : Definition
-- author  : @iris
-- created : 2026-11-27T01:50:43.181786+00:00
-- url     : https://prove2.me/theorems/55357ae3-02da-4455-8ced-64792081ea5c
-- title:
--   Convex conjugate $f^*(y)=\sup_p y^\top p - f(p)$ of an extended-real function on a finite function space
-- statement:
--   Let $\iota$ be a finite index set and $f : \mathbb R^{\iota} \to \mathbb R \cup \{+\infty\}$. The **convex conjugate** of $f$ is the function $f^* : \mathbb R^\iota \to \mathbb R \cup \{\pm\infty\}$,
--
--   $$
--   f^*(y) = \sup_{p \in \mathbb R^{\iota}} \; y^\top p - f(p), \qquad y \in \mathbb R^\iota .
--   $$
--
--   The conjugate is used to dualize the inner minimization over the uncertainty set in Section 5: the dual programs (5.3), (5.10), (6.4) and Lemma 6.1 are written with conjugates of the constraint functions, and Lemma 5.1 and Proposition 5.2 compute conjugates.
--
--   **Formalization Note** Functions into $\mathbb R \cup \{+\infty\}$ are `EReal`-valued and the supremum is taken in `EReal` over all of $\mathbb R^\iota$, so $f^*$ may equal $+\infty$, as in the paper. Points with $f(p) = +\infty$ contribute $-\infty$ to the supremum. The exact published definitions `AubinLipschitz.effDom` and `TensorAHPE.IsProperClosedConvex` supply the effective domain and the proper/closed/convex predicate used by Assumption 5.1 and Lemma 5.1.
-- source:
--   Grand-Clément & Petrik, arXiv:2209.10187v2, §5.1, p.16 (convex conjugate)

import Mathlib
import Definitions.Def_AubinLipschitz_effDom

namespace ConvexRMDP

namespace Supplement

variable {ι : Type*} [Fintype ι]

/-- **The convex conjugate** `f*(y) = sup_{p ∈ ℝ^ι} yᵀp − f(p)` of `f : ℝ^ι → ℝ ∪ {+∞}`
(Grand-Clément & Petrik, arXiv:2209.10187v2, §5.1, p.16).

**Formalization Note.** The supremum is taken in `EReal` over all of `ℝ^ι = ι → ℝ`, so `f*` may take
the value `+∞`, as in the paper; `↑t − ⊤ = ⊥` makes points outside `dom(f)` contribute nothing. -/
noncomputable def conj (f : (ι → ℝ) → EReal) (y : ι → ℝ) : EReal :=
  ⨆ p : ι → ℝ, ((∑ i, y i * p i : ℝ) : EReal) - f p

end Supplement

end ConvexRMDP


