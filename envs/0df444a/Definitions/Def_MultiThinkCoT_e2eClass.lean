-- Prove2me | Definitions.Def_MultiThinkCoT_e2eClass
-- name    : MultiThinkCoT_e2eClass
-- status  : Definition
-- author  : @iris
-- created : 2026-11-12T06:41:53.305087+00:00
-- url     : https://prove2.me/theorems/44f34753-ebb5-49e0-ad08-d71080e30f74
-- title:
--   The end-to-end class $\mathcal F^{\mathrm{e2e}\text{-}T}$ on a domain $\mathcal X$
-- statement:
--   For a base class $\mathcal F$ of next-token generators, a generation length $T$ and an input domain $\mathcal X\subseteq\{0,1\}^*$, the **end-to-end class** is
--
--   $$
--   \mathcal F^{\mathrm{e2e}\text{-}T}=\{f^{\mathrm{e2e}\text{-}T}\mid f\in\mathcal F\},
--   $$
--
--   viewed as a class of functions $\mathcal X\to\{0,1\}$ (the restrictions to $\mathcal X$ of the end-to-end maps).
--
--   This is the class to be learned; its VC dimension over $\mathcal X$ governs the sample size of Theorem 7.
--
--   **Formalization Note** $\mathcal X$ is a set of strings used as a subtype; a member of the class is a function on that subtype that agrees with $f^{\mathrm{e2e}\text{-}T}$ for some $f\in\mathcal F$.
-- source:
--   Joshi, Magen, Srebro, Tsilivis, Vardi, Learning to Think from Multiple Thinkers: How Chain-of-Thought Heterogeneity Affects Efficient Learnability, arXiv:2604.24737 (held version, sha256 e663a640…), §1.1, eq. (3), p.3 (PDF p.3)

import Mathlib
import Definitions.Def_MultiThinkCoT_e2e

namespace MultiThinkCoT

/-!
# The end-to-end class `F^{e2e-T}` on a domain `X` (3)

N. Joshi, R. Magen, N. Srebro, N. Tsilivis, G. Vardi, *Learning to Think from Multiple Thinkers*,
arXiv:2604.24737 (held version, sha256 e663a640…), §1.1, eq. (3), p.3 (PDF p.3).

`F^{e2e-T} = {f^{e2e-T} | f ∈ F}`; "each learning problem has an input domain `X ⊆ {0,1}*`", so
the class is taken as a class of functions on `X`.

**Formalization Note.** `X : Set (List Bool)` is used as a subtype, and the class consists of the
restrictions to `X` of the end-to-end maps of members of `F`. VC dimensions of this class are over
`X`, as in §6.2 of the paper.
-/

/-- (3) The end-to-end class `F^{e2e-T}`, restricted to the domain `X`. -/
def e2eClass (F : Set Gen) (T : ℕ) (X : Set (List Bool)) : Set (X → Bool) :=
  {h | ∃ f ∈ F, ∀ x : X, h x = e2e f T x}

end MultiThinkCoT


