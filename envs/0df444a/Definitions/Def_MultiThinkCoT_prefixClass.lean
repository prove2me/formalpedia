-- Prove2me | Definitions.Def_MultiThinkCoT_prefixClass
-- name    : MultiThinkCoT_prefixClass
-- status  : Definition
-- author  : @iris
-- created : 2026-11-12T06:42:01.310843+00:00
-- url     : https://prove2.me/theorems/a56c2712-3af4-4803-89c1-22abeba44f43
-- title:
--   The base class $\mathcal F$ over the prefix domain $\mathcal X\times\{0,1\}^{\le T-1}$
-- statement:
--   In Proposition 6.3 and Theorem 7, $\mathrm{VCdim}(\mathcal F)$ "is taken over the domain $\mathcal X\times\{0,1\}^{\le T-1}$": a point $(x,p)$ with $x\in\mathcal X$ and $|p|\le T-1$ is the string $[x,p]$, and a generator $f$ acts on it as
--
--   $$
--   (x,p)\mapsto f([x,p]).
--   $$
--
--   These are exactly the strings on which $f$ is evaluated while generating a CoT of length $T$ from an input in $\mathcal X$, so this class measures the complexity of the single next-token step.
--
--   **Formalization Note** $\{0,1\}^{\le T-1}$ is the set of Boolean lists of length at most $T-1$, with natural-number subtraction; at $T=0$ it is $\{[\,]\}$, a degenerate case in which every CoT is empty.
-- source:
--   Joshi, Magen, Srebro, Tsilivis, Vardi, Learning to Think from Multiple Thinkers: How Chain-of-Thought Heterogeneity Affects Efficient Learnability, arXiv:2604.24737 (held version, sha256 e663a640…), Proposition 6.3, p.18 (PDF p.18); Theorem 7, p.25 (PDF p.25)

import Mathlib
import Definitions.Def_MultiThinkCoT_e2e

namespace MultiThinkCoT

/-!
# The base class `F` over the prefix domain `X × {0,1}^{≤T−1}`

N. Joshi, R. Magen, N. Srebro, N. Tsilivis, G. Vardi, *Learning to Think from Multiple Thinkers*,
arXiv:2604.24737 (held version, sha256 e663a640…), Proposition 6.3, p.18 (PDF p.18), and
Theorem 7, p.25: "the quantity `VCdim(F)` is taken over the domain `X × {0,1}^{≤T−1}`".

A point `(x, p)` of the prefix domain is the string `[x, p]`, and `f ∈ F` acts on it as
`f([x, p])`.

**Formalization Note.** `{0,1}^{≤T−1}` is the subtype of `List Bool` of length at most `T - 1`
(natural-number subtraction; at `T = 0` this is `{[]}`, a case in which the CoT is empty and
`L^{CoT-0}(F)` is a single function).
-/

/-- `F` viewed as a class over `X × {0,1}^{≤T−1}`: `(x, p) ↦ f([x, p])`. -/
def prefixClass (F : Set Gen) (T : ℕ) (X : Set (List Bool)) :
    Set (X × {p : List Bool // p.length ≤ T - 1} → Bool) :=
  {g | ∃ f ∈ F, ∀ q : X × {p : List Bool // p.length ≤ T - 1}, g q = f (q.1.1 ++ q.2.1)}

end MultiThinkCoT


