-- Prove2me | Definitions.Def_ValiantModel_Supplement_IntersectionClosure
-- name    : ValiantModel_Supplement_IntersectionClosure
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T06:21:51.939194+00:00
-- url     : https://prove2.me/theorems/1c2735e8-45c7-4e4a-84f0-3b9a5f8b7e9d
-- title:
--   The intersection closure $\overline H$ of a concept class
-- statement:
--   For $H\subseteq\{0,1\}^X$, the **intersection closure** $\overline H$ is the smallest class that contains $H$ and is closed under finite intersections:
--   $$\overline H=\Big\{\mathrm{supp}(h_1)\cap\cdots\cap\mathrm{supp}(h_k)\;:\;k\ge1,\ h_1,\dots,h_k\in H\Big\},$$
--   each set identified with its indicator function.
--
--   It appears in Theorem 1.5(3): finite VC dimension of $\overline H$ is sufficient for learnability over a general domain.
--
--   **Formalization Note** Only non-empty families are intersected ($k\ge1$). The constant-one function, the empty intersection, is in $\overline H$ only if some intersection of members of $H$ equals it.
-- source:
--   Hanneke, Mehrotra, Velegkas, Zampetakis, What is Learnable in Valiant's Theory of the Learnable?, arXiv:2605.13840 (version held, sha256 f793f255…), footnote 4, p.4 (PDF p.6) and footnote 6, p.16 (PDF p.18)

import Mathlib

namespace ValiantModel.Supplement

/-- The **intersection closure** `H̄` of `H` (footnotes 4 and 6 of Hanneke, Mehrotra, Velegkas,
Zampetakis, arXiv:2605.13840, version held, sha256 f793f255…, p.4, PDF p.6 and p.16, PDF p.18): the
smallest class containing `H` and closed under finite intersections, i.e. all
`supp(h₁) ∩ ⋯ ∩ supp(h_k)` with `k ≥ 1` and every `hᵢ ∈ H`, as indicator functions.

**Formalization Note.** Only non-empty families are intersected (`k ≥ 1`): the constant-one function
(the empty intersection) is in `H̄` only if some intersection of members of `H` equals it. This is
exactly the smallest superclass closed under (binary) intersections. -/
def intersectionClosure {X : Type} (H : Set (X → Bool)) : Set (X → Bool) :=
  {g | ∃ F : Finset (X → Bool), F.Nonempty ∧ (↑F : Set (X → Bool)) ⊆ H ∧
    ∀ x, g x = true ↔ ∀ f ∈ F, f x = true}

end ValiantModel.Supplement


