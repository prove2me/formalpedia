-- Prove2me | Definitions.Def_JohnsonApprox_SetCover_Fig1
-- name    : JohnsonApprox_SetCover_Fig1
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-27T15:26:35.171718+00:00
-- url     : https://prove2.me/theorems/237a5229-6ad2-4062-8d07-6f9373c571e5
-- title:
--   The SET COVERING I input of Fig. 1, with subfamilies F₀ and F₁ (Section 5, p. 265)
-- statement:
--   This is the input of Fig. 1 in Johnson (1974), p. 265, used to show that the bound of Theorem 4 is attained. Fix $k \ge 1$.
--
--   The set to be covered, $T$, consists of $k \cdot k!$ points, divided into $k$ segments of $k!$ points each, labelled $1$ to $k$. Write $(s, q)$ for point $q$ ($0 \le q < k!$) of segment $s + 1$ ($0 \le s < k$). The family $F$ consists of two kinds of sets.
--
--   1. **$F_0$**: for each $q$, the set $\{(s, q) : 0 \le s < k\}$. These are $k!$ disjoint $k$-element sets, each containing one point from each of the $k$ segments.
--   2. **$F_1$**: for each segment $s + 1$ and each $b < k!/(s+1)$, the block
--   $$B_{s,b} = \{(s, q) : \lfloor q/(s+1) \rfloor = b\}.$$
--   For fixed $s$ these are $k!/(s+1)$ disjoint $(s+1)$-element sets forming a cover of segment $s + 1$.
--
--   So $F_1$ consists of $k!/k$ disjoint $k$-element sets covering segment $k$, $k!/(k-1)$ disjoint $(k-1)$-element sets covering segment $k-1$, and so on down to $k!$ single-element sets covering segment 1, in total $k!\,(1/k + 1/(k-1) + \dots + 1)$ sets.
--
--   **Formalization Note** Points are `Fin k × Fin k!`; set indices are `Fin k! ⊕ Σ s : Fin k, Fin (k!/(s+1))`, the left summand for $F_0$ and the right for $F_1$. Segments are 0-based. `fig1F₀ k` and `fig1F₁ k` are the two subfamilies as sets of sets. At $k = 1$ both subfamilies consist of the same single one-point set, which the input then carries under two indices.
-- source:
--   Johnson, Approximation algorithms for combinatorial problems, J. Comput. System Sci. 9 (1974), pp. 265–266, proof of Theorem 4 (Fig. 1)

import Mathlib
import Definitions.Def_JohnsonApprox_SetCover_Problem

namespace JohnsonApprox.SetCover

/-!
The SET COVERING I input of Fig. 1 (Johnson 1974, p. 265), for a given `k`.

`T` consists of `k · k!` points, divided into `k` segments of `k!` points each. The point
`(s, q)` is point `q` (`0 ≤ q < k!`) of segment `s + 1` (`0 ≤ s < k`).
-/

/-- The `k · k!` points of `T`: segment `s + 1` (`s : Fin k`), position `q` (`q : Fin k!`). -/
abbrev Fig1Point (k : ℕ) := Fin k × Fin k.factorial

/-- Indices of the sets of `F`: `inl q` for the `k!` sets of `F₀`, and `inr ⟨s, b⟩` for the
`k!/(s+1)` sets of `F₁` covering segment `s + 1`, `b < k!/(s+1)`. -/
abbrev Fig1Index (k : ℕ) := Fin k.factorial ⊕ (Σ s : Fin k, Fin (k.factorial / (s.val + 1)))

/-- The family `F` of Fig. 1.
* `F₀`: the set `inl q` contains one point from each segment, the point `q`; these `k!` sets
  are disjoint and have `k` elements.
* `F₁`: the set `inr ⟨s, b⟩` is the block of the `s + 1` points `q` of segment `s + 1` with
  `⌊q / (s+1)⌋ = b`; for fixed `s` these are `k!/(s+1)` disjoint `(s+1)`-element sets covering
  segment `s + 1`. -/
def fig1 (k : ℕ) : Fig1Index k → Finset (Fig1Point k)
  | Sum.inl q => Finset.univ.filter (fun x => x.2 = q)
  | Sum.inr ⟨s, b⟩ => Finset.univ.filter (fun x => x.1 = s ∧ x.2.val / (s.val + 1) = b.val)

/-- The subfamily `F₁` of Fig. 1: all the sets `inr ⟨s, b⟩`. -/
def fig1F₁ (k : ℕ) : Finset (Finset (Fig1Point k)) :=
  Finset.univ.image (fun i : (Σ s : Fin k, Fin (k.factorial / (s.val + 1))) => fig1 k (Sum.inr i))

/-- The subfamily `F₀` of Fig. 1: all the sets `inl q`. -/
def fig1F₀ (k : ℕ) : Finset (Finset (Fig1Point k)) :=
  Finset.univ.image (fun q : Fin k.factorial => fig1 k (Sum.inl q))

end JohnsonApprox.SetCover


