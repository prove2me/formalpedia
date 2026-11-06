-- Prove2me | Definitions.Def_GradSuffice_IsMDSLaw
-- name    : GradSuffice_IsMDSLaw
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T02:18:41.166192+00:00
-- url     : https://prove2.me/theorems/bb8f0faa-bcec-446f-aff1-c9ea915fd58f
-- title:
--   Finitely supported martingale-difference sequence in $X^\star$
-- statement:
--   A **martingale (difference sequence) of size $M$** in $X^\star$ is a random sequence $(\xi_1,\dots,\xi_M)$ of dual vectors with finite support such that
--   $$\mathbb E[\xi_i\mid\xi_1,\dots,\xi_{i-1}]=0\qquad(i=1,\dots,M).$$
--   It is described by its law $P$, a finitely supported probability distribution on sequences $x=(x_1,\dots,x_M)$; the condition says that for every $i$ and every sequence $x$ in the support,
--   $$\sum_{y:\ y_j=x_j\ (j<i)}P(y)\,y_i=0 .$$
--
--   **Formalization Note** The law is a `NondualOpt.FinLaw` on `Fin M → StrongDual ℝ X`. Conditioning is on the sequence's own past; a sequence that is a martingale difference for a larger filtration is one for its own past, so this is the most general class.
-- source:
--   Alon–Koren–Livni–Moran, When Do Gradients Suffice? A Characterization of First-Order Convex Optimization, manuscript of November 3, 2026 (STOC 2027 submission), §6.1, p.14; §8, pp.24–26

import Mathlib
import Definitions.Def_NondualOpt_FinLaw
open Classical

namespace GradSuffice

/-- **Finitely supported martingale-difference sequence of size `M` in `X⋆`.** Alon–Koren–Livni–Moran, *When Do Gradients Suffice?*, manuscript of November 3, 2026, §6.1, p.14
("`ξᵢ` is a random variable with finite support […] such that `E[ξᵢ | ξ₁, …, ξ_{i−1}] = 0`") and
§8, pp.24–26 ("every martingale of size `m` (not necessarily binary)").

**Formalization Note.** The law of `(ξ₁, …, ξ_M)` is a finitely supported probability law `P` on
paths `Fin M → StrongDual ℝ X` (`NondualOpt.FinLaw` on `Set.univ`). The martingale-difference
condition is conditional mean zero given each past prefix of positive probability: for every
`i` and every path `x` in the support, the `P`-weighted sum of `yᵢ` over the support paths `y`
agreeing with `x` before `i` vanishes. Conditioning is on the sequence's own past (a sequence
that is a martingale difference for a larger filtration is one for its own). -/
def IsMDSLaw {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] {M : ℕ}
    (P : NondualOpt.FinLaw (Set.univ : Set (Fin M → StrongDual ℝ X))) : Prop :=
  ∀ i : Fin M, ∀ x ∈ P.w.support,
    ∑ y ∈ P.w.support.filter (fun y => ∀ j : Fin M, j < i → y j = x j), P.w y • y i = 0

end GradSuffice


