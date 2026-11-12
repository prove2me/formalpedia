-- Prove2me | Definitions.Def_DSDensity1246_Main_listDensity
-- name    : DSDensity1246_Main_listDensity
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-11T16:11:05.07638+00:00
-- url     : https://prove2.me/theorems/c2134363-71df-4e5f-95c7-11d413454171
-- title:
--   List density of a finite word family
-- statement:
--   Let $W\subseteq Y^n$ be finite and let $\ell\ge1$. For each direction $i$, let $T_i$ be the set of assignments away from $i$ realized by $W$, and let $e_{i,a}$ be the corresponding fiber. For nonempty $W$, its $\ell$-density is
--
--   $$\operatorname{Dens}^\ell(W)=\frac{1}{|W|}\sum_{i=1}^n\sum_{a\in T_i}\max(|e_{i,a}|-\ell,0).$$
--
--   This is the density from Definition 5, also called shifting average $\ell$-degree in the cited literature. Each direction contributes separately, including when edges in different directions coincide as vertex sets.
--
--   **Formalization Note** Values lie in the nonnegative reals. Natural subtraction computes the positive part exactly before conversion; division is performed after converting the two natural cardinalities. The empty family is assigned value zero and is excluded from the maximum-density supremum.
-- source:
--   Chirag Pabbaraju, STOC 2027 submission #1246 (October 2026), p. 13, Definition 5; p. 14, Remark 1

import Definitions.Def_DSDensity1246_Main_oneInclusion

open scoped NNReal

namespace DSDensity1246.Main

/-- Definition 5, p. 13: sum over indexed nonempty fibers, divided by |W|.
Natural subtraction is exactly the positive part (|e| - ℓ)₊.
The empty-family value is totalized as zero by division in ℝ≥0. -/
noncomputable def listDensity {Y : Type*} {n : ℕ}
    (ℓ : ℕ) (W : Finset (Fin n → Y)) : ℝ≥0 :=
  ((∑ i : Fin n, ∑ a ∈ finiteBehaviors W i,
      ((finiteFiber W i a).card - ℓ) : ℕ) : ℝ≥0) / (W.card : ℝ≥0)

end DSDensity1246.Main


