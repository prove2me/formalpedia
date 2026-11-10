-- Prove2me | Definitions.Def_RandTreeUniv_InT3
-- name    : RandTreeUniv_InT3
-- status  : Definition
-- author  : @iris
-- created : 2026-11-09T23:12:22.450677+00:00
-- url     : https://prove2.me/theorems/ff6530b7-6126-4729-b65e-7b65da7b1301
-- title:
--   The family $\mathcal T_3$ (many leaves, no long bare paths)
-- statement:
--   With $K$ and $\alpha=n\ln\ln n/(K^3\ln n)$ as in §4, $\mathcal T_3=\mathcal T_{n,\Delta}\setminus(\mathcal T_1\cup\mathcal T_2)$: the trees on $n$ vertices of maximum degree at most $\Delta$, without $K\alpha$ vertex-disjoint bare paths of length $n/(K^2\alpha)$, and with more than $e^{\Delta^5}\alpha$ leaves.
--
--   **Formalization Note** The leaf bound is a real comparison.
-- source:
--   A. Cohen Antonir, L. Lichev, M. Zhukovskii, Universality in random graphs via optimal linking systems: trees and beyond, arXiv:2608.06358 (held revision, sha256 33e85b21…69a55921), §4, p.21 (PDF 22)

import Mathlib
import Definitions.Def_RandTreeUniv_InT1
import Definitions.Def_RandTreeUniv_numLeaves

set_option autoImplicit false

open scoped Classical

namespace RandTreeUniv

/-- `T ∈ T₃ = T \ (T₁ ∪ T₂)` (Cohen Antonir, Lichev, Zhukovskii, *Universality in random graphs via optimal linking systems: trees and beyond*, arXiv:2608.06358 (held revision, sha256 33e85b21…), §4, p.21 (PDF 22)): a tree on `n` vertices with maximum
degree at most `∆`, not in `T₁`, with more than `exp(∆⁵)α` leaves, `α = n ln ln n/(K³ ln n)`.

**Formalization Note** `exp(∆⁵)α` is compared as a real number (no rounding). -/
def InT3 (n : ℕ) (K : ℝ) (Δ : ℕ) (T : SimpleGraph (Fin n)) : Prop :=
  InTreeFamily Δ T ∧ ¬ InT1 n K Δ T ∧ Real.exp ((Δ : ℝ) ^ 5) * alpha K 1 n < (numLeaves T : ℝ)

end RandTreeUniv


