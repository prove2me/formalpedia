-- Prove2me | Definitions.Def_RandTreeUniv_InT2
-- name    : RandTreeUniv_InT2
-- status  : Definition
-- author  : @iris
-- created : 2026-11-09T23:12:11.277824+00:00
-- url     : https://prove2.me/theorems/30e69860-2aff-4314-b8ab-477011d5a5f9
-- title:
--   The family $\mathcal T_2$ (few leaves, no long bare paths)
-- statement:
--   With $K$ and $\alpha=n\ln\ln n/(K^3\ln n)$ as in §4, the family $\mathcal T_2$ consists of the trees in $\mathcal T_{n,\Delta}\setminus\mathcal T_1$ with at most $e^{\Delta^5}\alpha$ leaves: trees on $n$ vertices of maximum degree at most $\Delta$, without $K\alpha$ vertex-disjoint bare paths of length $n/(K^2\alpha)$, and with
--
--   $$
--   \#\{\text{leaves}\}\le e^{\Delta^5}\alpha .
--   $$
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

/-- `T ∈ T₂` (Cohen Antonir, Lichev, Zhukovskii, *Universality in random graphs via optimal linking systems: trees and beyond*, arXiv:2608.06358 (held revision, sha256 33e85b21…), §4, p.21 (PDF 22)): "the family `T₂` consists of the trees in `T \ T₁` with at
most `exp(∆⁵)α` leaves", with `α = n ln ln n/(K³ ln n)` (`ψ = 1`, §6, p.31 (PDF 32)).

**Formalization Note** `exp(∆⁵)α` is compared as a real number (no rounding). -/
def InT2 (n : ℕ) (K : ℝ) (Δ : ℕ) (T : SimpleGraph (Fin n)) : Prop :=
  InTreeFamily Δ T ∧ ¬ InT1 n K Δ T ∧ (numLeaves T : ℝ) ≤ Real.exp ((Δ : ℝ) ^ 5) * alpha K 1 n

end RandTreeUniv


