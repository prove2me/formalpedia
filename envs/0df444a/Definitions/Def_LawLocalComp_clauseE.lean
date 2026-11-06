-- Prove2me | Definitions.Def_LawLocalComp_clauseE
-- name    : LawLocalComp_clauseE
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T03:13:41.393028+00:00
-- url     : https://prove2.me/theorems/bb054889-7050-4feb-88de-053cd1e55eb5
-- title:
--   Theorem 1.1: horizon one or rank one is exact by the mean
-- statement:
--   The mean map $X\mapsto\delta_{\mathbb E X}$ is a rational conditional-mean replacement preserving means and point masses on rational laws, and for one job ($n\le1$) or for nonnegative directions of rank at most one it is exact: $\mathbb E g(\tilde L)=\mathbb E g(L)$ for every monotone norm $g$.
-- source:
--   Mahboub–Rahgoshay, Optimal Law-Local Compression for Stochastic Loads, STOC 2027 submission (manuscript of Oct. 29, 2026, sha256 5f71501c…aa873), Theorem 1.1, p.2; "Endpoint transfer", p.7, last two sentences

import Mathlib
import Definitions.Def_LawLocalComp_IsGoodOutput
import Definitions.Def_LawLocalComp_dirac
import Definitions.Def_LawLocalComp_IsMonotoneNorm
import Definitions.Def_LawLocalComp_expNorm
import Definitions.Def_LawLocalComp_dirRank

namespace LawLocalComp

/-- **Theorem 1.1: horizon one or rank one is exact by the mean.**
Mahboub–Rahgoshay, *Optimal Law-Local Compression for Stochastic Loads*, STOC 2027
submission manuscript of Oct. 29, 2026 (sha256 5f71501c…aa873), Theorem 1.1, p.2.

The mean map `X ↦ δ_{E X}` is a rational conditional-mean replacement preserving means and point
masses, and it is exact (`E g(L̃) = E g(L)`) for one job or for directions of rank at most one.
-/
def clauseE : Prop :=
  (∀ X : Law, IsRatLaw X → IsGoodOutput X (dirac (mean X))) ∧
  ∀ (d n : ℕ) (X : Fin n → Law) (a : Fin n → Fin d → ℝ), (∀ j, 0 ≤ a j) → (n ≤ 1 ∨ dirRank a ≤ 1) →
    ∀ g : (Fin d → ℝ) → ℝ, IsMonotoneNorm g →
      expNorm g (fun j => dirac (mean (X j))) a = expNorm g X a

end LawLocalComp


