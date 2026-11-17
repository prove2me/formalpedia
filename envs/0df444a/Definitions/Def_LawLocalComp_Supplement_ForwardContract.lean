-- Prove2me | Definitions.Def_LawLocalComp_Supplement_ForwardContract
-- name    : LawLocalComp_Supplement_ForwardContract
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T14:06:10.929181+00:00
-- url     : https://prove2.me/theorems/a8ce9abb-19f8-4dc7-aa1e-cf62d1ac31cb
-- title:
--   The forward guarantee (25): $\mathbb E g(L) \le \mathbb E g(L_{\hat Y}) \le \kappa\,\mathbb E g(L)$
-- statement:
--   Let $\Phi$ map finite nonnegative laws to finite nonnegative laws, let $R$ be a supplied resource (horizon $N$, rank promise $q$, or both) and $\kappa > 0$. $\Phi$ satisfies the **forward guarantee with factor $\kappa$** if for every dimension $d$, every selection of $n$ independent jobs with rational laws $X_1, \dots, X_n$ and directions $a_1, \dots, a_n \in \mathbb R^d_+$ admitted by $R$ ($n \le N$ under a horizon, $\dim \operatorname{span}\{a_j\} \le q$ under a rank promise), and every norm $g$ monotone on $\mathbb R^d_+$, the loads $L = \sum_j X_j a_j$ and $L_{\hat Y} = \sum_j \hat Y_j a_j$, with $\hat Y_j \sim \Phi(X_j)$ sampled independently per copy, satisfy
--   $$
--   \mathbb E g(L) \le \mathbb E g(L_{\hat Y}) \le \kappa\,\mathbb E g(L).
--   $$
--   With $\kappa = 1 + \varepsilon$ this is (25). It is the contracting guarantee (1) with input and output exchanged.
-- source:
--   Mahboub–Rahgoshay, Optimal Law-Local Compression for Stochastic Loads, STOC 2027 submission (manuscript of Oct. 29, 2026, sha256 5f71501c…aa873), Theorem 6.2, (25), p.10

import Mathlib
import Definitions.Def_LawLocalComp_IsRatLaw
import Definitions.Def_LawLocalComp_IsMonotoneNorm
import Definitions.Def_LawLocalComp_expNorm
import Definitions.Def_LawLocalComp_dirRank
import Definitions.Def_LawLocalComp_Resource_admits

namespace LawLocalComp

namespace Supplement

/-- **The forward guarantee (25) with factor `κ`.**
Mahboub–Rahgoshay, *Optimal Law-Local Compression for Stochastic Loads*, STOC 2027
submission manuscript of Oct. 29, 2026 (sha256 5f71501c…aa873), Theorem 6.2, (25), p.10: `E g(L) ≤ E g(L_Ŷ) ≤ (1 + ε) E g(L)`.

`ForwardContract Φ R κ`: for every dimension `d`, every selection of `n` independent jobs with
rational laws `X_j` and nonnegative directions `a_j ∈ ℝ^d_+` admitted by the resource `R`, and every
norm `g` monotone on `ℝ^d_+`, the original load `L = ∑ X_j a_j` and the output load
`L_Ŷ = ∑ Φ(X_j) a_j` (outputs sampled independently per copy) satisfy
`E g(L) ≤ E g(L_Ŷ) ≤ κ E g(L)`. (25) is `κ = 1 + ε`.

**Formalization Note.** This is the published `Contract` with the roles of input and output
exchanged: here the output load is the larger one. -/
def ForwardContract (Φ : Law → Law) (R : Resource) (κ : ℝ) : Prop :=
  ∀ (d n : ℕ) (X : Fin n → Law) (a : Fin n → Fin d → ℝ), (∀ j, IsRatLaw (X j)) →
    (∀ j, 0 ≤ a j) → R.admits n (dirRank a) → ∀ g : (Fin d → ℝ) → ℝ, IsMonotoneNorm g →
      expNorm g X a ≤ expNorm g (fun j => Φ (X j)) a ∧
        expNorm g (fun j => Φ (X j)) a ≤ κ * expNorm g X a

end Supplement

end LawLocalComp


