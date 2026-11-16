-- Prove2me | Definitions.Def_SATotalCoeffLB_Supplement_IsNonSignaling
-- name    : SATotalCoeffLB_Supplement_IsNonSignaling
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T03:27:17.26708+00:00
-- url     : https://prove2.me/theorems/b1fd52eb-614b-4adc-a9f8-24c3ffd7c2e9
-- title:
--   $(k,\delta)$-non-signaling family of distributions
-- statement:
--   Let $U$ be a finite set, $k$ a natural number and $\delta$ a real number. A family $D = \{D_S\}_{S \subseteq U,\, |S| \le k}$ of local distributions is **$(k, \delta)$-non-signaling** if for all $T \subseteq S \subseteq U$ with $|S| \le k$,
--
--   $$
--   \mathrm{SD}\bigl(D_T, (D_S)|_T\bigr) \le \delta ,
--   $$
--
--   where $(D_S)|_T$ is the marginal of $D_S$ on $T$. The number $\delta$ is the non-signaling parameter, and a $(k, 0)$-non-signaling family is called **exact**: then every $D_T$ is exactly the marginal of every $D_S$ with $S \supseteq T$, so the local views agree on common coordinates.
--
--   This is the paper's definition, following Kalai–Raz–Rothblum. It compares a set with each of its supersets; it is not the pairwise condition of Chiesa–Manohar–Shinkar and later works, which differs from it by a factor $2$ in $\delta$.
--
--   **Formalization Note** $D_T$ is evaluated at the proof of $|T| \le |S| \le k$.
-- source:
--   Chen–Jin, Non-signaling PCPs as Algebraic Proofs, and Total Coefficients Lower Bounds for Sherali–Adams, STOC 2027 submission (manuscript sha256 da19ece6…9d9178), §4.2 (Non-signaling Strategy), p.25

import Mathlib
import Definitions.Def_SamplingAC0_tvDist
import Definitions.Def_SATotalCoeffLB_Supplement_marginal
import Definitions.Def_SATotalCoeffLB_Supplement_LocalFamily

namespace SATotalCoeffLB.Supplement

/-- **`(k, δ)`-non-signaling family** (§4.2, "Non-signaling Strategy", p.25, of Chen–Jin, *Non-signaling PCPs as Algebraic Proofs, and Total Coefficients Lower Bounds for
Sherali–Adams*, STOC 2027 submission manuscript
(sha256 da19ece6898e20b159d01408327de710d69219772cc1f088c80301a6679d9178), following
[KRR14]): a family `D = {D_S}_{S ⊆ U, |S| ≤ k}` with
`SD(D_T, (D_S)|_T) ≤ δ` for all `T ⊆ S ⊆ U` with `|S| ≤ k`.
A `(k, 0)`-non-signaling family is called **exact**: then `D_T` is exactly the marginal of `D_S`.

**Formalization Note** This is the paper's condition (a sub-set against a super-set), not the
pairwise condition of [CMS20; DHK+26]. `D_T` is taken at the proof `|T| ≤ |S| ≤ k`. The statistical
distance `SD(p, q) = ½ ∑ₓ |p(x) − q(x)|` is the published `SamplingAC0.tvDist`. -/
def IsNonSignaling {U A : Type} [DecidableEq U] [Fintype A] (k : ℕ) (δ : ℝ)
    (D : LocalFamily U A k) : Prop :=
  ∀ (T S : Finset U) (hTS : T ⊆ S) (hS : S.card ≤ k),
    SamplingAC0.tvDist (D T ((Finset.card_le_card hTS).trans hS)) (marginal hTS (D S hS)) ≤ δ

end SATotalCoeffLB.Supplement


