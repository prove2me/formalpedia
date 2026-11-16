-- Prove2me | Definitions.Def_GeomDRSub_Supplement_OnlineAchievable
-- name    : GeomDRSub_Supplement_OnlineAchievable
-- status  : Definition
-- author  : @iris
-- created : 2026-11-15T18:44:53.062523+00:00
-- url     : https://prove2.me/theorems/2a025bb9-6060-486d-8620-ed804bcdc583
-- title:
--   Coefficients attained by a uniform online algorithm (Section 7.2, (213))
-- statement:
--   Fix $\zeta$. An **online instance** consists of a dimension $d$, an admissible $K\subseteq[0,1]^d$ with $\zeta\mathbf 1\in K$, a bound $D\ge\operatorname{diam}K$, and an oblivious sequence $f_1,f_2,\dots$ of nonnegative continuously differentiable DR-submodular objectives with $0\le f_t\le M$ and $\|\nabla f_t\|_2\le B$ on the cube (5). Queries are exact value–gradient queries and projections are exact. A **uniform online algorithm** receives $(d,T,D,M,B)$. On round $t$ it commits $p_t\in K$ before querying, and its queries on that round refer to $f_t$.
--
--   A coefficient $a$ is **attained** if there are a uniform online algorithm, a constant $\kappa<1$ and fixed real polynomials $P_Q,P_R$ such that on every instance and for every horizon $T$:
--
--   $$Q(T)\le P_Q(d,T,1+D,1+M,1+B),\qquad \mathrm{Reg}_a(T)\le P_R(d,1+D,1+M,1+B)\,T^{\kappa},$$
--
--   where $Q(T)$ is the number of objective queries and projections on every execution, and
--
--   $$\mathrm{Reg}_a(T)=a\max_{o\in K}\sum_{t=1}^T f_t(o)-\mathbb E\sum_{t=1}^T f_t(p_t)$$
--
--   is the expected static approximate regret (9).
--
--   **Formalization Note** The sequence is fixed before the learner's seed is drawn. The learner observes only the responses to its calls: to see its reward it queries $p_t$, which is counted. Only calls made before the commit of the last action $p_T$ are bounded; later calls cannot influence any action, so a learner may stop there and the set of attained coefficients is unchanged. Rounds are $0$-based, and the regret's maximum over $K$ is written as a bound for every comparator $o\in K$.
-- source:
--   Aggarwal–Lu, Geometry-Dependent Online and Offline Approximation for Non-Monotone DR-Submodular Maximization, arXiv:2610.00545, Section 7.2, p.52, (213); regret (9), p.9; online model Section 3.2, p.8

import Mathlib
import Definitions.Def_GeomDRSub_cube
import Definitions.Def_GeomDRSub_IsAdmissible
import Definitions.Def_GeomDRSub_gradQ
import Definitions.Def_GeomDRSub_IsDRSubmodular
import Definitions.Def_OrabonaOL_OGD_IsEuclideanProj
import Definitions.Def_GeomDRSub_Supplement_OracleStrategy_count
import Definitions.Def_GeomDRSub_Supplement_OracleStrategy_markPt
import Definitions.Def_GeomDRSub_Supplement_onlineAns

namespace GeomDRSub.Supplement

/-- **Coefficients attained by a uniform online algorithm (Section 7.2, (213)).** Aggarwal–Lu, *Geometry-Dependent Online and Offline Approximation for Non-Monotone
DR-Submodular Maximization*, arXiv:2610.00545,
p.52: "Fix `ζ`. An online instance consists of a set `K` as in Section 3.1 with `ζ1 ∈ K`, an
oblivious sequence of nonnegative continuously differentiable DR-submodular objectives satisfying
(5), exact value-and-gradient queries, and exact projection onto `K`. A uniform online algorithm is a
single algorithm that receives `d, T, D, M, B` and is run on every such instance; it may depend on
`ζ`. Let `αon(ζ)` be the supremum of coefficients `a` for which there are a uniform online
algorithm, a constant `κ < 1`, and fixed polynomials `P_Q, P_R` such that, on every instance and for
every `T`, `Q(T) ≤ P_Q(d, T, 1 + D, 1 + M, 1 + B)`, `Reg_a(T) ≤ P_R(d, 1 + D, 1 + M, 1 + B) T^κ`
(213), where `Q(T)` is the total number of objective queries and projections on every execution.
Objective queries on a round occur after the action for that round has been committed."

`OnlineAchievable ζ a` says: there are a probability space `(Ω, μ)`, one oracle algorithm `A` with
inputs `(T, D, M, B)` (and `d`), a real `κ < 1` and real polynomials `P_Q` (five variables) and
`P_R` (four variables) such that for every `d`, every admissible `K` with `D ≥ diam K` and exact
projection `proj = Π_K`, every sequence `f_0, f_1, …` of DR-submodular objectives with
`0 ≤ f_t ≤ M` and `‖∇f_t‖ ≤ B` on the cube (5), and every horizon `T`, in the online execution
(`onlineAns`: the `t`-th mark is the action `p_t`, and queries after it answer for `f_t`):
1. on every execution, for every round `t < T` the action `p_t` is committed, and the number of
   objective queries plus projection calls before it is at most `P_Q(d, T, 1 + D, 1 + M, 1 + B)`;
2. on every execution `p_t ∈ K` for `t < T`;
3. `Reg_a(T) ≤ P_R(d, 1 + D, 1 + M, 1 + B) · T^κ`, where
   `Reg_a(T) = a max_{o∈K} Σ_{t<T} f_t(o) − E Σ_{t<T} f_t(p_t)` (9), written for every `o ∈ K`.

**Formalization Note.** The sequence is fixed before the seed `ω` is drawn (oblivious adversary).
The learner observes only the responses to its calls (to see its reward it queries `p_t`, which is
counted); the rewards `f_t(p_t)` enter only the regret. Only the calls before the commit of
`p_{T-1}` are bounded in item 1: calls made after the last commit cannot influence any action, so a
learner can stop there, and the set of attained coefficients is the same as when every call is
counted. Rounds are 0-based; `T` is passed as the real `(T : ℝ)`. The range `a ∈ [0,1]` is imposed
in `alphaOn`. -/
def OnlineAchievable (ζ a : ℝ) : Prop :=
  ∃ (Ω : Type) (_ : MeasurableSpace Ω) (μ : MeasureTheory.Measure Ω) (A : OracleStrategy Ω 4)
    (κ : ℝ) (PQ : MvPolynomial (Fin 5) ℝ) (PR : MvPolynomial (Fin 4) ℝ),
    MeasureTheory.IsProbabilityMeasure μ ∧ κ < 1 ∧
    ∀ (d : ℕ) (K : Set (EuclideanSpace ℝ (Fin d))) (f : ℕ → EuclideanSpace ℝ (Fin d) → ℝ)
      (M B D : ℝ) (proj : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d)),
      IsAdmissible K ζ → (∀ a ∈ K, ∀ b ∈ K, ‖a - b‖ ≤ D) →
      (∀ z, OrabonaOL.OGD.IsEuclideanProj K z (proj z)) →
      (∀ t, IsDRSubmodular (f t) ∧
        ∀ y ∈ cube d, 0 ≤ f t y ∧ f t y ≤ M ∧ ‖gradQ (f t) y‖ ≤ B) →
      ∀ T : ℕ,
        (∀ ω, ∀ t < T, ∃ τ,
          (A.call d ![(T : ℝ), D, M, B] (onlineAns f proj) ω τ).elim (fun _ => false)
              Sum.isRight = true ∧
          (A.state d ![(T : ℝ), D, M, B] (onlineAns f proj) ω τ).2 = t ∧
          ((A.count d ![(T : ℝ), D, M, B] (onlineAns f proj) ω Sum.isLeft τ +
              A.count d ![(T : ℝ), D, M, B] (onlineAns f proj) ω
                (fun c => c.elim (fun _ => false) Sum.isLeft) τ : ℕ) : ℝ) ≤
            MvPolynomial.eval ![(d : ℝ), (T : ℝ), 1 + D, 1 + M, 1 + B] PQ) ∧
        (∀ ω, ∀ t < T, A.markPt d ![(T : ℝ), D, M, B] (onlineAns f proj) ω t ∈ K) ∧
        ∀ o ∈ K, a * ∑ t ∈ Finset.range T, f t o -
            ∫ ω, ∑ t ∈ Finset.range T,
              f t (A.markPt d ![(T : ℝ), D, M, B] (onlineAns f proj) ω t) ∂μ ≤
          MvPolynomial.eval ![(d : ℝ), 1 + D, 1 + M, 1 + B] PR * (T : ℝ) ^ κ

end GeomDRSub.Supplement


