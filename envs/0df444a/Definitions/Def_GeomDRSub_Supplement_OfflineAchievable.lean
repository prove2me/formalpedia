-- Prove2me | Definitions.Def_GeomDRSub_Supplement_OfflineAchievable
-- name    : GeomDRSub_Supplement_OfflineAchievable
-- status  : Definition
-- author  : @iris
-- created : 2026-11-15T18:43:09.923934+00:00
-- url     : https://prove2.me/theorems/2eb1c66b-2ae1-4282-afbf-0cffde414e8b
-- title:
--   Achievable offline coefficient (Definition 6.1)
-- statement:
--   Fix $\zeta\in[0,1]$. An **offline instance** consists of a dimension $d$ and the following data:
--
--   1. a nonempty compact convex down-closed $K\subseteq[0,1]^d$ with $\zeta\mathbf 1\in K$;
--   2. a nonnegative continuously differentiable DR-submodular $f$ on $[0,1]^d$;
--   3. supplied bounds $M,B,v,D$ with $0\le f(y)\le M$ and $\|\nabla f(y)\|_2\le B$ on the cube, $0<v\le\mathrm{OPT}:=\max_{y\in K}f(y)$, and $\|a-b\|\le D$ for $a,b\in K$.
--
--   The algorithm receives $(d,\varepsilon,M,B,v,D)$ and accesses $f$ and $K$ only through exact value–gradient queries and exact Euclidean projections onto $K$. A coefficient $a$ is **achievable** if there are one randomized oracle algorithm and one fixed real polynomial $P$ in five variables such that for every instance and every $\varepsilon\in(0,1)$:
--
--   1. on every execution the algorithm returns a point $p$, after at most $P(d,\varepsilon^{-1},1+D,1+M/v,1+B/v)$ objective queries and at most as many projection calls (129);
--   2. $p\in K$ almost surely;
--   3. $\mathbb E f(p)\ge(a-\varepsilon)\,\mathrm{OPT}$ (128).
--
--   The algorithm and the polynomial may depend on $\zeta$ and $a$.
--
--   **Formalization Note** $\mathrm{OPT}$ is the supremum of $f$ over $K$, which is attained. "$D=\operatorname{diam}K$ or a supplied upper bound" is encoded as $\|a-b\|\le D$ on $K$. The exact projection is any map satisfying the Euclidean-projection predicate at every point; it is unique. Dimension $d=0$ is included and adds no constraint.
-- source:
--   Aggarwal–Lu, Geometry-Dependent Online and Offline Approximation for Non-Monotone DR-Submodular Maximization, arXiv:2610.00545, Definition 6.1, p.33, (128)–(129)

import Mathlib
import Definitions.Def_GeomDRSub_cube
import Definitions.Def_GeomDRSub_IsAdmissible
import Definitions.Def_GeomDRSub_gradQ
import Definitions.Def_GeomDRSub_IsDRSubmodular
import Definitions.Def_OrabonaOL_OGD_IsEuclideanProj
import Definitions.Def_GeomDRSub_Supplement_OracleStrategy_count
import Definitions.Def_GeomDRSub_Supplement_OracleStrategy_markPt
import Definitions.Def_GeomDRSub_Supplement_offlineAns

namespace GeomDRSub.Supplement

/-- **Achievable offline coefficient (Definition 6.1).** Aggarwal–Lu, *Geometry-Dependent Online and Offline Approximation for Non-Monotone
DR-Submodular Maximization*, arXiv:2610.00545, p.33: "Fix `ζ ∈ [0,1]`. An
instance consists of a nonempty compact convex down-closed set `K ⊆ [0,1]^d` containing `ζ1`, a
nonnegative continuously differentiable DR-submodular function `f` on `[0,1]^d`, and supplied bounds
`0 ≤ f(y) ≤ M`, `‖∇f(y)‖₂ ≤ B` (`y ∈ [0,1]^d`), `0 < v ≤ OPT := max_{y∈K} f(y)`. Let `D = diam(K)`,
or a supplied upper bound on this diameter. An objective query at `y ∈ [0,1]^d` returns the exact
pair `(f(y), ∇f(y))`, and exact Euclidean projection onto `K` is supplied separately. A coefficient
`a ∈ [0,1]` is achievable if one randomized algorithm and one fixed polynomial `P` have the following
property: for every such instance and every `ε ∈ (0,1)`, the algorithm returns `p ∈ K` almost
surely, satisfies `Ef(p) ≥ (a − ε) OPT` (128), and makes, on every execution, at most
`P(d, ε⁻¹, 1 + D, 1 + M/v, 1 + B/v)` (129) calls to each oracle. The algorithm and polynomial may
depend on the fixed `ζ` and `a`."

`OfflineAchievable ζ a` says: there are a probability space `(Ω, μ)` of internal randomness, one
oracle algorithm `A` with inputs `(ε, M, B, v, D)` (and the dimension `d`), and one real polynomial
`P` in five variables, such that for every dimension `d`, every instance `(K, f, M, B, v, D)` with the
exact projection `proj = Π_K`, and every `ε ∈ (0,1)`, in the offline execution of `A`:
1. on every execution `A` emits a point (its first mark, at time `τ`), having made at most
   `P(d, 1/ε, 1 + D, 1 + M/v, 1 + B/v)` objective queries and at most as many projection calls;
2. the returned point `p = markPt 0` lies in `K` almost surely;
3. `(a − ε) · OPT ≤ E f(p)`, with `OPT = sup_{y∈K} f(y)`.

**Formalization Note.** `OPT` is `sSup (f '' K)`; `K` is compact and nonempty and `f` is continuous
on it, so this is the maximum. "`D = diam(K)` or a supplied upper bound" is "`‖a − b‖ ≤ D` for all
`a, b ∈ K`". The exact projection is any `proj` with `IsEuclideanProj K z (proj z)` for every `z`
(it is unique, `K` being nonempty, closed and convex). The algorithm never receives `K` or `f`.
Dimension `d = 0` is included; there `K = {0}` and every `a ∈ [0,1]` is trivially attained, so this
adds no constraint. The range `a ∈ [0,1]` is imposed in `alphaOracle`. -/
def OfflineAchievable (ζ a : ℝ) : Prop :=
  ∃ (Ω : Type) (_ : MeasurableSpace Ω) (μ : MeasureTheory.Measure Ω) (A : OracleStrategy Ω 5)
    (P : MvPolynomial (Fin 5) ℝ),
    MeasureTheory.IsProbabilityMeasure μ ∧
    ∀ (d : ℕ) (K : Set (EuclideanSpace ℝ (Fin d))) (f : EuclideanSpace ℝ (Fin d) → ℝ)
      (M B v D : ℝ) (proj : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d)),
      IsAdmissible K ζ → (∀ a ∈ K, ∀ b ∈ K, ‖a - b‖ ≤ D) →
      (∀ z, OrabonaOL.OGD.IsEuclideanProj K z (proj z)) →
      IsDRSubmodular f → (∀ y ∈ cube d, 0 ≤ f y ∧ f y ≤ M) →
      (∀ y ∈ cube d, ‖gradQ f y‖ ≤ B) → 0 < v → v ≤ sSup (f '' K) →
      ∀ ε ∈ Set.Ioo (0 : ℝ) 1,
        (∀ ω, ∃ τ,
          (A.call d ![ε, M, B, v, D] (offlineAns f proj) ω τ).elim (fun _ => false)
              Sum.isRight = true ∧
          (A.state d ![ε, M, B, v, D] (offlineAns f proj) ω τ).2 = 0 ∧
          ((A.count d ![ε, M, B, v, D] (offlineAns f proj) ω Sum.isLeft τ : ℕ) : ℝ) ≤
            MvPolynomial.eval ![(d : ℝ), ε⁻¹, 1 + D, 1 + M / v, 1 + B / v] P ∧
          ((A.count d ![ε, M, B, v, D] (offlineAns f proj) ω
              (fun c => c.elim (fun _ => false) Sum.isLeft) τ : ℕ) : ℝ) ≤
            MvPolynomial.eval ![(d : ℝ), ε⁻¹, 1 + D, 1 + M / v, 1 + B / v] P) ∧
        (∀ᵐ ω ∂μ, A.markPt d ![ε, M, B, v, D] (offlineAns f proj) ω 0 ∈ K) ∧
        (a - ε) * sSup (f '' K) ≤
          ∫ ω, f (A.markPt d ![ε, M, B, v, D] (offlineAns f proj) ω 0) ∂μ

end GeomDRSub.Supplement


