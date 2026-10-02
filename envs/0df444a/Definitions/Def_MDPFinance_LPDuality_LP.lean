-- Prove2me | Definitions.Def_MDPFinance_LPDuality_LP
-- name    : MDPFinance_LPDuality_LP
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-09-27T22:52:22.617989+00:00
-- url     : https://prove2.me/theorems/e0466362-57fb-4764-88b1-8c31567f701b
-- title:
--   The occupation measure, M_b, and the primal/dual linear programs (P), (D)
-- statement:
--   For a stationary policy $f^\infty$ and initial law $p$, the **(discounted) occupation measure**
--   $\mu^{f^\infty}_p(B) := \sum_{k=0}^\infty \beta^k \mathbb P^{f^\infty}_p((X_k,A_k) \in B)$ records
--   the discounted expected number of visits to each measurable subset of state-action pairs — built
--   here from iterated pushforwards of $p$ through the model's own transition kernel under $f$
--   (`pkStep`), avoiding a canonical infinite-horizon path measure. $M_b$ collects the measures on
--   $D$ with finite $b$-integral, needed for the dual objective $\int r\,d\mu$ to be well-defined.
--
--   Given a closed linear subspace $IM \subset IB_b$ with $b \in IM$, the **primal program** $(P)$
--   minimizes $\int v\,dp$ over $v \in IM$ subject to $v \ge Tv$ (equivalently $v(x) - \beta\int
--   v(x')Q(dx'|x,a) \ge r(x,a)$ on $D$); the **dual program** $(D)$ maximizes $\int r\,d\mu$ over
--   measures $\mu \in M_b$ satisfying $\int[v(x)-\beta\int v(x')Q(dx'|x,a)]\,\mu(d(x,a)) = \int v\,dp$
--   for every $v \in IM$. $Z_P$, $Z_D$ are their feasible sets, $\mathrm{val}(P)$/$\mathrm{val}(D)$
--   their optimal values ($EReal$-valued, so a genuine $-\infty$/$+\infty$ remains expressible —
--   see `MODERATION_NOTES.md`). A **`p`-optimal** policy maximizes the functional $\pi \mapsto
--   \int J_\infty^\pi\,dp$ over all of $F^\infty$.
--
--   **Moderation note.** $Z_P$ is stated with the book's pointwise constraint $v(x)\ge Lv(x,a)$ on $D$ (equivalent to $v\ge Tv$); `IsClosedSubspaceOf` records §7.5.2's standing setting "IM a closed linear subspace of $\mathbb B_b$"; $p$-optimality is over policies $\pi'\in F^\infty$ (the draft compared against all maps).
-- source:
--   Bäuerle and Rieder, Markov Decision Processes with Applications to Finance, Universitext, Springer 2011, DOI 10.1007/978-3-642-18324-9, p. 214-215, unnumbered display preceding Theorem 7.5.6

import Mathlib
import Definitions.Def_MDPFinance_LPDuality_Model
import Definitions.Def_MDPFinance_LPDuality_Value
import Definitions.Def_MDPFinance_LPDuality_Bounding

open MeasureTheory ProbabilityTheory Filter

namespace MDPFinance.LPDuality

variable {E A : Type*} [MeasurableSpace E] [MeasurableSpace A]

/-- The `k`-step pushforward of the initial distribution `p` under a stationary decision rule
`f`, `p_0 := p`, `p_{k+1} := p_k.bind (fun x => Q(\cdot|x,f(x)))` (Bäuerle–Rieder, p. 214, PDF
226, the law of `X_k` under `\mathbb P^{f^\infty}_p`, built by iterated `Measure.bind` rather than
a canonical infinite path measure, per this series' own convention). -/
noncomputable def pkStep (M : MarkovDecisionModel E A) (f : E → A) : ℕ → Measure E → Measure E
  | 0, p => p
  | (k + 1), p => pkStep M f k (p.bind fun x => M.Q (x, f x))

/-- The **(discounted) occupation measure** `\mu^{f^\infty}_p(B) := \sum_{k=0}^\infty \beta^k
\mathbb P^{f^\infty}_p((X_k,A_k) \in B)` of the stationary policy `f^\infty` from initial law `p`
(Bäuerle–Rieder, p. 214, PDF 226): a countable sum of `\beta^k`-scaled pushforwards of the
`k`-step law of `X_k` under `x \mapsto (x,f(x))`. -/
noncomputable def occMeasure (M : MarkovDecisionModel E A) (f : E → A) (p : Measure E) :
    Measure (E × A) :=
  Measure.sum fun k => (ENNReal.ofReal (M.β ^ k)) • (pkStep M f k p).map fun x => (x, f x)

/-- `M_b := \{\mu \text{ measure on } D \mid \int b\,d\mu < \infty\}` (Bäuerle–Rieder, p. 215,
PDF 226), represented as measures on `E × A` restricted (via `hsupp`) to live on `D`. -/
def Mb (M : MarkovDecisionModel E A) (b : E → ℝ) : Set (Measure (E × A)) :=
  {μ | μ M.D = μ Set.univ ∧ ∫⁻ xa, ENNReal.ofReal (b xa.1) ∂μ < ⊤}

/-- `Z_P := \{v \in IM \mid v(x) - Lv(x,a) \ge 0 \text{ for all } (x,a) \in D\}` (Bäuerle–Rieder,
p. 215, PDF 227), the feasible set of the primal program `(P)`, with `Lv(x,a) = r(x,a) + β ∫ v
dQ(·|x,a)` pointwise in `(x,a) ∈ D` (equivalently `v ≥ Tv`). -/
def ZP (M : MarkovDecisionModel E A) (IMs : Set (E → ℝ)) : Set (E → ℝ) :=
  {v ∈ IMs | ∀ xa ∈ M.D, M.r xa + M.β * ∫ x', v x' ∂(M.Q xa) ≤ v xa.1}

/-- `IM` is a closed linear subspace of `IB_b` (the standing setting of §7.5.2, p. 215):
contained in `IB_b`, closed under addition and real scaling, and sequentially closed in the
weighted norm `\|\cdot\|_b`. -/
def IsClosedSubspaceOf (b : E → ℝ) (IMs : Set (E → ℝ)) : Prop :=
  IMs ⊆ IBb b ∧ (0 : E → ℝ) ∈ IMs ∧ (∀ v ∈ IMs, ∀ w ∈ IMs, v + w ∈ IMs) ∧
    (∀ c : ℝ, ∀ v ∈ IMs, c • v ∈ IMs) ∧
    ∀ (vn : ℕ → E → ℝ) (v : E → ℝ), (∀ n, vn n ∈ IMs) → v ∈ IBb b →
      Filter.Tendsto (fun n => normb b fun x => vn n x - v x) Filter.atTop (nhds 0) → v ∈ IMs

/-- `Z_D := \{\mu \in M_b \mid \int [v(x)-\beta\int v(x')Q(dx'|x,a)]\,\mu(d(x,a)) = \int v\,dp
\text{ for all } v \in IM\}` (Bäuerle–Rieder, p. 215, PDF 227), the feasible set of the dual
program `(D)`. -/
def ZD (M : MarkovDecisionModel E A) (b : E → ℝ) (IMs : Set (E → ℝ)) (p : Measure E) :
    Set (Measure (E × A)) :=
  {μ ∈ Mb M b | ∀ v ∈ IMs,
    ∫ xa, (v xa.1 - M.β * ∫ x', v x' ∂(M.Q xa)) ∂μ = ∫ x, v x ∂p}

/-- `val(P) := \inf_{v \in Z_P} \int v\,dp` (Bäuerle–Rieder, p. 215, PDF 227). `EReal`-valued (not
`ℝ`, whose total `sInf`/`sSup` would trivialize the finiteness half of Theorem 7.5.6's own
conclusion by construction), so `-\infty < \mathrm{val}(D)` and `\mathrm{val}(P) < \infty` remain
genuine, non-vacuous claims. -/
noncomputable def valP (M : MarkovDecisionModel E A) (IMs : Set (E → ℝ)) (p : Measure E) : EReal :=
  ⨅ v ∈ ZP M IMs, ((∫ x, v x ∂p : ℝ) : EReal)

/-- `val(D) := \sup_{\mu \in Z_D} \int r\,d\mu` (Bäuerle–Rieder, p. 215, PDF 227), `EReal`-valued
for the same reason as `valP`. -/
noncomputable def valD (M : MarkovDecisionModel E A) (b : E → ℝ) (IMs : Set (E → ℝ))
    (p : Measure E) : EReal :=
  ⨆ μ ∈ ZD M b IMs p, ((∫ xa, M.r xa ∂μ : ℝ) : EReal)

/-- A (Markov) policy `\pi ∈ F^∞` is **`p`-optimal** if it maximizes `\pi \mapsto \int
J_\infty^\pi(x)\,p(dx)` over `F^\infty` (Bäuerle–Rieder, p. 214, PDF 226). -/
def IsPOptimal (M : MarkovDecisionModel E A) (p : Measure E) (π : ℕ → E → A) : Prop :=
  IsPolicyOf M π ∧ ∀ π' : ℕ → E → A, IsPolicyOf M π' →
    erealIntegral p (fun x => Jinfpi M M.r π' x) ≤ erealIntegral p (fun x => Jinfpi M M.r π x)

end MDPFinance.LPDuality


