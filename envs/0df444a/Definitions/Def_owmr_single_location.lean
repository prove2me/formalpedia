-- Prove2me | Definitions.Def_owmr_single_location
-- name    : owmr_single_location
-- status  : Definition
-- author  : @Ming Hu
-- created : 2026-11-16T00:53:31.768219+00:00
-- url     : https://prove2.me/theorems/aa975acf-25a7-48a7-a19c-2b8fe9dc5bb3
-- title:
--   Single-location problems, $(s,S)$ policies, canonical optima, mirror cost, $F_i$, $f_{L_0}$
-- statement:
--   **Single-location problem.** Let $\rho$ be a probability law on $[0,\infty)$, $f:\mathbb R\to\mathbb R$ a cost function, and $K$ a setup cost. In each period the position may be raised by $q_t\ge0$, which costs $K$ if $q_t>0$; the post-action position $x_t$ incurs $f(x_t)$, and an i.i.d. demand with law $\rho$ then reduces it. The **single-location value** $\mathcal J_\rho(f;K)$ is the infimum, over all nonanticipative (possibly randomized) policies, of
--
--   $$\limsup_{T\to\infty}\frac1T\,\mathbb E\sum_{t<T}\big[K\mathbf 1_{\{q_t>0\}}+f(x_t)\big].$$
--
--   **$(s,S)$ policies.** Started at pre-action position $S$, the $(s,S)$ policy raises the position to $S$ whenever it is at most $s$; base stock is the case $s=S$. A pair $(\hat s,\hat S)$ is a **canonical optimum** (Lemma 1) if $\hat s<\hat S$, the $(\hat s,\hat S)$ policy attains $J=\mathcal J_\rho(f;K)$, and the canonical conditions (4) hold:
--
--   $$f(\hat s)=J,\qquad f(\hat S)\le J,\qquad f(x)\le J\quad(\hat s\le x\le\hat S).$$
--
--   A **best half window** of $[\hat s,\hat S]$ is a pair $(s,S)$ with $\hat s\le s<S\le\hat S$ and $S-s=(\hat S-\hat s)/2$ whose long-run average holding and backlog cost is smallest among all such pairs.
--
--   **Mirror cost.** With the warehouse-rate loss $\phi(y)=hy^++py^-$, the mirror cost of an $(s,S)$ policy with post-action positions $\widehat P_t$ is $\min_{a\in\mathbb R}\limsup_{T}T^{-1}\,\mathbb E\sum_{t<T}\phi(a-\widehat P_t)$, and a minimizing $a$ is a **mirror center**.
--
--   **Network cost functions.** For retailer $i$ with marginal demand $D_i$, $F_i(y)=\mathbb E[H_i(y-Z_i)^++p(Z_i-y)^+]$, where $Z_i$ is a sum of $L_i+1$ i.i.d. copies of $D_i$, and $J_i(k)=\mathcal J_{D_i}(F_i;k)$ (equation (8)). For aggregate demand $D=\sum_iD_i$, $f_{L_0}(y)=\mathbb E\,\phi(y-D^{(L_0)})$, where $D^{(L_0)}$ is a sum of $L_0$ i.i.d. copies of $D$ ($D^{(0)}=0$), and $J_0(k)=\mathcal J_D(f_{L_0};k)$ (equation (22)). The **augmented cost** of an $(s,S)$ policy for retailer $i$ is its long-run average cost at the actual setup cost $K_i$ plus its mirror cost. The **renewal function** is $M(w)=\sum_{k\ge0}\mathbb P(D^{(k)}<w)$ (equation (9)). The demand vector is **associated** if $\operatorname{Cov}(u(D_t),v(D_t))\ge0$ for all bounded, coordinatewise nondecreasing $u,v$ (Section 6).
--
--   These objects are the building blocks of both policies and both guarantees.
--
--   **Formalization Note** Every long-run average is the limsup of Cesàro averages of expected costs, valued in $[0,\infty]$; where the source writes a limit, the limit exists and equals this limsup. Averages of $(s,S)$ policies start at pre-action position $S$, and $\mathcal J$ starts at position $0$ (the source shows that it does not depend on the initial position). A real cost $f$ enters through $\max(f,0)$; every $f$ used in the mission is nonnegative. $F_i$ and $f_{L_0}$ are Bochner integrals; the canonical conditions compare $\max(f,0)$ with $J$ in $[0,\infty]$. In the association condition, $u$ and $v$ are also required to be measurable, the standard convention.
-- source:
--   M. Hu, "A 5/2 Guarantee for Echelon Stock (s,S) Policies in One-Warehouse Multi-Retailer Systems", working paper (manuscript of November 2026), Section 3 (pp. 7-8: single-location problems, (s,S) policies, mirror cost, augmented cost), Section 4.1 (p. 11: single-location value, Lemma 1 and canonical conditions (4)), equations (8) (p. 12), (9) (p. 12), (14) (p. 15), (22) (p. 21), and Section 6 (p. 27: association).

import Definitions.Def_owmr_network_model

/-!
# Single-location problems, (s,S) policies, and the cost functions of the OWMR paper

Source: M. Hu, "A 5/2 Guarantee for Echelon Stock (s,S) Policies in One-Warehouse
Multi-Retailer Systems": Section 3 (the single-location problems and `(s,S)` policies used by
Definition 1, mirror cost, augmented cost), Section 4.1 (the single-location value `𝒥_D(f;K)`,
Lemma 1 and the canonical conditions (4)), equations (8) (`F_i`, `J_i`), (9) (renewal measure,
`M(w)`), (14) (warehouse-rate loss `φ`, mirror cost), (22) (`f_{L₀}`, `J₀`), and Section 6
(association).
-/

open MeasureTheory
open scoped ENNReal NNReal

noncomputable section

namespace OWMR

variable {n : ℕ}

/-! ## The single-location problem (Section 4.1) -/

/-- A single-location policy with auxiliary randomness `u : U`: the order quantity in period
`t`, as a function of `u` and the demand sequence. -/
abbrev SLPolicy (U : Type) := ℕ → U → (ℕ → ℝ≥0) → ℝ

/-- Post-action position in period `t`, starting from pre-action position `y0` in period `0`:
`x_t = y0 + ∑_{s ≤ t} q_s - ∑_{s < t} D_s`. -/
def slPos {U : Type} (y0 : ℝ) (q : SLPolicy U) (u : U) (d : ℕ → ℝ≥0) (t : ℕ) : ℝ :=
  y0 + ∑ s ∈ Finset.range (t + 1), q s u d - ∑ s ∈ Finset.range t, (d s : ℝ)

/-- Period cost `K 1{q_t > 0} + f(x_t)` of the single-location problem. -/
def slPeriodCost {U : Type} (f : ℝ → ℝ) (K y0 : ℝ) (q : SLPolicy U) (u : U) (d : ℕ → ℝ≥0)
    (t : ℕ) : ℝ :=
  K * (if 0 < q t u d then 1 else 0) + f (slPos y0 q u d t)

/-- Long-run average cost `limsup_T T⁻¹ 𝔼 ∑_{t<T} (K 1{q_t>0} + f(x_t))`, demands i.i.d. with
law `ρ`, auxiliary randomness with law `ν`. -/
def slAvgCost {U : Type} [MeasurableSpace U] (ρ : Measure ℝ≥0) [IsProbabilityMeasure ρ]
    (f : ℝ → ℝ) (K y0 : ℝ) (q : SLPolicy U) (ν : Measure U) : ℝ≥0∞ :=
  Filter.limsup (fun T : ℕ => (T : ℝ≥0∞)⁻¹ *
    ∫⁻ ω, ∑ t ∈ Finset.range T, ENNReal.ofReal (slPeriodCost f K y0 q ω.1 (padHist T ω.2) t)
      ∂(ν.prod (Measure.pi fun _ : Fin T => ρ))) Filter.atTop

/-- Admissible single-location policies: nonanticipative, measurable, nonnegative orders. -/
def SLAdmissible {U : Type} [MeasurableSpace U] (q : SLPolicy U) : Prop :=
  (∀ (t : ℕ) (u : U) (d d' : ℕ → ℝ≥0), (∀ s < t, d s = d' s) → q t u d = q t u d') ∧
  (∀ t : ℕ, Measurable (fun ω : U × (ℕ → ℝ≥0) => q t ω.1 ω.2)) ∧
  (∀ t u d, 0 ≤ q t u d)

/-- The single-location value `𝒥_D(f;K)`: the infimum of the long-run average cost over all
nonanticipative policies (from initial position `0`; by Lemma 1 the value does not depend on the
initial position). -/
def slValue (ρ : Measure ℝ≥0) [IsProbabilityMeasure ρ] (f : ℝ → ℝ) (K : ℝ) : ℝ≥0∞ :=
  ⨅ (U : Type) (_ : MeasurableSpace U) (ν : Measure U) (_ : IsProbabilityMeasure ν)
    (q : SLPolicy U) (_ : SLAdmissible q), slAvgCost ρ f K 0 q ν

/-! ## `(s,S)` policies -/

/-- Pre-action positions of the `(s,S)` policy started at pre-action position `S`: whenever the
position is at most `s` it is raised to `S`, then demand reduces it. -/
def ssPre (s S : ℝ) (d : ℕ → ℝ≥0) : ℕ → ℝ
  | 0 => S
  | t + 1 => (if ssPre s S d t ≤ s then S else ssPre s S d t) - (d t : ℝ)

/-- Post-action position of the `(s,S)` policy in period `t`. -/
def ssPost (s S : ℝ) (d : ℕ → ℝ≥0) (t : ℕ) : ℝ :=
  if ssPre s S d t ≤ s then S else ssPre s S d t

/-- Period cost of the `(s,S)` policy: `K` for a positive order, plus `f` of the post-action
position. -/
def ssPeriodCost (f : ℝ → ℝ) (K s S : ℝ) (d : ℕ → ℝ≥0) (t : ℕ) : ℝ :=
  K * (if ssPre s S d t ≤ s ∧ ssPre s S d t < S then 1 else 0) + f (ssPost s S d t)

/-- Long-run average cost of the `(s,S)` policy started at `S` (setup cost `K` per order).
With `K = 0` this is its long-run average holding and backlog cost. -/
def ssAvgCost (ρ : Measure ℝ≥0) [IsProbabilityMeasure ρ] (f : ℝ → ℝ) (K s S : ℝ) : ℝ≥0∞ :=
  Filter.limsup (fun T : ℕ => (T : ℝ≥0∞)⁻¹ *
    ∫⁻ z, ∑ t ∈ Finset.range T, ENNReal.ofReal (ssPeriodCost f K s S (padHist T z) t)
      ∂(Measure.pi fun _ : Fin T => ρ)) Filter.atTop

/-- `(s,S)` is a canonical optimum (Lemma 1): `s < S`, the `(s,S)` policy is optimal (its average
cost started at `S` equals `J = 𝒥_D(f;K)`), and the canonical conditions (4) hold:
`f(s) = J`, `f(S) ≤ J`, and `f(x) ≤ J` for `s ≤ x ≤ S`. -/
def IsCanonicalOptimum (ρ : Measure ℝ≥0) [IsProbabilityMeasure ρ] (f : ℝ → ℝ) (K s S : ℝ) :
    Prop :=
  s < S ∧ ssAvgCost ρ f K s S = slValue ρ f K ∧
    ENNReal.ofReal (f s) = slValue ρ f K ∧ ENNReal.ofReal (f S) ≤ slValue ρ f K ∧
    ∀ y ∈ Set.Icc s S, ENNReal.ofReal (f y) ≤ slValue ρ f K

/-- `(s,S)` has the smallest long-run average holding and backlog cost among the `(s',S')`
policies with `sh ≤ s' < S' ≤ Sh` and `S' - s' = (Sh - sh)/2` (the half windows of
`[sh, Sh]`), and is itself such a policy. -/
def IsBestHalfWindow (ρ : Measure ℝ≥0) [IsProbabilityMeasure ρ] (f : ℝ → ℝ) (sh Sh s S : ℝ) :
    Prop :=
  sh ≤ s ∧ s < S ∧ S ≤ Sh ∧ S - s = (Sh - sh) / 2 ∧
    ∀ s' S' : ℝ, sh ≤ s' → s' < S' → S' ≤ Sh → S' - s' = (Sh - sh) / 2 →
      ssAvgCost ρ f 0 s S ≤ ssAvgCost ρ f 0 s' S'

/-! ## Warehouse-rate loss and mirror cost -/

/-- The warehouse-rate loss `φ(y) = h y⁺ + p y⁻`. -/
def whLoss (h p y : ℝ) : ℝ := h * max y 0 + p * max (-y) 0

/-- Long-run average mirror loss `φ(a - P̂_t)` of the `(s,S)` policy started at `S`, where `P̂_t`
is its post-action position. -/
def mirrorAvg (ρ : Measure ℝ≥0) [IsProbabilityMeasure ρ] (h p s S a : ℝ) : ℝ≥0∞ :=
  Filter.limsup (fun T : ℕ => (T : ℝ≥0∞)⁻¹ *
    ∫⁻ z, ∑ t ∈ Finset.range T, ENNReal.ofReal (whLoss h p (a - ssPost s S (padHist T z) t))
      ∂(Measure.pi fun _ : Fin T => ρ)) Filter.atTop

/-- The mirror cost of the `(s,S)` policy: the minimum over centers `a` of `mirrorAvg`. -/
def mirrorCost (ρ : Measure ℝ≥0) [IsProbabilityMeasure ρ] (h p s S : ℝ) : ℝ≥0∞ :=
  ⨅ a : ℝ, mirrorAvg ρ h p s S a

/-! ## Renewal function (9) -/

/-- `M(w) = U[0,w) = ∑_{k ≥ 0} ℙ(D^{(k)} < w)`, with `D^{(k)}` the sum of `k` i.i.d. demands of
law `ρ` (and `D^{(0)} = 0`). -/
def renewalM (ρ : Measure ℝ≥0) [IsProbabilityMeasure ρ] (w : ℝ) : ℝ≥0∞ :=
  ∑' k : ℕ, (Measure.pi fun _ : Fin k => ρ) {z | ∑ j, (z j : ℝ) < w}

/-! ## Network-level cost functions -/

/-- Marginal law of retailer `i`'s demand `D_i`. -/
def Network.marginal (N : Network n) (i : Fin n) : Measure ℝ≥0 := N.μ.map (fun x => x i)

instance (N : Network n) (i : Fin n) : IsProbabilityMeasure (N.marginal i) :=
  Measure.isProbabilityMeasure_map (measurable_pi_apply i).aemeasurable

/-- Law of aggregate demand `D = ∑_i D_i`. -/
def Network.aggregate (N : Network n) : Measure ℝ≥0 := N.μ.map (fun x => ∑ i, x i)

instance (N : Network n) : IsProbabilityMeasure N.aggregate :=
  Measure.isProbabilityMeasure_map (Finset.measurable_sum _ fun i _ => measurable_pi_apply i).aemeasurable

/-- `F_i(y) = 𝔼[H_i (y - Z_i)⁺ + p (Z_i - y)⁺]` from (8), where `Z_i` is a sum of `L_i + 1`
i.i.d. demands of retailer `i`. -/
def Network.F (N : Network n) (i : Fin n) (y : ℝ) : ℝ :=
  ∫ z, (N.H i * max (y - ∑ j, (z j : ℝ)) 0 + N.p * max (∑ j, (z j : ℝ) - y) 0)
    ∂(Measure.pi fun _ : Fin (N.L i + 1) => N.marginal i)

/-- `J_i(k) = 𝒥_{D_i}(F_i; k)` from (8). -/
def Network.J (N : Network n) (i : Fin n) (k : ℝ) : ℝ≥0∞ :=
  slValue (N.marginal i) (N.F i) k

/-- `f_{L₀}(y) = 𝔼 φ(y - D^{(L₀)})` from (22), where `D^{(L₀)}` is a sum of `L₀` i.i.d. aggregate
demands (`D^{(0)} = 0`). -/
def Network.fL0 (N : Network n) (y : ℝ) : ℝ :=
  ∫ z, whLoss N.h N.p (y - ∑ j, (z j : ℝ)) ∂(Measure.pi fun _ : Fin N.L0 => N.aggregate)

/-- `J₀(k) = 𝒥_D(f_{L₀}; k)` from (22). -/
def Network.J0 (N : Network n) (k : ℝ) : ℝ≥0∞ :=
  slValue N.aggregate N.fL0 k

/-- The augmented cost of the `(s,S)` policy for retailer `i` (Section 3): its long-run average
cost in the single-location problem with actual setup cost `K_i` and lead time `L_i`, plus the
mirror cost of its position. -/
def Network.augCost (N : Network n) (i : Fin n) (s S : ℝ) : ℝ≥0∞ :=
  ssAvgCost (N.marginal i) (N.F i) (N.K i) s S + mirrorCost (N.marginal i) N.h N.p s S

/-- Association of the demand vector within a period (Section 6): `Cov(u(D_t), v(D_t)) ≥ 0`
for all bounded, measurable, coordinatewise nondecreasing `u, v`. -/
def Network.Associated (N : Network n) : Prop :=
  ∀ u v : DemandVec n → ℝ, Measurable u → Measurable v → Monotone u → Monotone v →
    (∃ C, ∀ x, |u x| ≤ C) → (∃ C, ∀ x, |v x| ≤ C) →
      (∫ x, u x ∂N.μ) * (∫ x, v x ∂N.μ) ≤ ∫ x, u x * v x ∂N.μ

end OWMR


