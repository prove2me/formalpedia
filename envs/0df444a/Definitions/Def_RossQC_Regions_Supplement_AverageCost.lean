-- Prove2me | Definitions.Def_RossQC_Regions_Supplement_AverageCost
-- name    : RossQC_Regions_Supplement_AverageCost
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-23T09:00:50.207808+00:00
-- url     : https://prove2.me/theorems/d91acf93-21ca-4e08-9edf-46c1691d0bb7
-- title:
--   §2 average-cost objects: f_β(P) = V_β(P) − V_β(P⁰), uniform boundedness and equicontinuity of {f_β}, the pairs (f, g) of (2), average-cost regions
-- statement:
--   This module adds to the general model of Ross's §2 (countably many underlying states, a stochastic transition matrix, bounded costs $C_i, I_i, R_i$, belief simplex $S$, the update $TP$ and the beliefs $e^i$) the objects of the paper's average-cost discussion on pp. 589–590.
--
--   1. **Varying the discount.** For $b\in\mathbb R$, the model with discount $b$ is the same model with $\beta$ replaced by $b$; $V_b$ denotes its $\beta$-discounted optimal cost.
--   2. **Relative value.** For a fixed reference belief $P^0\in S$ and a discount $b$,
--   $$
--   f_b(P)=V_b(P)-V_b(P^0).
--   $$
--   3. **Uniform boundedness and equicontinuity.** The family $\{f_b(P):P\in S,\ b\in(0,1)\}$ is *uniformly bounded* if there is $B$ with $|f_b(P)|\le B$ for all $b\in(0,1)$ and $P\in S$, and *equicontinuous* if for every $P\in S$ and $\varepsilon>0$ there is $\delta>0$ such that $|f_b(Q)-f_b(P)|<\varepsilon$ for every $b\in(0,1)$ and every $Q\in S$ with $\sum_i|P_i-Q_i|<\delta$.
--   4. **Limit property.** A function $f$ on beliefs has the limit property if $f(P)=\lim_{r\to\infty}f_{\beta_r}(P)$ for every $P\in S$, along some sequence $\beta_r\in(0,1)$ with $\beta_r\to1$.
--   5. **Average-cost pairs.** A pair $(f,g)$, $f$ a function on beliefs and $g$ a number, is an average-cost pair if $f$ has the limit property, $g=\lim_{\beta\to1^-}(1-\beta)V_\beta(P)$ for every $P\in S$, and the average-cost optimality equation (2) holds:
--   $$
--   g+f(P)=\min\Big\{\sum_i P_iC_i+f(TP);\ \sum_i P_iI_i+\sum_i P_if(e^i);\ \sum_i P_iR_i+f(e^0)\Big\},\qquad P\in S.
--   $$
--   6. **Average-cost regions.** For an action $a$ (produce, inspect, revise), the average-cost optimal region of $a$ is the set of $P\in S$ at which the term of $a$ on the right side of (2) equals $g+f(P)$.
--
--   These are exactly the properties (a)–(b) of the theorem the paper quotes from Ross (1968) on p. 589, and the regions the proof of Theorem 2.2′ describes as "defined by using (2) in the same manner as (1) was used in the β-discount case".
--
--   **Formalization Note** $V_b$ is the base mission's $V_\beta$ (the limit of value iteration from $V^0=0$) of the model with discount $b$. The right side of (2) is the base right side of (1) for the model with $\beta=1$, so (2) carries no discount factor. The paper names no metric on $S$; equicontinuity uses the $\ell^1$ distance $\sum_i|P_i-Q_i|$ (twice the usual total-variation distance). This sum converges for beliefs because $|P_i-Q_i|\le P_i+Q_i$. The paper's clause (a) also calls $f$ bounded; under uniform boundedness this follows from the limit property, so it is not restated.
-- source:
--   Ross, Quality Control under Markovian Deterioration, Management Science 17(9):587–596 (1971), DOI 10.1287/mnsc.17.9.587, p. 589, §2 (definition of f_β, the quoted Theorem (a)–(b), equation (2)); p. 590, proof of Theorem 2.2′ (average-cost regions)

import Mathlib
import Definitions.Def_RossQC_Regions_Model

namespace RossQC.Regions.Supplement

open Filter Topology

variable {ι : Type*}

/-- Ross, *Quality Control under Markovian Deterioration*, Management Science 17(9):587–596 (1971),
DOI 10.1287/mnsc.17.9.587, p. 589, §2: the general model of §2 with its discount factor replaced by
`b`. The paper varies the discount in the average-cost discussion ("`β ∈ (0, 1)`", "`β → 1`");
`(withDiscount M b).Vβ` is the base `V_β` of the published module at discount `b`. -/
def withDiscount (M : Model ι) (b : ℝ) : Model ι :=
  { M with β := b }

/-- The relative value `f_β(P) = V_β(P) − V_β(P⁰)` of p. 589 ("Fix some `P⁰ ∈ S` and let
`f_β(P) = V_β(P) − V_β(P⁰)`"), at discount `b` and reference belief `P⁰`. -/
noncomputable def relValue (M : Model ι) (P₀ : ι → ℝ) (b : ℝ) (P : ι → ℝ) : ℝ :=
  (withDiscount M b).Vβ P - (withDiscount M b).Vβ P₀

/-- The `ℓ¹` distance (twice the usual total-variation distance) `Σ_i |P_i − Q_i|` between two beliefs.

**Formalization Note.** The paper names no metric on `S` in "equicontinuous" (p. 589). This is the
`ℓ¹` distance. Equicontinuity is imposed only for `P, Q ∈ S`; there the family
`|P_i − Q_i|` is summable, since it is dominated by `P_i + Q_i`. Off `S`, the `tsum`
may return its default value; no statement uses that value. -/
noncomputable def l1dist (P Q : ι → ℝ) : ℝ :=
  ∑' i, |P i - Q i|

/-- The hypothesis of the quoted Theorem, of Lemma 2.1′ and of Theorem 2.2′ (p. 589):
"`{f_β(P) : P ∈ S, β ∈ (0, 1)}` is a uniformly bounded equicontinuous family of functions".

1. **Uniformly bounded:** one bound `B` with `|f_b(P)| ≤ B` for every `b ∈ (0, 1)` and `P ∈ S`.
2. **Equicontinuous:** at every `P ∈ S`, for every `ε > 0` one `δ > 0` serves every discount
   `b ∈ (0, 1)`: `Σ_i |P_i − Q_i| < δ` and `Q ∈ S` imply `|f_b(Q) − f_b(P)| < ε`. -/
def UnifBddEquicont [Countable ι] (M : Model ι) (P₀ : ι → ℝ) : Prop :=
  (∃ B : ℝ, ∀ b ∈ Set.Ioo (0 : ℝ) 1, ∀ P ∈ M.simplex, |relValue M P₀ b P| ≤ B) ∧
  (∀ P ∈ M.simplex, ∀ ε > 0, ∃ δ > 0, ∀ b ∈ Set.Ioo (0 : ℝ) 1, ∀ Q ∈ M.simplex,
    l1dist P Q < δ → |relValue M P₀ b Q - relValue M P₀ b P| < ε)

/-- Clause (b), second half, of the Theorem quoted on p. 589: "for some sequence `β_r → 1`,
`f(P) = lim_{r→∞} f_{β_r}(P)`" for all `P ∈ S`. The discounts `β_r` lie in `(0, 1)`. -/
def IsRelValueLimit [Countable ι] (M : Model ι) (P₀ : ι → ℝ) (f : (ι → ℝ) → ℝ) : Prop :=
  ∃ βs : ℕ → ℝ, (∀ r, βs r ∈ Set.Ioo (0 : ℝ) 1) ∧ Tendsto βs atTop (𝓝 1) ∧
    ∀ P ∈ M.simplex, Tendsto (fun r => relValue M P₀ (βs r) P) atTop (𝓝 (f P))

/-- A pair `(f, g)` as provided by the Theorem quoted on p. 589 (Ross [1968]):

* (a) `g + f(P) = min{Σ P_iC_i + f(TP); Σ P_iI_i + Σ P_if(e^i); Σ P_iR_i + f(e⁰)}` for `P ∈ S`
  (equation (2)); the right side is the base `rhs`/`bellman` of the model with `β := 1`;
* (b) `g = lim_{β→1} (1 − β)V_β(P)` for every `P ∈ S` (the limit from below, `β ∈ (0, 1)`), and
  `f(P) = lim_r f_{β_r}(P)` along some sequence `β_r → 1` (`IsRelValueLimit`).

**Formalization Note.** Clause (a) also calls `f` bounded. Under `UnifBddEquicont` this is implied by
the pointwise limit in (b) (`|f| ≤ B` on `S`), so it is not restated. The existence of such a pair is
the cited theorem's content and is not asserted here. -/
def IsAvgCostPair [Countable ι] (M : Model ι) (P₀ : ι → ℝ) (f : (ι → ℝ) → ℝ) (g : ℝ) : Prop :=
  (∀ P ∈ M.simplex, g + f P = (withDiscount M 1).bellman f P) ∧
  (∀ P ∈ M.simplex,
    Tendsto (fun b => (1 - b) * (withDiscount M b).Vβ P) (𝓝[<] (1 : ℝ)) (𝓝 g)) ∧
  IsRelValueLimit M P₀ f

/-- The average-cost optimal region of the action `a` for the pair `(f, g)`: the beliefs `P ∈ S` at
which `a` attains the minimum in (2), i.e. `g + f(P)` equals the right side of (2) for `a`. This is
"defined by using (2) in the same manner as (1) was used in the β-discount case" (proof of
Theorem 2.2′, p. 590), cf. the base `Model.region`. -/
def acRegion (M : Model ι) (f : (ι → ℝ) → ℝ) (g : ℝ) (a : Action) : Set (ι → ℝ) :=
  {P | P ∈ M.simplex ∧ g + f P = (withDiscount M 1).rhs f P a}

/-- The average-cost optimal inspect region `{P ∈ S : g + f(P) = Σ P_iI_i + Σ P_if(e^i)}`. -/
def acInspectRegion (M : Model ι) (f : (ι → ℝ) → ℝ) (g : ℝ) : Set (ι → ℝ) :=
  acRegion M f g .inspect

/-- The average-cost optimal revise region `{P ∈ S : g + f(P) = Σ P_iR_i + f(e⁰)}`. -/
def acReviseRegion (M : Model ι) (f : (ι → ℝ) → ℝ) (g : ℝ) : Set (ι → ℝ) :=
  acRegion M f g .revise

end RossQC.Regions.Supplement


