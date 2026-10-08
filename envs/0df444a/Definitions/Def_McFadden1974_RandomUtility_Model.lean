-- Prove2me | Definitions.Def_McFadden1974_RandomUtility_Model
-- name    : McFadden1974_RandomUtility_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-05T03:27:56.094577+00:00
-- url     : https://prove2.me/theorems/6c44305d-2b48-4dfb-820f-6ed120ae3859
-- title:
--   Equations (2), (12), (13) and translation completeness — the random utility model with i.i.d. shocks
-- statement:
--   This definition bundle fixes the objects of McFadden's random utility characterization of the conditional logit model.
--
--   An individual faces $J \ge 1$ alternatives with **representative utilities** $V_1,\dots,V_J \in \mathbb{R}$ (in the paper $V_j = V(s,x_j)$ depends on the individual's measured attributes $s$ and the alternative's attributes $x_j$) and has utility $U_j = V_j + \varepsilon_j$, where the **taste shocks** $\varepsilon_1,\dots,\varepsilon_J$ are independent and identically distributed with a common law $\mu$ on $\mathbb{R}$ and distribution function $G(t) = \mu((-\infty,t])$. The individual chooses the alternative of highest utility.
--
--   1. **Selection probability (2).** The probability of choosing alternative $i$ is
--   $$
--   P_i = \Pr\big[\varepsilon_j - \varepsilon_i < V_i - V_j \ \text{ for all } j \ne i\big],
--   $$
--   computed under the product law $\mu^{\otimes J}$ of the shocks.
--   2. **Logit formula (12).** $\displaystyle L_i(V) = \frac{e^{V_i}}{\sum_{j=1}^J e^{V_j}}$.
--   3. **The model is logit** when $P_i = L_i(V)$ for every $J \ge 1$, every utility vector $V \in \mathbb{R}^J$ (repeated values allowed) and every $i$.
--   4. **Logit on a universe.** For a utility map $u:X\to\mathbb R$, the logit identity holds on every finite set of distinct alternatives in $X$; different alternatives may have the same utility. This is the quantification in Lemma 2.
--   5. **Extreme value law (13).** $G(\varepsilon) = e^{-e^{-\varepsilon}}$ for all real $\varepsilon$ (the paper's "Weibull (Gnedenko, extreme value)" distribution, today called the standard Gumbel law).
--   6. **Translation completeness.** $\mu$ is translation complete if for every function $h:\mathbb{R}\to\mathbb{R}$ of bounded total variation with $h(t)\to 0$ as $t\to\pm\infty$, the condition $\int h(e+a)\,d\mu(e) = 0$ for all real $a$ implies $h = 0$ outside a Lebesgue-null set.
--
--   These are the objects of Lemmas 1 and 2: Lemma 1 gives logit probabilities for every utility vector; Lemma 2 uses a surjective utility map on an alternative universe.
--
--   **Formalization Note** Alternatives are indexed by `Fin J`, and the model is indexed by the utility vector, so $s$ and $x_j$ enter only through $V$. The event in (2) uses strict inequalities and the definition needs no density: it applies to every law $\mu$. A function of bounded variation on $\mathbb{R}$ is bounded and Borel measurable, so the integrals in translation completeness are genuine.
-- source:
--   McFadden, Conditional Logit Analysis of Qualitative Choice Behavior, in P. Zarembka (ed.), Frontiers in Econometrics, Academic Press (1974), p. 108, Equation (2); p. 110, Equation (12); p. 111, Equation (13) and the definition of translation completeness (PDF pp. 4, 6, 7)

import Mathlib

open MeasureTheory ProbabilityTheory Filter Topology

namespace McFadden1974.RandomUtility

/-! # The random utility model of §I with i.i.d. shocks (definition bundle)

McFadden, *Conditional Logit Analysis of Qualitative Choice Behavior*, in P. Zarembka (ed.),
*Frontiers in Econometrics*, Academic Press (1974), §I, pp. 108, 110–111 (PDF pp. 4, 6–7).

The bundle holds six closely tied objects:
* `selProb` — the selection probability (2) of the random utility model with i.i.d. shocks;
* `logitProb` — the logit formula (12);
* `IsLogit` — "the selection probabilities satisfy (12)", for every utility vector;
* `IsLogitOn` — (12) for the finite subsets of a universe of alternatives;
* `IsExtremeValue` — the extreme value law (13);
* `TranslationComplete` — translation completeness (p. 111).

Throughout, `μ : Measure ℝ` is the common law of the i.i.d. shocks `ε(s, x_j)` and its
cumulative distribution function is `ProbabilityTheory.cdf μ`. -/

/-- **Selection probability, Equation (2)** (p. 108, PDF p. 4):
`P_i = P[ε(s, x_j) − ε(s, x_i) < V(s, x_i) − V(s, x_j) for all j ≠ i]`, for shocks
`ε(s, x_1), …, ε(s, x_J)` that are independently identically distributed with law `μ`
(the hypothesis of Lemmas 1 and 2, pp. 111–112).

Formalization Note: the `J` alternatives are indexed by `Fin J` and enter the model only through
their representative utilities `V j = V(s, x_j)`, so the model is indexed by the utility vector
`V : Fin J → ℝ`; the individual attributes `s` and the alternative attributes `x_j` are absorbed
into `V`. Repeated utility values are allowed. The joint law of `(ε_1, …, ε_J)` is the product
measure `Measure.pi (fun _ => μ)`, which is what "independently identically distributed" means.
The event is the paper's, with **strict** inequalities, rewritten as `V j + e j < V i + e i`.
Unlike Equation (3), this definition needs no density: it applies to every law `μ`.
For `J = 1` the event is an empty conjunction and the probability is `1`. -/
noncomputable def selProb (μ : Measure ℝ) [IsProbabilityMeasure μ] {J : ℕ} (V : Fin J → ℝ)
    (i : Fin J) : ℝ :=
  (Measure.pi (fun _ : Fin J => μ) {e | ∀ j, j ≠ i → V j + e j < V i + e i}).toReal

/-- **The logit formula, Equation (12)** (p. 110, PDF p. 6):
`P(x | s, B) = e^{v(s,x)} / Σ_{y ∈ B} e^{v(s,y)}`, written for the alternative `i` of a set of
`J` alternatives with representative utilities `V j = v(s, x_j)`.

Formalization Note: the denominator is a sum over `Fin J` of positive terms; it is positive
whenever an index `i : Fin J` exists, so the division is genuine. -/
noncomputable def logitProb {J : ℕ} (V : Fin J → ℝ) (i : Fin J) : ℝ :=
  Real.exp (V i) / ∑ j, Real.exp (V j)

/-- **The selection probabilities satisfy Equation (12)** for the random utility model (2) with
i.i.d. shocks of law `μ`: for every number `J` of alternatives, every vector of representative
utilities `V : Fin J → ℝ` and every alternative `i`, `selProb μ V i = logitProb V i`.

Formalization Note: Lemma 1 asserts this universal vector version. Lemma 2 instead uses
`IsLogitOn` below, over the finite subsets of its stated universe. -/
def IsLogit (μ : Measure ℝ) [IsProbabilityMeasure μ] : Prop :=
  ∀ (J : ℕ) (V : Fin J → ℝ) (i : Fin J), selProb μ V i = logitProb V i

/-- **Equation (12) on finite alternative sets in a universe** (Lemma 2, p. 112,
PDF p. 8). The utility map `v : X → ℝ` is the paper's `v(s, ·)` for a fixed
measured-attribute vector `s`. An injective enumeration `x : Fin J → X`
represents a finite set of distinct alternatives. Their utility values may
coincide, as the paper permits. -/
def IsLogitOn (μ : Measure ℝ) [IsProbabilityMeasure μ] {X : Type*}
    (v : X → ℝ) : Prop :=
  ∀ (J : ℕ) (x : Fin J → X), Function.Injective x → ∀ i : Fin J,
    selProb μ (fun j => v (x j)) i = logitProb (fun j => v (x j)) i

/-- **The extreme value distribution, Equation (13)** (p. 111, PDF p. 7):
`P(ε(s, x_j) ≤ ε) = e^{−e^{−ε}}` for every real `ε`.

Formalization Note: the paper calls this "the Weibull (Gnedenko, extreme value) distribution";
in current terminology it is the standard Gumbel (type I extreme value) law. It is stated as an
identity of cumulative distribution functions, which determines the law `μ`. -/
def IsExtremeValue (μ : Measure ℝ) [IsProbabilityMeasure μ] : Prop :=
  ∀ e : ℝ, cdf μ e = Real.exp (-Real.exp (-e))

/-- **Translation completeness** (p. 111, PDF p. 7): "A random variable ε is said to be
*translation complete* if for a function h of bounded absolute variation with h(±∞) = 0, the
condition Eh(ε + a) = 0 for all real a implies h ≡ 0 (except possibly on a set of measure
zero)." Here `ε` has law `μ`, so `E h(ε + a) = ∫ h(e + a) dμ(e)`.

Formalization Note: "bounded absolute variation" is `BoundedVariationOn h Set.univ` (finite total
variation on the whole line); `h(±∞) = 0` is the pair of limits at `atTop` and `atBot`. A function
of bounded variation on `ℝ` is a difference of two bounded monotone functions, hence bounded and
Borel measurable, so each `h(· + a)` is `μ`-integrable and the integrals are genuine (no
integrability hypothesis is needed). "A set of measure zero" is read as a Lebesgue-null set. -/
def TranslationComplete (μ : Measure ℝ) [IsProbabilityMeasure μ] : Prop :=
  ∀ h : ℝ → ℝ, BoundedVariationOn h Set.univ → Tendsto h atTop (𝓝 0) →
    Tendsto h atBot (𝓝 0) → (∀ a : ℝ, ∫ e, h (e + a) ∂μ = 0) → h =ᵐ[volume] 0

end McFadden1974.RandomUtility


