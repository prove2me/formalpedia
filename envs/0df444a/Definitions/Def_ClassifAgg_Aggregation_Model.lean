-- Prove2me | Definitions.Def_ClassifAgg_Aggregation_Model
-- name    : ClassifAgg_Aggregation_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-07T03:12:40.818984+00:00
-- url     : https://prove2.me/theorems/f055603d-e747-4e63-aa22-c978e3b36636
-- title:
--   §1, pp. 135–136; §2, pp. 138, 140 — the sample law from (P_X, η), the Bayes set G* = {η ≥ 1/2}, d, d_△, d_△,e and R_n
-- statement:
--   The basic objects of Tsybakov's classification model.
--
--   Observations are i.i.d. pairs $(X_1,Y_1),\dots,(X_n,Y_n)$ with $X_i\in\mathbb R^d$ and $Y_i\in\{0,1\}$. A joint distribution $\pi$ of $(X,Y)$ is described by its design law $P_X$ (the law of $X$) and its regression function $\eta(x)=P(Y=1\mid X=x)$. A classifier is a Borel set $G\subseteq\mathbb R^d$: it predicts $Y=1$ on $G$ and $Y=0$ off $G$.
--
--   1. **Sample law.** $P_{\pi,n}$ is the law of the sample: $n$ independent copies of the pair obtained by drawing $X\sim P_X$ and then $Y\sim\mathrm{Bernoulli}(\eta(X))$.
--   2. **Bayes classifier.** $G^*=G^*_\pi=\{x:\eta(x)\ge 1/2\}$, display (1).
--   3. **Excess risk.** For a classifier $G$,
--   $$d(G,G^*)=\int_{G\triangle G^*}|2\eta(x)-1|\,P_X(dx)=R(G)-R(G^*),$$
--   display (2), where $R(G)=P(Y\ne I(X\in G))$ is the misclassification error.
--   4. **Pseudodistances.** $d_\triangle(G,G')=P_X(G\triangle G')$ (p. 138) and its empirical analogue $d_{\triangle,e}(G,G')=\frac1n\sum_{i=1}^n I(X_i\in G\triangle G')$ (p. 140).
--   5. **Empirical risk.** $R_n(G)=\frac1n\sum_{i=1}^n\big(Y_i-I(X_i\in G)\big)^2$, the fraction of misclassified sample points (p. 136).
--
--   These objects are shared by every statement of the mission: risks are measured through $d$, and the classes and procedures are built from $d_\triangle$, $d_{\triangle,e}$ and $R_n$.
--
--   **Formalization Note** $\mathbb R^d$ is `EuclideanSpace ℝ (Fin d)` with its Borel σ-algebra, and labels are `Bool` with `true` ↔ 1. A distribution is the pair $(P_X,\eta)$; the law of one pair is `UnderstandingML.condLaw PX η` from the published definition `UnderstandingML_NearestNeighbor` (draw $x\sim P_X$, then $y\sim\mathrm{Bernoulli}(\eta(x))$), which is the same object: every law on $\mathbb R^d\times\{0,1\}$ disintegrates this way, so nothing is lost. The sample law is the $n$-fold product measure. $d_\triangle$ is the real value of $P_X(G\triangle G')$, finite since $P_X$ is a probability measure in every statement.
-- source:
--   Tsybakov (2004), Ann. Statist. 32, §1 (1)–(2), pp. 135–136; §2, pp. 138 (d_△), 140 (d_△,e)

import Mathlib
import Definitions.Def_UnderstandingML_NearestNeighbor

namespace ClassifAgg.Aggregation

open MeasureTheory

/-- The feature space `ℝᵈ`, as `EuclideanSpace ℝ (Fin d)` with its Borel σ-algebra. -/
abbrev E (d : ℕ) := EuclideanSpace ℝ (Fin d)

/-- The numerical value of a label: `Y ∈ {0, 1}` is encoded as `Bool`, with `true ↔ 1`. -/
def yval (b : Bool) : ℝ := if b then 1 else 0

/-- The law `P_{π,n}` of an i.i.d. sample `(X₁, Y₁), …, (Xₙ, Yₙ)` from the joint distribution `π`
of `(X, Y)` with design law `P_X` and regression function `η` (Tsybakov 2004, §1, p. 135).

The joint law of one pair is `UnderstandingML.condLaw PX η`: draw `X ∼ P_X`, then
`Y ∼ Bernoulli(η(X))`, with label `true ↔ 1`. For a probability measure `P_X` and a measurable `η`
with values in `[0, 1]` this is the law on `ℝᵈ × {0, 1}` with `X`-marginal `P_X` and
`P(Y = 1 | X = x) = η(x)`; every law on `ℝᵈ × {0, 1}` is of this form. -/
noncomputable def sampleLaw {d : ℕ} (PX : Measure (E d)) (η : E d → ℝ) (n : ℕ) :
    Measure (Fin n → E d × Bool) :=
  Measure.pi (fun _ : Fin n => UnderstandingML.condLaw PX η)

/-- The Bayes classifier `G* = G*_π = {x : η(x) ≥ 1/2}`, display (1), p. 135. -/
def bayesSet {d : ℕ} (η : E d → ℝ) : Set (E d) := {x | 1 / 2 ≤ η x}

/-- The excess risk `d(G, G*) = ∫_{G △ G*} |2η(x) − 1| P_X(dx) = R(G) − R(G*)`, display (2),
p. 136. -/
noncomputable def excess {d : ℕ} (PX : Measure (E d)) (η : E d → ℝ) (G : Set (E d)) : ℝ :=
  ∫ x in symmDiff G (bayesSet η), |2 * η x - 1| ∂PX

/-- The pseudodistance `d_△(G, G') = P_X(G △ G')`, p. 138. -/
noncomputable def dTri {d : ℕ} (PX : Measure (E d)) (G G' : Set (E d)) : ℝ :=
  (PX (symmDiff G G')).toReal

/-- The empirical pseudodistance `d_{△,e}(G, G') = (1/n) ∑ᵢ I(Xᵢ ∈ G △ G')`, p. 140, on the
sample `s = ((X₁, Y₁), …, (Xₙ, Yₙ))`. -/
noncomputable def dTriEmp {d n : ℕ} (s : Fin n → E d × Bool) (G G' : Set (E d)) : ℝ :=
  (1 / (n : ℝ)) * ∑ i, (symmDiff G G').indicator (fun _ => (1 : ℝ)) (s i).1

/-- The empirical risk `Rₙ(G) = (1/n) ∑ᵢ (Yᵢ − I(Xᵢ ∈ G))²`, p. 136. -/
noncomputable def empRisk {d n : ℕ} (s : Fin n → E d × Bool) (G : Set (E d)) : ℝ :=
  (1 / (n : ℝ)) * ∑ i, (yval (s i).2 - G.indicator (fun _ => (1 : ℝ)) (s i).1) ^ 2

end ClassifAgg.Aggregation


