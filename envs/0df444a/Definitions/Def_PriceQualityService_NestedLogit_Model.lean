-- Prove2me | Definitions.Def_PriceQualityService_NestedLogit_Model
-- name    : PriceQualityService_NestedLogit_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-09T17:26:47.937295+00:00
-- url     : https://prove2.me/theorems/7f58b68f-3817-40b6-876e-b5022c1a76db
-- title:
--   §4, pp. 17–19 — the two-stage nested logit model: nests, choice probabilities $d_x$, $d_{i|x}$, $d_{xi}$ and the profit $\Pi_M(\mathbf p,\mathbf q)$ of (9)
-- statement:
--   This file sets up the two-stage nested logit (NL) model of a firm that sells substitutable products with a service attached, grouped into two **nests** according to their service duration.
--
--   There are two nests $x\in\{s,l\}$ (short and long service). Nest $x$ contains $m_x$ products, indexed $i=1,\dots,m_x$, and every product of nest $x$ comes with the same fixed service duration $t_x\in\mathbb R$. Product $i$ of nest $x$ has quality sensitivity $\alpha_{xi}$, base service cost per unit time $a_{xi}$, marginal effect of quality on service cost $b_{xi}$, production-cost coefficient $c_{xi}$ (production cost $c_{xi}q_{xi}^2$) and service utility per unit time $s_{xi}$. The upper-level scale parameter is $\mu_1$, so the nest coefficient is $1/\mu_1$; the lower-level scale is normalized to $1$. The firm chooses a price $p_{xi}$ and a quality $q_{xi}$ for every product; write $\mathbf p=(\mathbf p_s,\mathbf p_l)$, $\mathbf q=(\mathbf q_s,\mathbf q_l)$.
--
--   The total attractiveness of nest $x$ is
--   $$
--   e_x(\mathbf p_x,\mathbf q_x)=\sum_{i=1}^{m_x}\exp(\alpha_{xi}q_{xi}-p_{xi}+t_xs_{xi}).
--   $$
--   A consumer chooses nest $x$ with probability
--   $$
--   d_x(\mathbf p,\mathbf q)=\frac{e_x(\mathbf p_x,\mathbf q_x)^{1/\mu_1}}{1+e_s(\mathbf p_s,\mathbf q_s)^{1/\mu_1}+e_l(\mathbf p_l,\mathbf q_l)^{1/\mu_1}},
--   $$
--   the remaining probability being the outside (no-purchase) option, and then product $i$ of nest $x$ with conditional probability $d_{i|x}=\exp(\alpha_{xi}q_{xi}-p_{xi}+t_xs_{xi})/e_x(\mathbf p_x,\mathbf q_x)$; the probability of buying product $i$ of nest $x$ is $d_{xi}=d_x\cdot d_{i|x}$. The **markup** of product $i$ of nest $x$ is $p_{xi}-c_{xi}q_{xi}^2-t_x(a_{xi}-b_{xi}q_{xi})$, the average profit of nest $x$ is $r_x=\sum_{i}[p_{xi}-c_{xi}q_{xi}^2-t_x(a_{xi}-b_{xi}q_{xi})]\,d_{i|x}$, and the total expected profit, with the market size normalized to one, is
--   $$
--   \Pi_M(\mathbf p,\mathbf q)=\sum_{x\in\{s,l\}}\sum_{i=1}^{m_x}\bigl[p_{xi}-c_{xi}q_{xi}^2-t_x(a_{xi}-b_{xi}q_{xi})\bigr]\cdot d_{xi}(\mathbf p,\mathbf q).
--   $$
--
--   These objects are the model of Theorem 4 and of every milestone of this mission. The paper derives the choice probabilities from Gumbel random utilities (Ben-Akiva 1973, McFadden 1980); here the closed forms are the model.
--
--   **Formalization Note.** The nests are a two-element type `Nest` with constructors `s` and `l`; the products of nest $x$ are `Fin (m x)`, 0-based. A nest may be empty: then $e_x=0$ and, since $1/\mu_1\neq 0$, $e_x^{1/\mu_1}=0$ (`Real.rpow`), so the empty nest is never chosen. Prices and qualities are unconstrained real numbers. The durations $t_s,t_l$ are data, not decisions, and no order between them is assumed.
-- source:
--   Wang, Ke & Cui, Product Price, Quality and Service Decisions under Consumer Choice Models, accepted manuscript (SSRN 3766191), pp. 17–19, §4 (choice probabilities p. 18, equation (9) p. 18, markup p. 19); Online Supplement p. 5 (average profit r_x)

import Mathlib

namespace PriceQualityService.NestedLogit

/-- The two nests of §4 (Wang, Ke & Cui, p. 17): `s` groups the products sold with the short
service duration `t_s`, `l` those sold with the long duration `t_l`. -/
inductive Nest
  | s
  | l
  deriving DecidableEq, Repr

/-- The two nests form a finite type, enumerated as `{s, l}`. -/
instance : Fintype Nest :=
  ⟨{Nest.s, Nest.l}, fun x => by cases x <;> simp⟩

/-- Data of the two-stage nested logit model of §4, pp. 17–18.
* `m x` is the number of products in nest `x` (products of nest `x` are `Fin (m x)`, 0-based: the
  paper's product `i` of nest `x` is `⟨i - 1, _⟩`; an empty nest is allowed);
* `t x` is the fixed, pre-determined service duration of every product of nest `x` (data, not a
  decision);
* `μ₁` is the upper-level scale parameter (the nest coefficient is `1/μ₁`; the lower-level scale
  `μ₂` is normalized to `1`);
* `α x i`, `a x i`, `b x i`, `c x i`, `s x i` are the quality sensitivity, base service cost per
  unit time, marginal effect of quality on service cost, production-cost coefficient (cost
  `c_xi q_xi²`) and service utility per unit time of product `i` of nest `x` (§2, pp. 8–9).
No sign conditions are part of the structure; theorems state the ones they use. -/
structure Model where
  m : Nest → ℕ
  t : Nest → ℝ
  μ₁ : ℝ
  α : (x : Nest) → Fin (m x) → ℝ
  a : (x : Nest) → Fin (m x) → ℝ
  b : (x : Nest) → Fin (m x) → ℝ
  c : (x : Nest) → Fin (m x) → ℝ
  s : (x : Nest) → Fin (m x) → ℝ

/-- A vector indexed by the products of both nests: a price vector `p = (p_s, p_l)` or a quality
vector `q = (q_s, q_l)`. Qualities and prices are unconstrained reals. -/
abbrev Vec (M : Model) : Type := (x : Nest) → Fin (M.m x) → ℝ

/-- Attraction `exp(α_xi q_xi − p_xi + t_x s_xi)` of product `i` of nest `x` (p. 18). -/
noncomputable def attraction (M : Model) (p q : Vec M) (x : Nest) (i : Fin (M.m x)) : ℝ :=
  Real.exp (M.α x i * q x i - p x i + M.t x * M.s x i)

/-- Total attractiveness of nest `x`, `e_x(p_x, q_x) = ∑_{i=1}^{m_x} exp(α_xi q_xi − p_xi + t_x s_xi)`
(p. 18). It is `0` for an empty nest. -/
noncomputable def nestAttraction (M : Model) (p q : Vec M) (x : Nest) : ℝ :=
  ∑ i, attraction M p q x i

/-- First-stage probability of choosing nest `x` (p. 18):
`d_x(p, q) = e_x^{1/μ₁} / (1 + e_s^{1/μ₁} + e_l^{1/μ₁})`. The power is `Real.rpow`; every base is
a sum of exponentials, hence `≥ 0`, and an empty nest has `0 ^ (1/μ₁) = 0` for `μ₁ ≠ 0`. The
outside option is the `1 +` of the denominator, not a nest. The paper derives this formula from
Gumbel utilities (Ben-Akiva 1973, McFadden 1980); the derivation is not part of this definition. -/
noncomputable def nestProb (M : Model) (p q : Vec M) (x : Nest) : ℝ :=
  nestAttraction M p q x ^ (1 / M.μ₁) /
    (1 + nestAttraction M p q Nest.s ^ (1 / M.μ₁) + nestAttraction M p q Nest.l ^ (1 / M.μ₁))

/-- Second-stage probability of choosing product `i` given nest `x` (p. 18):
`d_{i|x}(p_x, q_x) = exp(α_xi q_xi − p_xi + t_x s_xi) / ∑_{j=1}^{m_x} exp(α_xj q_xj − p_xj + t_x s_xj)`. -/
noncomputable def condProb (M : Model) (p q : Vec M) (x : Nest) (i : Fin (M.m x)) : ℝ :=
  attraction M p q x i / nestAttraction M p q x

/-- Probability of choosing product `i` of nest `x` (p. 18): `d_xi(p, q) = d_x(p, q) · d_{i|x}(p_x, q_x)`. -/
noncomputable def choiceProb (M : Model) (p q : Vec M) (x : Nest) (i : Fin (M.m x)) : ℝ :=
  nestProb M p q x * condProb M p q x i

/-- Markup (profit margin) of product `i` of nest `x` (p. 19):
`p_xi − c_xi q_xi² − t_x (a_xi − b_xi q_xi)`. -/
def markup (M : Model) (p q : Vec M) (x : Nest) (i : Fin (M.m x)) : ℝ :=
  p x i - M.c x i * q x i ^ 2 - M.t x * (M.a x i - M.b x i * q x i)

/-- Average profit of nest `x` (Online Supplement p. 5):
`r_x = ∑_{i=1}^{m_x} [p_xi − c_xi q_xi² − t_x (a_xi − b_xi q_xi)] d_{i|x}`. -/
noncomputable def nestAvgMarkup (M : Model) (p q : Vec M) (x : Nest) : ℝ :=
  ∑ i, markup M p q x i * condProb M p q x i

/-- Total expected profit (9), p. 18, with market size normalized to one:
`Π_M(p, q) = ∑_{x∈{s,l}} ∑_{i=1}^{m_x} [p_xi − c_xi q_xi² − t_x (a_xi − b_xi q_xi)] · d_xi(p, q)`. -/
noncomputable def profit (M : Model) (p q : Vec M) : ℝ :=
  ∑ x, ∑ i, markup M p q x i * choiceProb M p q x i

end PriceQualityService.NestedLogit


