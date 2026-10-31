-- Prove2me | Definitions.Def_AdviceBonus_Model
-- name    : AdviceBonus_Model
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T19:44:00.149007+00:00
-- url     : https://prove2.me/theorems/7bf3cb17-d154-4140-b559-e22630aedca1
-- title:
--   Advice with bonuses: posterior distribution, advice cutoffs (2)–(4), sales probabilities and firm profits (6)
-- statement:
--   Two firms $A$ and $B$ sell only through one advisor. For each of two customers, who arrive one after the other, the advisor holds a posterior belief $q\in[0,1]$ that product $A$ suits the customer.
--
--   **Posterior distribution.** The posteriors are i.i.d. with density $g$ and c.d.f. $G(q)=\int_0^q g(x)\,dx$. The standing assumptions (pp.7, 9) are:
--   1. $g$ is continuous and positive on $[0,1]$;
--   2. $G$ is symmetric around $1/2$: $G(q)=1-G(1-q)$ for $q\in[0,1]$ (in particular $\int_0^1 g=1$);
--   3. the hazard rate $g(q)/[1-G(q)]$ is increasing on $[0,1)$.
--
--   **Compensation and cutoffs.** Firm $n$ offers a commission $f_n$ and a bonus $b_n$: it pays $f_n$ for one sale and $2f_n+b_n$ for two. The advisor's liability is $w=w_h-w_l>0$, and she earns $qw$ (net of $w_l$) from recommending $A$ and $(1-q)w$ from recommending $B$. After a first sale of $A$, respectively $B$, she recommends $A$ to the second customer exactly when $q_2$ exceeds
--   $$
--   \bar q^A_2=\Big[\tfrac12-\frac{f_A-f_B+b_A}{2w}\Big]_0^1,\qquad \bar q^B_2=\Big[\tfrac12-\frac{f_A-f_B-b_B}{2w}\Big]_0^1, \qquad(2),(3)
--   $$
--   where $[t]_0^1=\max\{0,\min\{1,t\}\}$ (footnote 19). Her continuation payoffs after a first recommendation of $A$, respectively $B$, are
--   $$
--   Z^A=\int_0^{\bar q^A_2}(f_B+(1-q)w)g(q)\,dq+\int_{\bar q^A_2}^1(f_A+b_A+qw)g(q)\,dq,
--   $$
--   $$
--   Z^B=\int_0^{\bar q^B_2}(f_B+b_B+(1-q)w)g(q)\,dq+\int_{\bar q^B_2}^1(f_A+qw)g(q)\,dq,
--   $$
--   and the first customer's cutoff is
--   $$
--   \bar q_1=\Big[\tfrac12-\frac{f_A-f_B+Z^A-Z^B}{2w}\Big]_0^1. \qquad(4)
--   $$
--
--   **Sales and profits** (p.13). With
--   $$
--   \Pr(1)=G(\bar q_1)[1-G(\bar q^B_2)]+[1-G(\bar q_1)]G(\bar q^A_2),\quad \Pr_A(2)=[1-G(\bar q_1)][1-G(\bar q^A_2)],\quad \Pr_B(2)=G(\bar q_1)G(\bar q^B_2),
--   $$
--   firm $n$ sells $S_n=\Pr(1)+2\Pr_n(2)$ units in expectation and, at the common price $p$ and unit cost $c$, earns
--   $$
--   \pi_n=S_n(p-c-f_n)-\Pr_n(2)\,b_n. \qquad(6)
--   $$
--
--   These are the primitives of every statement of the mission.
--
--   **Formalization Note** A scheme is a pair $(f,b)\in\mathbb R^2$. The constant $w_l$ is dropped from every advisor payoff: it shifts both payoffs of each comparison equally and cancels from (2)–(4). The cutoff $\bar q_1$ is clamped to $[0,1]$ like $\bar q^A_2$ (the paper states no corner convention for it). $G$ is the oriented integral $\int_0^q g$; it is only evaluated on $[0,1]$.
-- source:
--   Honda–Inderst–Ottaviani, When Liability is Not Enough, SSRN 4125013 (May 2022), §2, pp.7–9 (density, symmetry, hazard rate); §3, eqs. (2), (3) with footnote 19, p.10; Z^A, Z^B and eq. (4), p.11; Pr(1), Pr_n(2), S_n and eq. (6), p.13

import Mathlib

namespace AdviceBonus

/-!
Honda, Inderst, Ottaviani, *When Liability is Not Enough: Regulating Bonus Payments in Markets
With Advice*, SSRN 4125013 (May 2022 version), §2 (pp.7–9) and §3 (pp.10–13).

The model primitives: the distribution of the advisor's posterior, the advisor's advice cutoffs
(2), (3), (4) with the continuation payoffs `Z^A`, `Z^B` (p.11), the sales probabilities and the
firm profits (6) (p.13).

Conventions used throughout:
* a firm's compensation scheme is a pair `s = (f, b) : ℝ × ℝ` (commission `f = s.1`, bonus
  `b = s.2`), so that `F(1) = f`, `F(2) = 2f + b` (p.8); `sA` is firm A's scheme, `sB` firm B's;
* `w` is the liability `w = w_h − w_l`; the paper's `w_l` is dropped: it adds the same constant
  to every payoff the advisor compares, so it cancels from (2), (3), (4) and from `Z^A − Z^B`;
* all cutoffs are clamped to `[0, 1]` (footnote 19, p.10, for `q̄^A_2`; the same convention for
  `q̄^B_2` and `q̄_1`).
-/

/-- The cumulative distribution function `G(q) = ∫₀^q g` of a density `g` (p.7). Only its values
on `[0, 1]` are ever used: every cutoff of the model lies in `[0, 1]`.

**Formalization Note** For `q < 0` this oriented integral is `−∫_q^0 g`, not `0`; no statement of
the mission evaluates `G` outside `[0, 1]`. -/
noncomputable def cdf (g : ℝ → ℝ) (q : ℝ) : ℝ := ∫ x in (0 : ℝ)..q, g x

/-- The distribution of the advisor's posterior belief `q = Pr(θ = A)` about a customer, §2,
pp.7 and 9. The posterior has density `g > 0` on `[0, 1]` and c.d.f. `G(q) = ∫₀^q g`;
`G` is symmetric around `1/2`, `G(q) = 1 − G(1 − q)` (p.9), and the hazard rate
`g(q)/[1 − G(q)]` is increasing (p.9).

**Formalization Note** `g` is continuous on `[0, 1]` (a reading: the proof of Lemma 3, p.35, uses
the intermediate value theorem). The hazard rate is undefined at `q = 1`, so monotonicity is
required on `[0, 1)`, and "increasing" is read weakly (`MonotoneOn`). `∫₀¹ g = 1` is not a separate
field: it is the symmetry at `q = 0` (`G(0) = 0`). Values of `g` outside `[0, 1]` play no role. -/
structure Dist where
  /-- the density `g` of the posterior -/
  g : ℝ → ℝ
  continuousOn : ContinuousOn g (Set.Icc 0 1)
  pos : ∀ q ∈ Set.Icc (0 : ℝ) 1, 0 < g q
  symm : ∀ q ∈ Set.Icc (0 : ℝ) 1, cdf g q = 1 - cdf g (1 - q)
  hazard : MonotoneOn (fun q => g q / (1 - cdf g q)) (Set.Ico 0 1)

/-- The c.d.f. `G` of a posterior distribution. -/
noncomputable def Dist.G (D : Dist) (q : ℝ) : ℝ := cdf D.g q

/-- Clamping to the unit interval, `max 0 (min 1 t)` (footnote 19, p.10). -/
def clamp01 (t : ℝ) : ℝ := max 0 (min 1 t)

/-- The advice cutoff (2), p.10, for the second customer after product A was sold to the first:
`q̄^A_2 = 1/2 − (f_A − f_B + b_A)/(2w)`, clamped to `[0, 1]` as in footnote 19 (`q̄^A_2 = 0` if
`w ≤ f_A − f_B + b_A`, `q̄^A_2 = 1` if `w ≤ −(f_A − f_B + b_A)`). It is the point where the
advisor's payoffs `f_A + b_A + q w` (recommend A) and `f_B + (1 − q) w` (recommend B) cross. -/
noncomputable def q2A (w : ℝ) (sA sB : ℝ × ℝ) : ℝ :=
  clamp01 (1 / 2 - (sA.1 - sB.1 + sA.2) / (2 * w))

/-- The advice cutoff (3), p.10, for the second customer after product B was sold to the first:
`q̄^B_2 = 1/2 − (f_A − f_B − b_B)/(2w)`, clamped to `[0, 1]` like (2). It is the point where the
advisor's payoffs `f_A + q w` (recommend A) and `f_B + b_B + (1 − q) w` (recommend B) cross. -/
noncomputable def q2B (w : ℝ) (sA sB : ℝ × ℝ) : ℝ :=
  clamp01 (1 / 2 - (sA.1 - sB.1 - sB.2) / (2 * w))

/-- The advisor's expected continuation payoff after advising the first customer to buy A, p.11:
`Z^A = ∫₀^{q̄^A_2} (f_B + (1 − q) w) g(q) dq + ∫_{q̄^A_2}^1 (f_A + b_A + q w) g(q) dq`
(the paper's `+ w_l` in both integrands is dropped; it cancels in (4)). -/
noncomputable def ZA (D : Dist) (w : ℝ) (sA sB : ℝ × ℝ) : ℝ :=
  (∫ q in (0 : ℝ)..q2A w sA sB, (sB.1 + (1 - q) * w) * D.g q) +
    ∫ q in q2A w sA sB..1, (sA.1 + sA.2 + q * w) * D.g q

/-- The advisor's expected continuation payoff after advising the first customer to buy B, p.11
(defined there in words as the mirror image of `Z^A`):
`Z^B = ∫₀^{q̄^B_2} (f_B + b_B + (1 − q) w) g(q) dq + ∫_{q̄^B_2}^1 (f_A + q w) g(q) dq`. -/
noncomputable def ZB (D : Dist) (w : ℝ) (sA sB : ℝ × ℝ) : ℝ :=
  (∫ q in (0 : ℝ)..q2B w sA sB, (sB.1 + sB.2 + (1 - q) * w) * D.g q) +
    ∫ q in q2B w sA sB..1, (sA.1 + q * w) * D.g q

/-- The advice cutoff (4), p.11, for the first customer:
`q̄_1 = 1/2 − (f_A − f_B + Z^A − Z^B)/(2w)`, the point where `f_A + q w + Z^A` (recommend A) and
`f_B + (1 − q) w + Z^B` (recommend B) cross.

**Formalization Note** Clamped to `[0, 1]` like footnote 19 (a reading; the paper states no corner
convention for `q̄_1`). -/
noncomputable def q1 (D : Dist) (w : ℝ) (sA sB : ℝ × ℝ) : ℝ :=
  clamp01 (1 / 2 - (sA.1 - sB.1 + ZA D w sA sB - ZB D w sA sB) / (2 * w))

/-- `Pr(1)`, p.13: the ex-ante probability that the advisor recommends different products to the
two customers, `G(q̄_1)[1 − G(q̄^B_2)] + [1 − G(q̄_1)] G(q̄^A_2)`. -/
noncomputable def pr1 (D : Dist) (w : ℝ) (sA sB : ℝ × ℝ) : ℝ :=
  D.G (q1 D w sA sB) * (1 - D.G (q2B w sA sB)) + (1 - D.G (q1 D w sA sB)) * D.G (q2A w sA sB)

/-- `Pr_A(2) = [1 − G(q̄_1)][1 − G(q̄^A_2)]`, p.13: the probability that A is recommended twice. -/
noncomputable def prA2 (D : Dist) (w : ℝ) (sA sB : ℝ × ℝ) : ℝ :=
  (1 - D.G (q1 D w sA sB)) * (1 - D.G (q2A w sA sB))

/-- `Pr_B(2) = G(q̄_1) G(q̄^B_2)`, p.13: the probability that B is recommended twice. -/
noncomputable def prB2 (D : Dist) (w : ℝ) (sA sB : ℝ × ℝ) : ℝ :=
  D.G (q1 D w sA sB) * D.G (q2B w sA sB)

/-- Expected sales of firm A, `S_A = Pr(1) + 2 Pr_A(2)`, p.13. -/
noncomputable def salesA (D : Dist) (w : ℝ) (sA sB : ℝ × ℝ) : ℝ :=
  pr1 D w sA sB + 2 * prA2 D w sA sB

/-- Expected sales of firm B, `S_B = Pr(1) + 2 Pr_B(2)`, p.13. -/
noncomputable def salesB (D : Dist) (w : ℝ) (sA sB : ℝ × ℝ) : ℝ :=
  pr1 D w sA sB + 2 * prB2 D w sA sB

/-- Firm A's profit (6), p.13, at the common price `p` and unit cost `c` (§4 takes `p_n = p` as
given, p.16; `c_n = c`, p.9): `π_A = S_A (p − c − f_A) − Pr_A(2) b_A`. -/
noncomputable def profitA (D : Dist) (p c w : ℝ) (sA sB : ℝ × ℝ) : ℝ :=
  salesA D w sA sB * (p - c - sA.1) - prA2 D w sA sB * sA.2

/-- Firm B's profit (6), p.13: `π_B = S_B (p − c − f_B) − Pr_B(2) b_B`. -/
noncomputable def profitB (D : Dist) (p c w : ℝ) (sA sB : ℝ × ℝ) : ℝ :=
  salesB D w sA sB * (p - c - sB.1) - prB2 D w sA sB * sB.2

end AdviceBonus


