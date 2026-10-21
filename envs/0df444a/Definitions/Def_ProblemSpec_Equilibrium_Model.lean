-- Prove2me | Definitions.Def_ProblemSpec_Equilibrium_Model
-- name    : ProblemSpec_Equilibrium_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-20T09:18:47.678493+00:00
-- url     : https://prove2.me/theorems/89c9215c-2d99-4f49-ad78-709a08fc1ff1
-- title:
--   §3, pp. 5–9, and (A.1)–(A.3), App. p. 1 — crowdsourcing design contest: costs (1), quality (2), logit win probability, symmetric equilibrium, r̄, r̄^g, r∗, m∗, free entry
-- statement:
--   This file fixes the model of a crowdsourcing contest for a design problem (Jiang, Huang & Beil, §3).
--
--   A seeker offers an award $A>0$ and discloses $S_r\ge 0$ **conceptual objectives** and $S_g\ge 0$ **execution guidelines**. Each of $N$ participating designers chooses how many objectives $r_i\ge 0$ to incorporate and how many design trials $m_i>0$ to generate. The primitives are the award $A$, the outside option $s$, the quality weight $w$ of a disclosed objective, the discount $\nu$ of a guessed one, the Gumbel scale $\mu$, the probability $p$ that a sampled concept satisfies one objective, the unit costs $c_1$ (understanding a disclosed objective), $c_g$ (guessing one), $c_2$ (one concept attempt), and the trial cost $c_3=h(S_g)$.
--
--   The **standing assumptions** are $A,w,\mu,c_2>0$, $\nu\in(0,1)$, $0\le c_1<c_g$, $0<p<1$, $s>0$, and $h$ positive and strictly decreasing on $[0,\infty)$.
--
--   1. **Baseline quality** (deterministic part of (2)): $v(r)=rw$ for $r\le S_r$ and $v(r)=S_rw+(r-S_r)\nu w$ for $r>S_r$.
--   2. **Cost** (1): $$C_i(r_i,m_i)=c_g(r_i-S_r)^+ + c_1S_r + c_2(1/p)^{r_i} + h(S_g)\,m_i.$$
--   3. **Win probability** (A.1) of a designer playing $(r_i,m_i)$ against $N-1$ opponents playing $(r,m)$: $$\Pr(i\text{ wins})=\frac{m_i e^{v(r_i)/\mu}}{m_i e^{v(r_i)/\mu}+(N-1)\,m\,e^{v(r)/\mu}},$$ and the participant's **expected utility** is $\Pr(i\text{ wins})\cdot A-C_i(r_i,m_i)$, the $d_i=1$ branch of (3).
--   4. A **symmetric equilibrium** given $N$ is a pair $(r,m)$ with $r\ge0$, $m>0$ such that no deviation $(r_i,m_i)$ with $r_i\ge 0$, $m_i>0$ raises a participant's expected utility when the other $N-1$ play $(r,m)$.
--   5. With $L=\ln(1/p)$, the thresholds of Theorem 1 are $$\bar r=\frac{1}{L}\ln\Big(\frac{N-1}{N^2}\frac{w}{\mu}\frac{A}{c_2}\frac1L\Big),\qquad \bar r^g=\frac1L\ln\Big(\frac{N-1}{N^2}\frac{\nu w}{\mu}\frac{A}{c_2}\frac1L-\frac{c_g}{c_2}\frac1L\Big).$$ Designers **guess** (Region 0) when the argument of the logarithm in $\bar r^g$ is positive and $S_r<\bar r^g$.
--   6. $r^*(N)$ is $\bar r^g$ in Region 0, $S_r$ if $\bar r^g\le S_r\le\bar r$ (Region I), and $\bar r$ if $S_r>\bar r$ (Region II), as in (A.2); $m^*(N)=A(N-1)/(N^2h(S_g))$ as in (A.3).
--   7. The **entry utility** $U(N;S_r)$ is a participant's expected utility when all $N$ play $(r^*(N),m^*(N))$. $N$ is the **free-entry level** $N^*$ when $N>1$, $U(N;S_r)=s$, and $U(N';S_r)<s$ for every $N'>N$ (App. p. 2).
--   8. The closed forms $N_1^*=\sqrt{A/(s+c_1S_r+c_2(1/p)^{S_r})}$ of (A.5) and $N_2^*=(\sqrt{4Y(X+1)+X^2}-X)/(2Y)$ of (A.6), with $X=w/(\mu L)$ and $Y=(s+c_1S_r)/A$.
--
--   Every theorem of the mission is stated in terms of these objects.
--
--   **Formalization Note** All quantities are real numbers, as the paper allows (p. 9: "we allow $N^*$, $r^*$, and $m^*$ to be non-integer numbers"). Four standing assumptions are added or narrowed relative to the page: $0<p<1$ (the page has $p\in[0,1]$, where $(1/p)^r$ and $\ln(1/p)$ degenerate); $s>0$ ((A.6) divides by $Y$); $h>0$ ($m^*$ divides by $c_3$); and "decreasing" is read as strictly decreasing. (A.1) is taken as the definition of the win probability for real $m_i,m$, as the paper does; the milestone (A.1) derives it from Gumbel shocks for integer trial counts. $N^*$ is the free-entry level, never a closed form. The real power $(1/p)^r$ is `Real.rpow`.
-- source:
--   Jiang, Huang & Beil, The Role of Problem Specification in Crowdsourcing Contests for Design Problems, SSRN 3260862 (version of 30 Oct 2019), pp. 5–9 (PDF 5–9), §3, (1)–(3), Theorem 1; and App. pp. 1–2 (PDF 29–30), (A.1)–(A.3), (A.5), (A.6), free-entry condition

import Mathlib

namespace ProblemSpec.Equilibrium

/-! # The crowdsourcing design contest of §3

Jiang, Huang & Beil, *The Role of Problem Specification in Crowdsourcing Contests for Design
Problems*, SSRN 3260862 (version of 30 Oct 2019), §3, pp. 5–9 (PDF 5–9), and Appendix A,
App. pp. 1–2 (PDF 29–30). Every quantity is real: the paper allows `N∗`, `r∗`, `m∗` to be
non-integer (p. 9) and differentiates in `Sr` and `Sg`. -/

/-- The primitives of the model (§3, pp. 5–9): award `A`, outside option (opportunity cost) `s`,
weight `w` of each disclosed conceptual objective, discount `ν` of a guessed objective, Gumbel
scale `μ`, probability `p` that a sampled design concept satisfies one objective, unit costs `c1`
(understanding a disclosed objective), `cg` (guessing an objective), `c2` (one concept attempt),
and the trial-cost function `h`, with `c3 = h(Sg)`. -/
structure Params where
  A : ℝ
  s : ℝ
  w : ℝ
  ν : ℝ
  μ : ℝ
  p : ℝ
  c1 : ℝ
  cg : ℝ
  c2 : ℝ
  h : ℝ → ℝ

/-- Standing assumptions of §3 (pp. 5–9): positive award, weight, Gumbel scale and attempt cost;
`ν ∈ (0,1)` and `cg > c1 ≥ 0` (p. 7); `0 < p < 1` (narrowed from p. 7's `p ∈ [0,1]`, which would
make `(1/p)^r` or `ln(1/p)` degenerate); `s > 0` (added: an opportunity cost); `h` positive and
strictly decreasing on `[0, ∞)` (p. 8: "h(·) is a decreasing function"; positivity added). -/
def Params.Standing (P : Params) : Prop :=
  0 < P.A ∧ 0 < P.w ∧ 0 < P.μ ∧ 0 < P.c2 ∧
  (0 < P.ν ∧ P.ν < 1) ∧ (0 ≤ P.c1 ∧ P.c1 < P.cg) ∧ (0 < P.p ∧ P.p < 1) ∧ 0 < P.s ∧
  (∀ x : ℝ, 0 ≤ x → 0 < P.h x) ∧ StrictAntiOn P.h (Set.Ici 0)

/-- Baseline quality `v(r)` of a design concept incorporating `r` objectives when `Sr` are
disclosed, the deterministic part of (2), p. 8: `r w` for `r ≤ Sr`, `Sr w + (r − Sr) ν w` for
`r > Sr`. -/
noncomputable def quality (P : Params) (Sr r : ℝ) : ℝ :=
  if r ≤ Sr then r * P.w else Sr * P.w + (r - Sr) * P.ν * P.w

/-- Expected cost (1), p. 8: `C(r, m) = cg (r − Sr)⁺ + c1 Sr + c2 (1/p)^r + c3 m`,
`c3 = h(Sg)`; `(1/p)^r` is the real power. -/
noncomputable def cost (P : Params) (Sr Sg r m : ℝ) : ℝ :=
  P.cg * max (r - Sr) 0 + P.c1 * Sr + P.c2 * (1 / P.p) ^ r + P.h Sg * m

/-- Win probability (A.1), App. p. 1 (PDF 29), of a designer choosing `(ri, mi)` against
`N − 1` opponents each choosing `(r, m)`:
`mi e^{v(ri)/μ} / (mi e^{v(ri)/μ} + (N − 1) m e^{v(r)/μ})`. -/
noncomputable def winProb (P : Params) (Sr N ri mi r m : ℝ) : ℝ :=
  mi * Real.exp (quality P Sr ri / P.μ) /
    (mi * Real.exp (quality P Sr ri / P.μ) + (N - 1) * m * Real.exp (quality P Sr r / P.μ))

/-- A participant's expected utility, the `d = 1` branch of (3), p. 9:
`Pr(i wins) · A − C(ri, mi)`. -/
noncomputable def payoff (P : Params) (Sr Sg N ri mi r m : ℝ) : ℝ :=
  winProb P Sr N ri mi r m * P.A - cost P Sr Sg ri mi

/-- `(r, m)` is a symmetric pure-strategy Nash equilibrium of the designers' game among `N`
participants (§3.3, p. 9): `r ≥ 0`, `m > 0`, and no participant gains by any unilateral deviation
`(ri, mi)` with `ri ≥ 0`, `mi > 0` when the other `N − 1` play `(r, m)`. -/
def IsSymEq (P : Params) (Sr Sg N r m : ℝ) : Prop :=
  0 ≤ r ∧ 0 < m ∧
    ∀ ri mi : ℝ, 0 ≤ ri → 0 < mi → payoff P Sr Sg N ri mi r m ≤ payoff P Sr Sg N r m r m

/-- `ln(1/p)`. -/
noncomputable def L (P : Params) : ℝ :=
  Real.log (1 / P.p)

/-- The argument of the logarithm in `r̄` (Theorem 1, p. 9):
`(N−1)/N² · w/μ · A/c2 · 1/ln(1/p)`. -/
noncomputable def rbarArg (P : Params) (N : ℝ) : ℝ :=
  (N - 1) / N ^ 2 * (P.w / P.μ) * (P.A / P.c2) * (1 / L P)

/-- `r̄ = ln((N−1)/N² · w/μ · A/c2 · 1/ln(1/p)) / ln(1/p)` (Theorem 1, p. 9; (A.2)). -/
noncomputable def rbar (P : Params) (N : ℝ) : ℝ :=
  Real.log (rbarArg P N) / L P

/-- The argument of the logarithm in `r̄^g` (Theorem 1, p. 9):
`(N−1)/N² · νw/μ · A/c2 · 1/ln(1/p) − cg/c2 · 1/ln(1/p)`. -/
noncomputable def rgArg (P : Params) (N : ℝ) : ℝ :=
  (N - 1) / N ^ 2 * (P.ν * P.w / P.μ) * (P.A / P.c2) * (1 / L P) - P.cg / P.c2 * (1 / L P)

/-- `r̄^g = ln((N−1)/N² · νw/μ · A/c2 · 1/ln(1/p) − cg/c2 · 1/ln(1/p)) / ln(1/p)`
(Theorem 1, p. 9; (A.2)). -/
noncomputable def rg (P : Params) (N : ℝ) : ℝ :=
  Real.log (rgArg P N) / L P

/-- Region 0 ("Sr < r̄^g", (A.2)): designers guess beyond the disclosed objectives. When the
argument of the logarithm in `r̄^g` is `≤ 0` the formula is undefined and the region is empty. -/
def Guessing (P : Params) (N Sr : ℝ) : Prop :=
  0 < rgArg P N ∧ Sr < rg P N

open Classical in
/-- `r∗(N)` of (A.2), App. p. 1 (PDF 29): `r̄^g` if `Sr < r̄^g` (Region 0), `Sr` if
`r̄^g ≤ Sr ≤ r̄` (Region I), `r̄` if `Sr > r̄` (Region II). -/
noncomputable def rstar (P : Params) (N Sr : ℝ) : ℝ :=
  if Guessing P N Sr then rg P N else if Sr ≤ rbar P N then Sr else rbar P N

/-- `m∗(N) = A (N − 1) / (N² c3)`, `c3 = h(Sg)` ((A.3), App. p. 1). -/
noncomputable def mstar (P : Params) (Sg N : ℝ) : ℝ :=
  P.A * (N - 1) / (N ^ 2 * P.h Sg)

/-- A participant's expected utility `Ui(N; Sr)` when all `N` participants play
`(r∗(N), m∗(N))`. -/
noncomputable def entryUtility (P : Params) (Sr Sg N : ℝ) : ℝ :=
  payoff P Sr Sg N (rstar P N Sr) (mstar P Sg N) (rstar P N Sr) (mstar P Sg N)

/-- `N` is the free-entry number of participants `N∗` (App. p. 2, PDF 30): `N > 1`, the `N`-th
designer's expected utility equals the opportunity cost `s`, and every larger number of
participants gives expected utility below `s`. -/
def IsFreeEntry (P : Params) (Sr Sg N : ℝ) : Prop :=
  1 < N ∧ entryUtility P Sr Sg N = P.s ∧ ∀ N' : ℝ, N < N' → entryUtility P Sr Sg N' < P.s

/-- The closed form `N∗1 = √(A / (s + c1 Sr + c2 (1/p)^{Sr}))` of (A.5), App. p. 1. -/
noncomputable def N1closed (P : Params) (Sr : ℝ) : ℝ :=
  Real.sqrt (P.A / (P.s + P.c1 * Sr + P.c2 * (1 / P.p) ^ Sr))

/-- `X = w / (μ ln(1/p))` of (A.6), App. p. 2. -/
noncomputable def X (P : Params) : ℝ :=
  P.w / (P.μ * L P)

/-- `Y = (s + c1 Sr) / A` of (A.6), App. p. 2. -/
noncomputable def Y (P : Params) (Sr : ℝ) : ℝ :=
  (P.s + P.c1 * Sr) / P.A

/-- The closed form `N∗2 = (√(4Y(X+1) + X²) − X) / (2Y)` of (A.6), App. p. 2. -/
noncomputable def N2closed (P : Params) (Sr : ℝ) : ℝ :=
  (Real.sqrt (4 * Y P Sr * (X P + 1) + X P ^ 2) - X P) / (2 * Y P Sr)

end ProblemSpec.Equilibrium


