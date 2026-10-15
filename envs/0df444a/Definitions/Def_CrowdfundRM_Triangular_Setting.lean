-- Prove2me | Definitions.Def_CrowdfundRM_Triangular_Setting
-- name    : CrowdfundRM_Triangular_Setting
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-15T06:49:33.862436+00:00
-- url     : https://prove2.me/theorems/94feb3d4-8a2d-4b1d-801a-49cdbe8d23ea
-- title:
--   §3–§5 — the pledging model: parameters, valuation laws, systems (1)–(4), (8)–(10), closed forms (5), (6), (11), (12), n(p,T), (17), π, (18), R_i (22), R_h (27), triangular laws, (34)–(35)
-- statement:
--   This file fixes the deterministic fluid model of a single crowdfunding campaign studied by Zhang, Savin and Veeraraghavan.
--
--   **Parameters.** A campaign $M$ consists of the population $\hat I$ of independent backers, their arrival rate $k$, the backers' time-discounting factor $r$, the arrival rate $\Lambda_h$ of herding backers, their propensity $q$ to pledge, the upper end $\bar v$ of the valuation support $[0,\bar v]$, and the survival functions $\bar F_i = 1 - F_i$ and $\bar F_h = 1 - F_h$ of the valuation laws of independent and herding backers. A function $\bar F$ is a *valuation law on $[0,\bar v]$* if it is non-increasing, takes values in $[0,1]$, equals $1$ on $(-\infty,0)$ and equals $0$ on $[\bar v,\infty)$. The *standing assumptions* are
--   $$\hat I>0,\quad k>0,\quad r>0,\quad \bar v>0,\quad \Lambda_h\ge 0,\quad q\ge 0,$$
--   and both $\bar F_i$ and $\bar F_h$ are valuation laws on $[0,\bar v]$.
--
--   **Pledging dynamics.** Fix a pledge level $p$ and a duration $T\ge0$. A backer arriving at time $t$ with valuation $V$ pledges iff $Ve^{-r(T-t)}\ge p$, which has probability $\bar F(pe^{r(T-t)})$. The independent backers' system (1)–(4) is: $n^p_i$, $n^l_i$, $n_i$ are continuous on $[0,T]$ and, for every $t\in[0,T]$,
--   $$n^p_i(t)=\int_0^t k(\hat I-n_i(s))\,\bar F_i(pe^{r(T-s)})\,ds,\qquad n^l_i(t)=\int_0^t k(\hat I-n_i(s))\,\bigl(1-\bar F_i(pe^{r(T-s)})\bigr)\,ds,\qquad n_i=n^p_i+n^l_i.$$
--   The herding backers' system (8)–(10), driven by the independent pledges $n^p_i$, is: $n^p_h$, $n^l_h$ are continuous on $[0,T]$ and
--   $$n^p_h(t)=\int_0^t \Lambda_h q p\,(n^p_i(s)+n^p_h(s))\,\bar F_h(pe^{r(T-s)})\,ds,\qquad n^l_h(t)=\int_0^t \Lambda_h q p\,(n^p_i(s)+n^p_h(s))\,\bigl(1-\bar F_h(pe^{r(T-s)})\bigr)\,ds.$$
--
--   **Closed forms.** The paper's displays (5), (6), (11) and the corrected (12) are defined as functions of $(p,T,t)$, for instance
--   $$n^p_i(t,p,T)=k\hat I\int_0^t e^{-kx}\bar F_i(pe^{r(T-x)})\,dx,$$
--   $$n^p_h(t,p,T)=\Lambda_h q p\Bigl(k\hat I\int_0^t e^{\Lambda_h q p\int_\tau^t \bar F_h(pe^{r(T-u)})du}\,\bar F_h(pe^{r(T-\tau)})\int_0^\tau e^{-kx}\bar F_i(pe^{r(T-x)})\,dx\,d\tau\Bigr).$$
--   The total number of pledges is $n(p,T)=n^p_i(T,p,T)+n^p_h(T,p,T)$, built from (5) and (11). Separately, (17) is
--   $$k\hat I\Bigl(e^{-kT}\int_0^T e^{kx}\bar F_i(pe^{rx})\,e^{\Lambda_h q p\int_0^x \bar F_h(pe^{ry})dy}\,dx\Bigr).$$
--   The creator's revenue is $\pi(p,T)=p\,n(p,T)$ and the feasible set of problem (18) is
--   $$0<p\le\bar v,\qquad 0\le T\le \tfrac1r\ln(\bar v/p).$$
--   Further, $R_i(p,T)=k\hat I p e^{-kT}\int_0^T e^{kx}\bar F_i(pe^{rx})\,dx$ (22) and $R_h(p,T)=p\int_0^T\bar F_h(pe^{ry})\,dy$ (27).
--
--   **Right-triangular laws** on $[0,\bar v]$: with mode $0$, $\bar F(y)=(1-y/\bar v)^2$ on $[0,\bar v)$; with mode $\bar v$, $\bar F(y)=1-(y/\bar v)^2$ on $[0,\bar v)$; both equal $1$ below $0$ and $0$ from $\bar v$ on.
--
--   **Optimality.** A point is *the unique maximizer* of $f$ on a set $S$ if it lies in $S$, $f$ attains its maximum over $S$ there, and no other point of $S$ attains that value; likewise for pairs $(p,T)$.
--
--   **Constants (34), (35):**
--   $$x^*_0=\tfrac1{16}\Bigl(-1-\sqrt{9-4\sqrt[3]{11}}+2\sqrt{\tfrac92+\sqrt[3]{11}+\tfrac{5}{2\sqrt{9-4\sqrt[3]{11}}}}\Bigr)^2,\qquad x^*_1=\tfrac12\Bigl(1+\sqrt[3]{8-\sqrt{37}}+\sqrt[3]{8+\sqrt{37}}\Bigr).$$
--
--   These objects are shared by every statement of the mission: the model results (Propositions 1–2, Corollary 2, (22)) and the optimization results (Propositions 4, 5, 7).
--
--   **Formalization Note** $\Lambda_h$ is written `Lh`. The probability $\mathbb P(Ve^{-r(T-t)}-p\ge0)$ is written $\bar F(pe^{r(T-t)})$, as the paper does in (11) and (17); it differs from $\mathbb P(V\ge y)$ only at atoms of the law, i.e. at countably many $t$, which the integral form ignores. The systems are stated in integral (Carathéodory) form, because with discontinuous $\bar F$ no classical solution exists. The paper prints (12) without the factor $\Lambda_h q p$ of (9) and with inner upper limits $v$ for the outer variable $u$; the definition uses the corrected display. The positivity $p>0$ in the feasible set, the standing assumptions and the explicit triangular survival functions are not printed on the page and are added as the evident reading. Cube roots are `rpow` with exponent $1/3$ on positive bases.
-- source:
--   Zhang, Savin, Veeraraghavan, Revenue Management in Crowdfunding, SSRN 3065267 (manuscript of May 26, 2021), pp. 7–20, Assumptions 1–2, (1)–(12), (17)–(18), (22), (27), (34)–(35); triangular laws p. 13

import Mathlib

namespace CrowdfundRM.Triangular

/-- The primitives of the crowdfunding model of §3 (Zhang, Savin, Veeraraghavan, SSRN 3065267,
pp. 7–12). Data only; the standing assumptions are `Campaign.Standing`.
* `Ihat` : Î, the population of independent backers (Assumption 1(a));
* `k` : the arrival rate of independent backers (Assumption 1(d));
* `r` : the backers' time-discounting factor (Assumption 1(f));
* `Lh` : Λ_h, the arrival rate of herding backers (ASCII name for Λ_h);
* `q` : the herding backers' propensity to pledge (p. 9);
* `vbar` : v̄, the upper end of the valuation support [0, v̄];
* `Fbi`, `Fbh` : the survival functions F̄_i = 1 − F_i and F̄_h = 1 − F_h of the valuation
  laws of independent and herding backers. -/
structure Campaign where
  Ihat : ℝ
  k : ℝ
  r : ℝ
  Lh : ℝ
  q : ℝ
  vbar : ℝ
  Fbi : ℝ → ℝ
  Fbh : ℝ → ℝ

/-- `Fb` is the survival function F̄ = 1 − F of a law on the finite support [0, v̄]
(Assumptions 1(b), 2(b)): antitone, [0, 1]-valued, equal to 1 below 0 and to 0 from v̄ on. -/
def IsValLaw (vbar : ℝ) (Fb : ℝ → ℝ) : Prop :=
  Antitone Fb ∧ (∀ y, 0 ≤ Fb y ∧ Fb y ≤ 1) ∧ (∀ y, y < 0 → Fb y = 1) ∧
    (∀ y, vbar ≤ y → Fb y = 0)

/-- The standing assumptions, implicit on the page: Î, k, r, v̄ > 0, Λ_h, q ≥ 0, and both
valuation laws live on [0, v̄]. -/
def Campaign.Standing (M : Campaign) : Prop :=
  0 < M.Ihat ∧ 0 < M.k ∧ 0 < M.r ∧ 0 < M.vbar ∧ 0 ≤ M.Lh ∧ 0 ≤ M.q ∧
    IsValLaw M.vbar M.Fbi ∧ IsValLaw M.vbar M.Fbh

/-- The independent backers' system (1)–(4) on [0, T], in integral form: `ni`, `np`, `nl` are
continuous on [0, T], start at 0, and integrate (1), (2); (3) holds. The probability
ℙ(V_i e^{−r(T−s)} − p ≥ 0) is written F̄_i(p e^{r(T−s)}). -/
def Campaign.IndepSol (M : Campaign) (p T : ℝ) (ni np nl : ℝ → ℝ) : Prop :=
  ContinuousOn ni (Set.Icc 0 T) ∧ ContinuousOn np (Set.Icc 0 T) ∧
    ContinuousOn nl (Set.Icc 0 T) ∧
    ∀ t ∈ Set.Icc 0 T,
      np t = ∫ s in (0:ℝ)..t, M.k * (M.Ihat - ni s) * M.Fbi (p * Real.exp (M.r * (T - s))) ∧
      nl t = ∫ s in (0:ℝ)..t,
        M.k * (M.Ihat - ni s) * (1 - M.Fbi (p * Real.exp (M.r * (T - s)))) ∧
      ni t = np t + nl t

/-- The herding backers' system (8)–(10) on [0, T], in integral form, driven by the independent
pledges `np`: `nhp`, `nhl` are continuous on [0, T], start at 0, and integrate (8), (9). -/
def Campaign.HerdSol (M : Campaign) (p T : ℝ) (np nhp nhl : ℝ → ℝ) : Prop :=
  ContinuousOn nhp (Set.Icc 0 T) ∧ ContinuousOn nhl (Set.Icc 0 T) ∧
    ∀ t ∈ Set.Icc 0 T,
      nhp t = ∫ s in (0:ℝ)..t,
        M.Lh * M.q * p * (np s + nhp s) * M.Fbh (p * Real.exp (M.r * (T - s))) ∧
      nhl t = ∫ s in (0:ℝ)..t,
        M.Lh * M.q * p * (np s + nhp s) * (1 - M.Fbh (p * Real.exp (M.r * (T - s))))

/-- (5): n^p_i(t, p, T) = k Î ∫_0^t e^{−kx} F̄_i(p e^{r(T−x)}) dx. -/
noncomputable def Campaign.npi (M : Campaign) (p T t : ℝ) : ℝ :=
  M.k * M.Ihat * ∫ x in (0:ℝ)..t, Real.exp (-M.k * x) * M.Fbi (p * Real.exp (M.r * (T - x)))

/-- (6): n^l_i(t, p, T) = k Î ∫_0^t e^{−kx} F_i(p e^{r(T−x)}) dx, with F_i = 1 − F̄_i. -/
noncomputable def Campaign.nli (M : Campaign) (p T t : ℝ) : ℝ :=
  M.k * M.Ihat *
    ∫ x in (0:ℝ)..t, Real.exp (-M.k * x) * (1 - M.Fbi (p * Real.exp (M.r * (T - x))))

/-- (11): n^p_h(t, p, T). -/
noncomputable def Campaign.nph (M : Campaign) (p T t : ℝ) : ℝ :=
  M.Lh * M.q * p * (M.k * M.Ihat * ∫ τ in (0:ℝ)..t,
    Real.exp (M.Lh * M.q * p * ∫ u in τ..t, M.Fbh (p * Real.exp (M.r * (T - u)))) *
      M.Fbh (p * Real.exp (M.r * (T - τ))) *
      ∫ x in (0:ℝ)..τ, Real.exp (-M.k * x) * M.Fbi (p * Real.exp (M.r * (T - x))))

/-- (12), corrected: the printed display lacks the factor Λ_h q p of (9) and writes the inner
upper limits as `v` for the outer variable `u`. -/
noncomputable def Campaign.nlh (M : Campaign) (p T t : ℝ) : ℝ :=
  M.Lh * M.q * p * (M.k * M.Ihat * ∫ u in (0:ℝ)..t,
    (1 - M.Fbh (p * Real.exp (M.r * (T - u)))) *
      ((∫ x in (0:ℝ)..u, Real.exp (-M.k * x) * M.Fbi (p * Real.exp (M.r * (T - x)))) +
        M.Lh * M.q * p * ∫ τ in (0:ℝ)..u,
          Real.exp (M.Lh * M.q * p * ∫ w in τ..u, M.Fbh (p * Real.exp (M.r * (T - w)))) *
            M.Fbh (p * Real.exp (M.r * (T - τ))) *
            ∫ x in (0:ℝ)..τ, Real.exp (-M.k * x) * M.Fbi (p * Real.exp (M.r * (T - x)))))

/-- n(p, T) = n^p_i(T, p, T) + n^p_h(T, p, T) (p. 12, sentence before Corollary 2), built from
(5) and (11). -/
noncomputable def Campaign.ntot (M : Campaign) (p T : ℝ) : ℝ :=
  M.npi p T T + M.nph p T T

/-- (17), Corollary 2's closed form. A separate object from `ntot`. -/
noncomputable def Campaign.nCor2 (M : Campaign) (p T : ℝ) : ℝ :=
  M.k * M.Ihat * (Real.exp (-M.k * T) * ∫ x in (0:ℝ)..T,
    Real.exp (M.k * x) * M.Fbi (p * Real.exp (M.r * x)) *
      Real.exp (M.Lh * M.q * p * ∫ y in (0:ℝ)..x, M.Fbh (p * Real.exp (M.r * y))))

/-- (18): the creator's revenue π(p, T) = p n(p, T). -/
noncomputable def Campaign.revenue (M : Campaign) (p T : ℝ) : ℝ :=
  p * M.ntot p T

/-- The feasible set of (18): 0 < p ≤ v̄, 0 ≤ T ≤ (1/r) ln(v̄/p). (p > 0 is added: ln(v̄/p)
needs it, and π(0, T) = 0.) -/
def Campaign.Feasible (M : Campaign) (p T : ℝ) : Prop :=
  0 < p ∧ p ≤ M.vbar ∧ 0 ≤ T ∧ T ≤ Real.log (M.vbar / p) / M.r

/-- (22): R_i(p, T) = k Î p e^{−kT} ∫_0^T e^{kx} F̄_i(p e^{rx}) dx. -/
noncomputable def Campaign.Ri (M : Campaign) (p T : ℝ) : ℝ :=
  M.k * M.Ihat * p * Real.exp (-M.k * T) *
    ∫ x in (0:ℝ)..T, Real.exp (M.k * x) * M.Fbi (p * Real.exp (M.r * x))

/-- (27): the herding-dominated proxy R_h(p, T) = p ∫_0^T F̄_h(p e^{ry}) dy. -/
noncomputable def Campaign.Rh (M : Campaign) (p T : ℝ) : ℝ :=
  p * ∫ y in (0:ℝ)..T, M.Fbh (p * Real.exp (M.r * y))

/-- Survival function of the right-triangular law on [0, v̄] with mode 0
(density 2(v̄ − v)/v̄²). -/
noncomputable def triBar0 (vbar y : ℝ) : ℝ :=
  if y < 0 then 1 else if y < vbar then (1 - y / vbar) ^ 2 else 0

/-- Survival function of the right-triangular law on [0, v̄] with mode v̄ (density 2v/v̄²). -/
noncomputable def triBar1 (vbar y : ℝ) : ℝ :=
  if y < 0 then 1 else if y < vbar then 1 - (y / vbar) ^ 2 else 0

/-- `x₀` is the unique maximizer of `f` on `S`: it lies in `S`, attains the maximum on `S`, and
is the only point of `S` that does. -/
def IsUniqueMaxOn (f : ℝ → ℝ) (S : Set ℝ) (x₀ : ℝ) : Prop :=
  x₀ ∈ S ∧ (∀ x ∈ S, f x ≤ f x₀) ∧ (∀ x ∈ S, f x = f x₀ → x = x₀)

/-- Two-variable version: `(p₀, T₀)` is the unique maximizer of `f` on `{(p, T) | S p T}`. -/
def IsUniqueMaxOn₂ (f : ℝ → ℝ → ℝ) (S : ℝ → ℝ → Prop) (p₀ T₀ : ℝ) : Prop :=
  S p₀ T₀ ∧ (∀ p T, S p T → f p T ≤ f p₀ T₀) ∧
    (∀ p T, S p T → f p T = f p₀ T₀ → p = p₀ ∧ T = T₀)

/-- (34): x*₀ = (1/16)(−1 − √(9 − 4∛11) + 2√(9/2 + ∛11 + 5/(2√(9 − 4∛11))))². -/
noncomputable def x0 : ℝ :=
  (1 / 16) * (-1 - Real.sqrt (9 - 4 * (11:ℝ) ^ ((1:ℝ) / 3)) +
    2 * Real.sqrt (9 / 2 + (11:ℝ) ^ ((1:ℝ) / 3) +
      5 / (2 * Real.sqrt (9 - 4 * (11:ℝ) ^ ((1:ℝ) / 3))))) ^ 2

/-- (35): x*₁ = (1/2)(1 + ∛(8 − √37) + ∛(8 + √37)). -/
noncomputable def x1 : ℝ :=
  (1 / 2) * (1 + (8 - Real.sqrt 37) ^ ((1:ℝ) / 3) + (8 + Real.sqrt 37) ^ ((1:ℝ) / 3))

end CrowdfundRM.Triangular


