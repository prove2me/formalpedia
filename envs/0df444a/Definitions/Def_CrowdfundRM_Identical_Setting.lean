-- Prove2me | Definitions.Def_CrowdfundRM_Identical_Setting
-- name    : CrowdfundRM_Identical_Setting
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-15T09:07:20.455863+00:00
-- url     : https://prove2.me/theorems/421d26fd-d7a9-4cf5-8517-55b261d26f81
-- title:
--   §3–§5 — the crowdfunding pledging model: parameters, closed forms (5) and (11), n(p,T), π and problem (18), identical valuations (58)–(59), Proposition 6's feasible set, constants (32)–(33)
-- statement:
--   This file sets up the deterministic fluid model of a single crowdfunding campaign from Zhang, Savin and Veeraraghavan, *Revenue Management in Crowdfunding*, §3, specialised to the objects needed for the case where every backer of a given type values the project equally.
--
--   **Parameters.** A campaign has a population $\hat I$ of independent backers, who arrive at rate $k$ in proportion to the number still to come; backers discount the project's value at rate $r$ between their arrival and the campaign's end; herding backers arrive at rate $\Lambda_h$ and pledge with propensity $q$ in proportion to the pledges collected so far. Valuations live on the support $[0,\bar v]$. The valuation laws of independent and herding backers enter only through their survival functions $\bar F_i = 1-F_i$ and $\bar F_h = 1-F_h$. A function $\bar F$ is admissible when it is nonincreasing, takes values in $[0,1]$, equals $1$ on $(-\infty,0)$ and equals $0$ on $[\bar v,\infty)$. The standing assumptions are $\hat I,k,r,\bar v>0$, $\Lambda_h,q\ge 0$ and admissibility of both survival functions.
--
--   **Pledge counts.** For a pledge level $p$, a duration $T$ and a time $t$, the numbers of pledging independent and herding backers are the closed forms (5) and (11) of Propositions 1 and 2:
--
--   $$n^p_i(t,p,T)=k\hat I\int_0^t e^{-kx}\,\bar F_i\big(pe^{r(T-x)}\big)\,dx,$$
--
--   $$n^p_h(t,p,T)=\Lambda_h q p\,\big(k\hat I\big)\int_0^t d\tau\,e^{\Lambda_h q p\int_\tau^t \bar F_h(pe^{r(T-u)})\,du}\,\bar F_h\big(pe^{r(T-\tau)}\big)\int_0^\tau e^{-kx}\bar F_i\big(pe^{r(T-x)}\big)\,dx.$$
--
--   The total number of pledges is $n(p,T)=n^p_i(T,p,T)+n^p_h(T,p,T)$ and the creator's revenue is $\pi(p,T)=p\,n(p,T)$. The creator's problem (18) maximizes $\pi$ over the feasible set $0<p\le\bar v$, $0\le T\le \frac1r\ln(\bar v/p)$.
--
--   **Identical valuations.** When every independent backer values the project at $v_i$ and every herding backer at $v_h$, with $0<v_i\le\bar v$ and $0<v_h\le\bar v$, the laws are the point masses (58)–(59): $\bar F_i(y)=1$ for $y<v_i$ and $0$ for $y\ge v_i$, and likewise for $\bar F_h$ with $v_h$. Proposition 6 restricts problem (18) further by $T\le\frac1r\ln(v_i/p)$.
--
--   **Constants.** For Proposition 6(ii), (32) sets $\delta=\Lambda_h q v_h/r$, $a=k/(\Lambda_h q)$, $b=\Lambda_h q/r$, and (33) sets
--
--   $$X(k,r,\Lambda_h,q,v_h)=e^{bv_h/e}\,\frac1{4a}\Big(\frac kr v_h e^{-2}+0.5\,b v_h^2 e^{-3}+2a+v_h\Big)+\frac1a\Big(\frac kr (v_h+a)+a\Big).$$
--
--   The file also defines the indicator $\mathbb I(x)=1$ for $x\ge0$ and $0$ for $x<0$ of (16), and the predicates "unique maximizer" and "maximizer" used to state optimality.
--
--   **Formalization Note.** $\Lambda_h$ is written `Lh`. Valuation laws are encoded by their survival functions, so (5)'s $1-F_i$ appears as $\bar F_i$. $n(p,T)$ is built from (5) and (11), not from the paper's single formula (17). The feasible set of (18) adds $p>0$, which $\ln(\bar v/p)$ requires. The standing assumptions are implicit on the page. In (33), the factors $e^{bv_h/e}$ and $1/(4a)$ multiply only the first bracket, as on the rendered page, and $0.5$ is written $1/2$.
-- source:
--   Zhang, Savin, Veeraraghavan, Revenue Management in Crowdfunding, SSRN 3065267 (manuscript of May 26, 2021), pp. 7–13, 19, 29, Assumptions 1–2, (5), (11), (16), (18), (32)–(33), (58)–(59)

import Mathlib
import Definitions.Def_CrowdfundRM_Triangular_Setting

namespace CrowdfundRM.Identical

noncomputable section

/-- Parameters of the crowdfunding model of Zhang–Savin–Veeraraghavan, §3.
`Ihat` = Î (population of independent backers), `k` (arrival rate of independent backers),
`r` (backers' time-discounting rate), `Lh` = Λ_h (arrival rate of herding backers, ASCII name),
`q` (herding propensity), `vbar` = v̄ (upper end of the valuation support),
`Fbi` = F̄_i = 1 − F_i and `Fbh` = F̄_h = 1 − F_h (survival functions of the valuation laws). -/
structure Campaign where
  Ihat : ℝ
  k : ℝ
  r : ℝ
  Lh : ℝ
  q : ℝ
  vbar : ℝ
  Fbi : ℝ → ℝ
  Fbh : ℝ → ℝ

/-- Standing assumptions (implicit on the page): Î, k, r, v̄ > 0, Λ_h, q ≥ 0, and both
valuation laws live on `[0, v̄]`. -/
def Campaign.Standing (M : Campaign) : Prop :=
  0 < M.Ihat ∧ 0 < M.k ∧ 0 < M.r ∧ 0 < M.vbar ∧ 0 ≤ M.Lh ∧ 0 ≤ M.q ∧
    CrowdfundRM.Triangular.IsValLaw M.vbar M.Fbi ∧ CrowdfundRM.Triangular.IsValLaw M.vbar M.Fbh

/-- (5): the number of pledging independent backers `n^p_i(t, p, T)`. -/
def npi (M : Campaign) (p T t : ℝ) : ℝ :=
  M.k * M.Ihat * ∫ x in (0:ℝ)..t, Real.exp (-M.k * x) * M.Fbi (p * Real.exp (M.r * (T - x)))

/-- (11): the number of pledging herding backers `n^p_h(t, p, T)`. -/
def nph (M : Campaign) (p T t : ℝ) : ℝ :=
  M.Lh * M.q * p * (M.k * M.Ihat * ∫ τ in (0:ℝ)..t,
    Real.exp (M.Lh * M.q * p * ∫ u in τ..t, M.Fbh (p * Real.exp (M.r * (T - u)))) *
      M.Fbh (p * Real.exp (M.r * (T - τ))) *
      ∫ x in (0:ℝ)..τ, Real.exp (-M.k * x) * M.Fbi (p * Real.exp (M.r * (T - x))))

/-- The total number of pledges `n(p, T) = n^p_i(T, p, T) + n^p_h(T, p, T)` (p. 12). -/
def ntot (M : Campaign) (p T : ℝ) : ℝ := npi M p T T + nph M p T T

/-- The creator's revenue `π(p, T) = p n(p, T)`, (18). -/
def revenue (M : Campaign) (p T : ℝ) : ℝ := p * ntot M p T

/-- The feasible set of (18), with `p > 0`: `0 < p ≤ v̄`, `0 ≤ T ≤ (1/r) ln(v̄/p)`. -/
def Campaign.Feasible (M : Campaign) (p T : ℝ) : Prop :=
  0 < p ∧ p ≤ M.vbar ∧ 0 ≤ T ∧ T ≤ Real.log (M.vbar / p) / M.r

/-- Survival function of the point mass at `v`, from (58)–(59): `F̄(y) = 1` if `y < v`, else `0`. -/
def stepBar (v : ℝ) (y : ℝ) : ℝ := if y < v then 1 else 0

/-- Identical valuations: every independent backer values the project at `vi`, every herding
backer at `vh`, with `0 < vi ≤ v̄` and `0 < vh ≤ v̄` ((58)–(59)). -/
def IdenticalVals (M : Campaign) (vi vh : ℝ) : Prop :=
  0 < vi ∧ vi ≤ M.vbar ∧ 0 < vh ∧ vh ≤ M.vbar ∧ M.Fbi = stepBar vi ∧ M.Fbh = stepBar vh

/-- Proposition 6's feasible set: (18)'s set together with `T ≤ (1/r) ln(vi/p)`. -/
def Feasible6 (M : Campaign) (vi p T : ℝ) : Prop :=
  M.Feasible p T ∧ T ≤ Real.log (vi / p) / M.r

/-- (32): `δ = Λ_h q v_h / r`. -/
def δ6 (M : Campaign) (vh : ℝ) : ℝ := M.Lh * M.q * vh / M.r

/-- (32): `a = k / (Λ_h q)`. -/
def a6 (M : Campaign) : ℝ := M.k / (M.Lh * M.q)

/-- (32): `b = Λ_h q / r`. -/
def b6 (M : Campaign) : ℝ := M.Lh * M.q / M.r

/-- (33): `X(k, r, Λ_h, q, v_h) = e^{b v_h / e} (1/(4a)) ((k/r) v_h e^{-2} + 0.5 b v_h² e^{-3} + 2a + v_h)
+ (1/a)((k/r)(v_h + a) + a)`. -/
def Xthr (M : Campaign) (vh : ℝ) : ℝ :=
  Real.exp (b6 M * vh / Real.exp 1) * (1 / (4 * a6 M)) *
      ((M.k / M.r) * vh * Real.exp (-2) + 1 / 2 * b6 M * vh ^ 2 * Real.exp (-3) + 2 * a6 M + vh) +
    1 / a6 M * ((M.k / M.r) * (vh + a6 M) + a6 M)

/-- (16): `𝕀(x) = 1` if `x ≥ 0`, `0` if `x < 0`. -/
def ind (x : ℝ) : ℝ := if 0 ≤ x then 1 else 0

/-- `(p₀, T₀)` maximizes `f` over the pairs satisfying `S`. -/
def IsMaxOn₂ (f : ℝ → ℝ → ℝ) (S : ℝ → ℝ → Prop) (p₀ T₀ : ℝ) : Prop :=
  S p₀ T₀ ∧ ∀ p T, S p T → f p T ≤ f p₀ T₀

end

end CrowdfundRM.Identical


