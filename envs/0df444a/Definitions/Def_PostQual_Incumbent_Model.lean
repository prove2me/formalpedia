-- Prove2me | Definitions.Def_PostQual_Incumbent_Model
-- name    : PostQual_Incumbent_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-19T01:25:34.593029+00:00
-- url     : https://prove2.me/theorems/cf0c8016-dc63-4df7-b694-d1188696d36f
-- title:
--   §2, §3.2, Theorem 2, pp. 6–18 — POST auction primitives, the incumbent's Bellman system (8)–(10), and m⋆, b⋆_m, p⋆_m, s⋆_m
-- statement:
--   This file fixes the model of the post-auction qualification-screening (POST) open-bid auction of Zhang, Chen and Katok and the incumbent's dynamic program.
--
--   **Primitives (§2).** Suppliers' costs lie in $[\underline R,\overline R]$; the buyer invites $N$ entrants whose costs are i.i.d. with density $f_e$ and c.d.f. $F_e(x)=\int_{-\infty}^x f_e$; each screened entrant qualifies with probability $\beta$, and screening costs $K$. When the incumbent drops out, the price drops by $\Delta:=K/\beta$. The **standing assumptions** are $\underline R<\overline R$, $N\ge 2$, $0<\beta<1$, $K>0$, $K/\beta<\overline R-\underline R$, and $f_e$ is a probability density vanishing off $[\underline R,\overline R]$; in addition $f_e$ is positive and continuous on $[\underline R,\overline R]$. **Assumption 1** says $F_e/f_e$ is nondecreasing and convex on $[\underline R,\overline R]$.
--
--   **Order statistics (p. 13).** $G^k_e(z;c)=[F_e(z)/F_e(c)]^k$ and $g^k_e(z;c)=k[F_e(z)]^{k-1}f_e(z)/[F_e(c)]^k$.
--
--   **The incumbent's problem (8)–(10), p. 17.** With incumbent cost $x_0$, $m$ remaining entrants and clock price $p$, let $\ell(x_0)=\max\{\underline R+\Delta,x_0\}$,
--   $$\Pi^m_0(b;x_0,p)=\int_b^p V^{m-1}_0(x_0,z)\,g^m_e(z-\Delta;p-\Delta)\,dz+G^m_e(b-\Delta;p-\Delta)(1-\beta)^m(b-x_0),$$
--   $$V^m_0(x_0,p)=\max_{b\in[\ell(x_0),p]}\Pi^m_0(b;x_0,p),\qquad V^0_0(x_0,p)=p-x_0.$$
--
--   **Theorem 2's objects (p. 18).** $m^\star(x_0)=\big\lfloor \inf_{b\in(\max\{x_0,\underline R+\Delta\},\overline R+\Delta]}\frac{(1-\beta)F_e(b-\Delta)}{\beta(b-x_0)f_e(b-\Delta)}\big\rfloor$; $b^\star_m(x_0)=\underline R+\Delta$ if $x_0\le\underline R+\Delta$ and otherwise $\inf\{b\in(x_0,\overline R+\Delta]: H(b)-L^m(b;x_0)<0\}$; $p^\star_m(x_0)=\inf\{b>b^\star_m(x_0):\Pi^m_0(b;x_0,\overline R+\Delta)-\Pi^m_0(b^\star_m(x_0);x_0,\overline R+\Delta)\ge0\}$; and $s^\star_m(x_0;p)=b^\star_m(x_0)\wedge p$ if $m>m^\star(x_0)$ and $p\le p^\star_m(x_0)$, else $p$.
--
--   **Proof helpers (pp. ec5, ec10).** $H(b)=F_e(b-\Delta)/f_e(b-\Delta)$, $L^m(b;x)=m\beta(b-x)/(1-\beta)$,
--   $$\zeta^m(b;x_0,p)=\frac{[F_e(b-\Delta)]^{m-1}(1-\beta)^m}{[F_e(p-\Delta)]^m}\Big[-\frac{m\beta}{1-\beta}(b-x_0)f_e(b-\Delta)+F_e(b-\Delta)\Big],$$
--   and $b^{\star\star}_m(x)=\sup\{b\in(\max\{x,\underline R+\Delta\},\overline R+\Delta]:H(b)-L^m(b,x)<0\}$.
--
--   These are the objects of Theorem 2, which shows that the incumbent's optimal drop-out rule is a compete-or-fold threshold rule.
--
--   **Formalization Note** All quantities are real; counts are natural numbers. The max in (8) is written as a real supremum over the compact interval $[\ell(x_0),p]$; that it is attained is part of what Theorem 2 asserts. The integral in (9) is the signed interval integral, so $\Pi^m_0(b;x_0,p)$ is defined by (9) for every real $b$, including $b>p$, as the definition of $p^\star_m$ and Lemma EC.1 (d) require. The page's min in $m^\star$ is read as an infimum over the half-open interval, because the ratio has a zero denominator at $b=x_0$. The page's $(b^\star_m(x_0),\infty]$ in $p^\star_m$ is taken over the reals. $b^{\star\star}$ is restricted to $b>\underline R+\Delta$, where $H$ has a nonzero denominator; this does not change the supremum when $m>m^\star(x)$. `Pi m` uses `V (m - 1)` and is used only for $m\ge1$.
-- source:
--   Zhang, Chen & Katok, “Now or Later?” When to deploy qualification screening in open-bid auction for re-sourcing, accepted manuscript (Operations Research 69(6), 2021; LBS Research Online eprint 1542), pp. 6–18 (PDF 7–19), §2, Assumption 1, (8)–(10), Theorem 2; pp. ec5, ec10 (PDF 39, 44), H, L^m, ζ^m (EC.7), b⋆⋆ (Claim EC.1)

import Mathlib

namespace PostQual.Incumbent

/-- Primitives of the POST auction (Zhang, Chen & Katok, §2, pp. 6–8): the support `[R̲, R̄]` of
the suppliers' costs (`Rlo`, `Rhi`), the number `N` of entrants, the probability `β` that a
screened entrant qualifies, the screening cost `K`, and the entrants' cost density `fe`. -/
structure Params where
  /-- `R̲`, the lower end of the cost support. -/
  Rlo : ℝ
  /-- `R̄`, the upper end of the cost support (the incumbent's current price). -/
  Rhi : ℝ
  /-- `N`, the number of entrants. -/
  N : ℕ
  /-- `β`, the probability that a screened entrant passes qualification. -/
  β : ℝ
  /-- `K`, the cost of screening one entrant. -/
  K : ℝ
  /-- `fe`, the probability density of an entrant's cost. -/
  fe : ℝ → ℝ

namespace Params

variable (P : Params)

/-- The price decrement `∆ := K/β` announced when the incumbent drops out (p. 8). -/
noncomputable def Δ : ℝ := P.K / P.β

/-- The c.d.f. `Fe(x) = ∫_{-∞}^x fe` of an entrant's cost. -/
noncomputable def Fe (x : ℝ) : ℝ := ∫ t in Set.Iic x, P.fe t

/-- The standing assumptions of §2 (pp. 6–7) and §3.1.1 (p. 11): `R̲ < R̄`, `N ≥ 2`,
`β ∈ (0,1)`, `K > 0`, `K/β < R̄ − R̲`, and `fe` is a probability density supported on `[R̲, R̄]`.
Added (needed by the page's own formulas `H(b) = Fe(b−∆)/fe(b−∆)` and `∂Π/∂b`): `fe` is positive
and continuous on `[R̲, R̄]`. -/
def Standing : Prop :=
  P.Rlo < P.Rhi ∧ 2 ≤ P.N ∧ 0 < P.β ∧ P.β < 1 ∧ 0 < P.K ∧ P.Δ < P.Rhi - P.Rlo ∧
  (∀ t, t ∉ Set.Icc P.Rlo P.Rhi → P.fe t = 0) ∧
  (∀ t ∈ Set.Icc P.Rlo P.Rhi, 0 < P.fe t) ∧
  ContinuousOn P.fe (Set.Icc P.Rlo P.Rhi) ∧
  ∫ t in P.Rlo..P.Rhi, P.fe t = 1

/-- Assumption 1 (p. 6): `Fe/fe` is nondecreasing and convex on the support `[R̲, R̄]`. -/
def Assumption1 : Prop :=
  MonotoneOn (fun t => P.Fe t / P.fe t) (Set.Icc P.Rlo P.Rhi) ∧
  ConvexOn ℝ (Set.Icc P.Rlo P.Rhi) (fun t => P.Fe t / P.fe t)

/-- `G^k_e(z; c) = [Fe(z)/Fe(c)]^k` (p. 13): the c.d.f. of the highest of `k` entrants' costs
given that all are at most `c`. -/
noncomputable def G (k : ℕ) (z c : ℝ) : ℝ := (P.Fe z / P.Fe c) ^ k

/-- `g^k_e(z; c) = k [Fe(z)]^{k−1} fe(z) / [Fe(c)]^k` (p. 13): the matching density. -/
noncomputable def g (k : ℕ) (z c : ℝ) : ℝ := k * P.Fe z ^ (k - 1) * P.fe z / P.Fe c ^ k

/-- The left end `max{R̲ + ∆, x0}` of the incumbent's feasible drop-out prices in (8). -/
noncomputable def lo (x0 : ℝ) : ℝ := max (P.Rlo + P.Δ) x0

/-- Formula (9) with the continuation value `W = V^{m−1}_0(x0, ·)` supplied as an argument:
`∫_b^p W(z) g^m_e(z−∆; p−∆) dz + G^m_e(b−∆; p−∆) (1−β)^m (b − x0)`.
The integral is the signed interval integral, so the formula is evaluated for every real `b`,
also `b > p`. -/
noncomputable def PiAux (m : ℕ) (W : ℝ → ℝ) (b x0 p : ℝ) : ℝ :=
  (∫ z in b..p, W z * P.g m (z - P.Δ) (p - P.Δ)) +
    P.G m (b - P.Δ) (p - P.Δ) * (1 - P.β) ^ m * (b - x0)

/-- The incumbent's value `V^m_0(x0, p)`: the boundary condition (10) `V^0_0(x0, p) = p − x0`,
and the Bellman equation (8)
`V^m_0(x0, p) = max_{b ∈ [max{R̲+∆, x0}, p]} Π^m_0(b; x0, p)` (written as a supremum). -/
noncomputable def V : ℕ → ℝ → ℝ → ℝ
  | 0, x0, p => p - x0
  | m + 1, x0, p => sSup ((fun b => P.PiAux (m + 1) (V m x0) b x0 p) '' Set.Icc (P.lo x0) p)

/-- `Π^m_0(b; x0, p)` of (9), for `m ≥ 1`: drop-out plan `b` with `m` entrants left at price `p`. -/
noncomputable def Pi (m : ℕ) (b x0 p : ℝ) : ℝ := P.PiAux m (P.V (m - 1) x0) b x0 p

/-- `H(b) = Fe(b−∆)/fe(b−∆)` (p. ec5). -/
noncomputable def H (b : ℝ) : ℝ := P.Fe (b - P.Δ) / P.fe (b - P.Δ)

/-- `L^m(b; x) = mβ(b − x)/(1 − β)` (p. ec5). -/
noncomputable def L (m : ℕ) (b x : ℝ) : ℝ := m * P.β * (b - x) / (1 - P.β)

/-- The ratio `(1−β) Fe(b−∆) / (β (b − x0) fe(b−∆))` minimized in the definition of `m⋆`. -/
noncomputable def ratio (x0 b : ℝ) : ℝ :=
  (1 - P.β) * P.Fe (b - P.Δ) / (P.β * (b - x0) * P.fe (b - P.Δ))

/-- `m⋆(x0)` of Theorem 2 (p. 18): the floor of the minimum of `ratio x0` over
`b ∈ [max{x0, R̲+∆}, R̄+∆]`, read as the infimum over the half-open interval
`(max{x0, R̲+∆}, R̄+∆]` (the ratio at `b = x0` has a zero denominator). -/
noncomputable def mStar (x0 : ℝ) : ℕ :=
  ⌊sInf (P.ratio x0 '' Set.Ioc (max x0 (P.Rlo + P.Δ)) (P.Rhi + P.Δ))⌋₊

/-- `b⋆_m(x0)` of Theorem 2 (p. 18): `R̲ + ∆` if `x0 ≤ R̲ + ∆`, and otherwise
`inf{b ∈ (x0, R̄+∆] : Fe(b−∆)/fe(b−∆) − mβ(b−x0)/(1−β) < 0}`. -/
noncomputable def bStar (m : ℕ) (x0 : ℝ) : ℝ :=
  if x0 ≤ P.Rlo + P.Δ then P.Rlo + P.Δ
  else sInf {b | b ∈ Set.Ioc x0 (P.Rhi + P.Δ) ∧ P.H b - P.L m b x0 < 0}

/-- `p⋆_m(x0)` of Theorem 2 (p. 18): the least `b > b⋆_m(x0)` with
`Π^m_0(b; x0, R̄+∆) − Π^m_0(b⋆_m(x0); x0, R̄+∆) ≥ 0`. -/
noncomputable def pStar (m : ℕ) (x0 : ℝ) : ℝ :=
  sInf {b | P.bStar m x0 < b ∧
    0 ≤ P.Pi m b x0 (P.Rhi + P.Δ) - P.Pi m (P.bStar m x0) x0 (P.Rhi + P.Δ)}

/-- `s⋆_m(x0; p)` of Theorem 2 (ii) (p. 18): `b⋆_m(x0) ∧ p` if `m > m⋆(x0)` and `p ≤ p⋆_m(x0)`,
and `p` otherwise. -/
noncomputable def sStar (m : ℕ) (x0 p : ℝ) : ℝ :=
  if P.mStar x0 < m ∧ p ≤ P.pStar m x0 then min (P.bStar m x0) p else p

/-- `ζ^m(b; x0, p)`, the upper bound in (EC.7) (p. ec5):
`[Fe(b−∆)]^{m−1}(1−β)^m/[Fe(p−∆)]^m · [−mβ/(1−β) (b−x0) fe(b−∆) + Fe(b−∆)]`. -/
noncomputable def zeta (m : ℕ) (b x0 p : ℝ) : ℝ :=
  P.Fe (b - P.Δ) ^ (m - 1) * (1 - P.β) ^ m / P.Fe (p - P.Δ) ^ m *
    (-(m * P.β / (1 - P.β)) * (b - x0) * P.fe (b - P.Δ) + P.Fe (b - P.Δ))

/-- `b⋆⋆_m(x) = sup{b ∈ (x, R̄+∆] : H(b) − L^m(b, x) < 0}` (Claim EC.1, p. ec10), with `b`
restricted to `b > R̲ + ∆`, where `H` is defined by a nonzero denominator. -/
noncomputable def bStarStar (m : ℕ) (x : ℝ) : ℝ :=
  sSup {b | b ∈ Set.Ioc (max x (P.Rlo + P.Δ)) (P.Rhi + P.Δ) ∧ P.H b - P.L m b x < 0}

end Params

end PostQual.Incumbent


