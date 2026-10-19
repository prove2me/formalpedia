-- Prove2me | Definitions.Def_DataGrowth_BGP_DecEconomy
-- name    : DataGrowth_BGP_DecEconomy
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-18T20:09:06.725349+00:00
-- url     : https://prove2.me/theorems/b7eaa931-6635-4bbc-8005-b9dd932a312c
-- title:
--   §2, pp. 4–8 — the decentralized equilibrium path and its balanced growth path
-- statement:
--   A path of the **decentralized data economy** consists of per-capita consumption $c$, data sold per capita $\phi$, the number of varieties $N$, the labor shares $l_R$ (R&D) and $l_E$ (final good), the patent value $V$, the wage $w$, the data price $p_\phi$, the interest rate $r$ and the per-variety profit $\pi$, all functions of time.
--
--   It is an **equilibrium path** if, for every $t>0$: $c,\phi,N,l_R,l_E,V,w,p_\phi$ are positive and $l_E+l_R=1$, and
--   1. (4) $\dot c/c=(r-\rho)/\gamma$;
--   2. (5) $\dot p_\phi/p_\phi-(\sigma-1)\dot\phi/\phi=r-\rho$;
--   3. (3) with $s=0$: $\dot\phi/\phi\le\dot c/c$;
--   4. (13) $\pi(t)=K_\pi\,l_E(t)L(t)$ and (15) $w(t)=K_wN(t)$;
--   5. (9) the integrand below is integrable on $(t,\infty)$ and
--   $$
--   V(t)=\int_t^\infty \exp\Big(-\int_t^s r(\tau)\,d\tau\Big)\pi(s)\,ds ;
--   $$
--   6. (17) $\dot N=\eta N^\zeta\phi^\xi l_R^{1-\xi}L$;
--   7. (18) $\eta\xi N^\zeta\phi^{\xi-1}l_R^{1-\xi}V=p_\phi$ and (19) $\eta(1-\xi)N^\zeta\phi^\xi l_R^{-\xi}V=w$.
--
--   Per-capita output is $y(t)=K_yN(t)l_E(t)$ by (14). A **balanced growth path** is an equilibrium path along which $r(t)=r^*$ is constant, each of $c,\phi,N,l_R,l_E,V,w,p_\phi$ grows at a constant rate of its own, and $y$ grows at the rate $g_c$ of consumption.
--
--   This is the object of Proposition 1 and of the decentralized side of Proposition 3.
--
--   **Formalization Note** The consumer's problem (1)–(3) and the producers' problems (6)–(12) are not formalized as optimization problems: the paper works only with their first-order conditions (4)–(5) and the closed forms (13)–(15), which are encoded in level form with derivatives. The baseline $s=0$, $\theta=0$ is used. Labor-market clearing is the equality $l_E+l_R=1$ used in every proof (the inequality of p. 7 is not). Time runs over $t>0$. "All variables growing at the same constant rate" (p. 9) is read as each variable at its own constant rate, since Proposition 1 has $g^*_\phi\neq g^*$. The condition $g_y=g_c$ is part of the BGP notion, as the paper uses it (PDF p. 25) without deriving it.
-- source:
--   Cong, Xie, Zhang, Knowledge Accumulation, Privacy, and Growth in a Data Economy, arXiv:2109.10028v1, pp. 4–8, §2, (3)–(5), (9), (13)–(15), (17)–(19); p. 9, §3

import Mathlib
import Definitions.Def_DataGrowth_BGP_Params

namespace DataGrowth.BGP

/-- A time path of the decentralized data economy (arXiv:2109.10028v1, §2, pp. 4–8):
per-capita consumption `c`, data sold per capita `phi` (ϕ), number of varieties `N`, labor shares
`lR` (R&D) and `lE` (final good), patent value `V`, wage `w`, data price `pphi` (p_ϕ), interest
rate `r` and per-variety profit `pi` (π). -/
structure DecPath where
  c : ℝ → ℝ
  phi : ℝ → ℝ
  N : ℝ → ℝ
  lR : ℝ → ℝ
  lE : ℝ → ℝ
  V : ℝ → ℝ
  w : ℝ → ℝ
  pphi : ℝ → ℝ
  r : ℝ → ℝ
  pi : ℝ → ℝ

/-- Equilibrium conditions of the decentralized data economy (Cong, Xie, Zhang, *Knowledge
Accumulation, Privacy, and Growth in a Data Economy*, arXiv:2109.10028v1, pp. 4–8, §2), required
at every time t > 0:
* positivity of c, ϕ, N, l_R, l_E, V, w, p_ϕ, and labor-market clearing l_E + l_R = 1;
* the consumption Euler equation (4) ċ/c = (r − ρ)/γ;
* the data Euler equation (5) ṗ_ϕ/p_ϕ − (σ − 1) ϕ̇/ϕ = r − ρ;
* the data constraint (3) with s = 0: ϕ̇/ϕ ≤ ċ/c;
* the profit (13) π = K_π L_E with L_E = l_E L, and the wage (15) w = K_w N;
* the patent value (9) V(t) = ∫_t^∞ exp(−∫_t^s r(τ) dτ) π(s) ds, with the integrand integrable;
* the innovation possibility frontier (17) Ṅ = η N^ζ ϕ^ξ l_R^{1−ξ} L;
* the free-entry conditions (18) ηξ N^ζ ϕ^{ξ−1} l_R^{1−ξ} V = p_ϕ and
  (19) η(1 − ξ) N^ζ ϕ^ξ l_R^{−ξ} V = w.

Formalization Note: the consumer's problem (1)–(3) and the producers' problems (6)–(12) are not
formalized as optimization problems; the paper itself works only with their first-order conditions
(4)–(5) and the closed forms (13)–(15), which are encoded here in level form. The baseline s = 0
(p. 5) and θ = 0 (p. 7) is used. Labor-market clearing is the equality l_E + l_R = 1 used in every
proof (Lemma A.1, (27)), not the inequality of p. 7. Time runs over t > 0 (the paper's [0, ∞);
the endpoint does not affect growth rates). Real powers are `Real.rpow` on positive bases. -/
def IsDecEq (P : Params) (E : DecPath) : Prop :=
  ∀ t : ℝ, 0 < t →
    (0 < E.c t ∧ 0 < E.phi t ∧ 0 < E.N t ∧ 0 < E.lR t ∧ 0 < E.lE t ∧ 0 < E.V t ∧ 0 < E.w t ∧
      0 < E.pphi t) ∧
    E.lE t + E.lR t = 1 ∧
    -- (4)
    HasDerivAt E.c ((E.r t - P.ρ) / P.γ * E.c t) t ∧
    -- (5)
    (DifferentiableAt ℝ E.pphi t ∧ DifferentiableAt ℝ E.phi t ∧
      deriv E.pphi t / E.pphi t - (P.σ - 1) * (deriv E.phi t / E.phi t) = E.r t - P.ρ) ∧
    -- (3) with s = 0
    deriv E.phi t / E.phi t ≤ deriv E.c t / E.c t ∧
    -- (13) and (15)
    E.pi t = P.Kpi * (E.lE t * P.pop t) ∧
    E.w t = P.Kw * E.N t ∧
    -- (9)
    (∀ s : ℝ, 0 < s → IntervalIntegrable E.r MeasureTheory.volume t s) ∧
    MeasureTheory.IntegrableOn
      (fun s => Real.exp (-∫ τ in t..s, E.r τ) * E.pi s) (Set.Ioi t) ∧
    E.V t = (∫ s in Set.Ioi t, Real.exp (-∫ τ in t..s, E.r τ) * E.pi s) ∧
    -- (17)
    HasDerivAt E.N
      (P.η * E.N t ^ P.ζ * E.phi t ^ P.ξ * E.lR t ^ (1 - P.ξ) * P.pop t) t ∧
    -- (18)
    P.η * P.ξ * E.N t ^ P.ζ * E.phi t ^ (P.ξ - 1) * E.lR t ^ (1 - P.ξ) * E.V t = E.pphi t ∧
    -- (19)
    P.η * (1 - P.ξ) * E.N t ^ P.ζ * E.phi t ^ P.ξ * E.lR t ^ (-P.ξ) * E.V t = E.w t

/-- Per-capita output y(t) = Y(t)/L(t) = K_y N(t) l_E(t), from (14) (arXiv:2109.10028v1, p. 6). -/
noncomputable def outputPC (P : Params) (E : DecPath) (t : ℝ) : ℝ := P.Ky * E.N t * E.lE t

/-- The constant growth rates of a decentralized balanced growth path: of c (`gc`), ϕ (`gphi`),
N (`gN`), l_R (`glR`), l_E (`glE`), V (`gV`), w (`gw`), p_ϕ (`gp`), and the constant interest rate
r* (`rstar`). -/
structure DecRates where
  gc : ℝ
  gphi : ℝ
  gN : ℝ
  glR : ℝ
  glE : ℝ
  gV : ℝ
  gw : ℝ
  gp : ℝ
  rstar : ℝ

/-- A balanced growth path of the decentralized economy (arXiv:2109.10028v1, p. 9, §3): an
equilibrium path along which r(t) = r* is constant and each of c, ϕ, N, l_R, l_E, V, w, p_ϕ grows
at its own constant rate, and per-capita output grows at the rate of consumption.

Formalization Note: p. 9 says a BGP "requires that all variables are growing at the same constant
rate", but Proposition 1 itself has g*_ϕ ≠ g* and constant l_R; the reading used in every proof is
that each variable grows at a constant rate of its own and r is constant. The last conjunct,
"the growth rate of consumption is the same as that of output" (PDF p. 25), is part of the BGP
notion: the paper never derives it (the budget constraint (2) is not used). -/
def IsDecBGP (P : Params) (E : DecPath) (R : DecRates) : Prop :=
  IsDecEq P E ∧ (∀ t : ℝ, 0 < t → E.r t = R.rstar) ∧
    HasConstGrowth E.c R.gc ∧ HasConstGrowth E.phi R.gphi ∧ HasConstGrowth E.N R.gN ∧
    HasConstGrowth E.lR R.glR ∧ HasConstGrowth E.lE R.glE ∧ HasConstGrowth E.V R.gV ∧
    HasConstGrowth E.w R.gw ∧ HasConstGrowth E.pphi R.gp ∧
    HasConstGrowth (outputPC P E) R.gc

end DataGrowth.BGP


