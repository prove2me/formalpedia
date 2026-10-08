-- Prove2me | Definitions.Def_BesbesZeevi_Nonparametric_Model
-- name    : BesbesZeevi_Nonparametric_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-05T14:06:53.493195+00:00
-- url     : https://prove2.me/theorems/052cff2e-6430-4fe2-a3c2-c4afc02517f5
-- title:
--   Prices, the nonparametric demand class $\mathcal L(M,\underline K,\overline K,m)$ and the deterministic relaxation $J^D$
-- statement:
--   This file sets up the model of Besbes and Zeevi (§3 and §4.2).
--
--   **Prices.** Fix $0<\underline p<\overline p<\infty$ and an "off" price $p_\infty>0$ outside $[\underline p,\overline p]$. The admissible prices are $[\underline p,\overline p]\cup\{p_\infty\}$.
--
--   **Demand class.** A demand function is a map $\lambda:\mathbb R\to\mathbb R$; $\lambda(p)$ is the instantaneous demand rate at price $p$. Fix finite positive constants $M,\underline K,\overline K,m$ with $\underline K\le\overline K$. The class $\mathcal L=\mathcal L(M,\underline K,\overline K,m)$ consists of the functions $\lambda$ that are *regular*:
--
--   1. $\lambda\ge 0$ and $\lambda(p_\infty)=0$;
--   2. $\lambda$ is non-increasing and injective on $[\underline p,\overline p]$, with inverse $\gamma$ (the price at which the rate is $l$);
--   3. the revenue rate $r(l)=l\,\gamma(l)$ is concave on $[\lambda(\overline p),\lambda(\underline p)]$;
--
--   and that satisfy Assumption 1:
--
--   4. $|\lambda(p)|\le M$ for $p\in[\underline p,\overline p]$;
--   5. $|\lambda(p)-\lambda(p')|\le\overline K|p-p'|$ on $[\underline p,\overline p]$, and $|\gamma(l)-\gamma(l')|\le\underline K^{-1}|l-l'|$ on $[\lambda(\overline p),\lambda(\underline p)]$;
--   6. $\max\{p\lambda(p):p\in[\underline p,\overline p]\}\ge m$.
--
--   **Deterministic relaxation.** For inventory $x$ and horizon $T$, the full-information deterministic relaxation (5) is
--
--   $$
--   J^D(x,T\mid\lambda)=\sup\Big\{\int_0^T p(s)\lambda(p(s))\,ds\;:\;\int_0^T\lambda(p(s))\,ds\le x,\ p(s)\in[\underline p,\overline p]\cup\{p_\infty\}\ \text{for } s\in[0,T]\Big\},
--   $$
--
--   the supremum taken over measurable price paths. Under the scaling (11) (inventory $nx$, demand $n\lambda$) its value is $J^D_n(x,T\mid\lambda)=J^D(nx,T\mid n\lambda)$.
--
--   $J^D$ is the benchmark against which the regret of a pricing policy is measured.
--
--   **Formalization Note** The paper's requirement that $\lambda$ have an inverse $\gamma$ is rendered as injectivity on $[\underline p,\overline p]$, with $\gamma$ given by `Function.invFunOn`. For members of the class, $\lambda$ is Lipschitz, hence continuous, so this is the genuine inverse on $[\lambda(\overline p),\lambda(\underline p)]$. The revenue rate $r(\lambda(p))$ is written $p\lambda(p)$, which equals $\lambda(p)\gamma(\lambda(p))$ on $[\underline p,\overline p]$. Monotonicity is required on $[\underline p,\overline p]$, where Assumption 1 lives; $\lambda$ is unconstrained elsewhere except $\lambda\ge0$ and $\lambda(p_\infty)=0$. A feasible path must be measurable with $\lambda\circ p$ interval-integrable on $[0,T]$, so the constraint and the objective are never junk integrals. The set of path revenues is nonempty (the path at $p_\infty$) and bounded above by $\overline pMT$ for members of the class, so the supremum is genuine.
-- source:
--   Besbes & Zeevi, Dynamic Pricing Without Knowing the Demand Function: Risk Bounds and Near-Optimal Algorithms, Operations Research 57(6), 2009, DOI 10.1287/opre.1080.0640 (authors' final manuscript, last revised December 16, 2007), pp. 6-8 (PDF 8-10), §3, eq. (5); p. 11 (PDF 13), Assumption 1; p. 12 (PDF 14), eq. (11)

import Mathlib

namespace BesbesZeevi.Nonparametric

open MeasureTheory

/-- The price set `[p̲, p̄] ∪ {p_∞}` of Besbes–Zeevi (p. 6): `0 < p̲ < p̄ < ∞`, and `p_∞ > 0` is a
separate price that "turns off" demand (the demand class requires `λ(p_∞) = 0`). `p_∞` is not
a point of `[p̲, p̄]`. -/
structure PriceSet where
  /-- the lower price bound `p̲` -/
  pl : ℝ
  /-- the upper price bound `p̄` -/
  pu : ℝ
  /-- the "off" price `p_∞` -/
  pinf : ℝ
  pl_pos : 0 < pl
  pl_lt_pu : pl < pu
  pinf_pos : 0 < pinf
  pinf_not_mem : pinf ∉ Set.Icc pl pu

/-- The inverse `γ` of the demand function on `[p̲, p̄]`: `γ(l)` is the price in `[p̲, p̄]` at
which the demand rate is `l`. For a demand function that is continuous and injective on
`[p̲, p̄]` (every member of the class `𝓛` below), this is the genuine inverse on
`[λ(p̄), λ(p̲)]`. -/
noncomputable def invDemand (P : PriceSet) (lam : ℝ → ℝ) (l : ℝ) : ℝ :=
  Function.invFunOn lam (Set.Icc P.pl P.pu) l

/-- The parameters `M, K̲, K̄, m` of the class `𝓛(M, K̲, K̄, m)` (Assumption 1, p. 11): finite
positive constants with `K̲ ≤ K̄`. -/
structure DemandClass where
  /-- the demand bound `M` -/
  M : ℝ
  /-- the inverse-Lipschitz constant `K̲` -/
  Klo : ℝ
  /-- the Lipschitz constant `K̄` -/
  Khi : ℝ
  /-- the minimum revenue rate `m` -/
  m : ℝ
  M_pos : 0 < M
  Klo_pos : 0 < Klo
  Klo_le_Khi : Klo ≤ Khi
  m_pos : 0 < m

/-- Membership `λ ∈ 𝓛(M, K̲, K̄, m)` (pp. 6 and 11): `λ` is a *regular* demand function
(nonnegative, `λ(p_∞) = 0`, non-increasing on `[p̲, p̄]`, invertible there with inverse `γ`, and
with concave revenue rate `r(l) = l γ(l)` on `[λ(p̄), λ(p̲)]`) satisfying Assumption 1 (i)–(iii). -/
structure DemandClass.Mem (P : PriceSet) (L : DemandClass) (lam : ℝ → ℝ) : Prop where
  nonneg : ∀ p, 0 ≤ lam p
  off : lam P.pinf = 0
  antitone : AntitoneOn lam (Set.Icc P.pl P.pu)
  injOn : Set.InjOn lam (Set.Icc P.pl P.pu)
  revenue_concave :
    ConcaveOn ℝ (Set.Icc (lam P.pu) (lam P.pl)) (fun l => l * invDemand P lam l)
  /-- Assumption 1 (i) -/
  bounded : ∀ p ∈ Set.Icc P.pl P.pu, |lam p| ≤ L.M
  /-- Assumption 1 (ii), first half -/
  lipschitz : ∀ p ∈ Set.Icc P.pl P.pu, ∀ p' ∈ Set.Icc P.pl P.pu,
    |lam p - lam p'| ≤ L.Khi * |p - p'|
  /-- Assumption 1 (ii), second half -/
  inv_lipschitz : ∀ l ∈ Set.Icc (lam P.pu) (lam P.pl), ∀ l' ∈ Set.Icc (lam P.pu) (lam P.pl),
    |invDemand P lam l - invDemand P lam l'| ≤ L.Klo⁻¹ * |l - l'|
  /-- Assumption 1 (iii): `max {p λ(p) : p ∈ [p̲, p̄]} ≥ m` -/
  min_revenue : ∃ p ∈ Set.Icc P.pl P.pu, L.m ≤ p * lam p

/-- A feasible price path of the deterministic relaxation (5) (p. 8): a measurable
`p : ℝ → ℝ` taking values in `[p̲, p̄] ∪ {p_∞}` on `[0, T]`, whose demand rate is integrable on
`[0, T]`, with total demand `∫₀ᵀ λ(p(s)) ds ≤ x`. -/
def FeasiblePath (P : PriceSet) (lam : ℝ → ℝ) (x T : ℝ) (p : ℝ → ℝ) : Prop :=
  Measurable p ∧
  (∀ s ∈ Set.Icc 0 T, p s ∈ Set.Icc P.pl P.pu ∨ p s = P.pinf) ∧
  IntervalIntegrable (fun s => lam (p s)) volume 0 T ∧
  ∫ s in (0 : ℝ)..T, lam (p s) ≤ x

/-- The revenue `∫₀ᵀ r(λ(p(s))) ds = ∫₀ᵀ p(s) λ(p(s)) ds` of a price path. -/
noncomputable def pathRevenue (lam : ℝ → ℝ) (T : ℝ) (p : ℝ → ℝ) : ℝ :=
  ∫ s in (0 : ℝ)..T, p s * lam (p s)

/-- `J^D(x, T | λ)`, the value of the full-information deterministic relaxation (5) (p. 8): the
supremum of the revenue over feasible price paths. -/
noncomputable def JD (P : PriceSet) (lam : ℝ → ℝ) (x T : ℝ) : ℝ :=
  sSup (pathRevenue lam T '' {p | FeasiblePath P lam x T p})

/-- `J^D_n(x, T | λ)`: the value of (5) under the scaling (11), inventory `n x` and demand
function `n λ(·)` (p. 12). -/
noncomputable def JDn (P : PriceSet) (lam : ℝ → ℝ) (x T : ℝ) (n : ℕ) : ℝ :=
  JD P (fun p => (n : ℝ) * lam p) ((n : ℝ) * x) T

end BesbesZeevi.Nonparametric


