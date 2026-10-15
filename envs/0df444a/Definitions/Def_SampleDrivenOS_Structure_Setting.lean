-- Prove2me | Definitions.Def_SampleDrivenOS_Structure_Setting
-- name    : SampleDrivenOS_Structure_Setting
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-15T04:31:50.795122+00:00
-- url     : https://prove2.me/theorems/a4ebef13-2255-4210-a983-f8a5c9bf3c17
-- title:
--   §3.2–3.3 — the negative-binomial term, the functionals $F_k(q)$ (4), feasibility for CLP$_p$, equations (5)–(6), the threshold form (7) and one mass-moving step
-- statement:
--   This file fixes the objects of the continuous linear program CLP$_p$ of Correa, Cristi, Epstein and Soto, which describes the limiting stopping probabilities of rank-based algorithms when a fraction $p\in[0,1)$ of the items is observed as a sample before the online phase.
--
--   **Variables.** A candidate solution is a function $q(t,\ell)$ of a time $t\in[p,1]$ and a rank $\ell\in\{1,2,\dots\}$; $q(t,\ell)$ is the density of stopping at time $t$ on an item that is the $\ell$-th best among those seen so far. Ranks are $1$-based; the value at $\ell=0$ is never used.
--
--   **The negative-binomial term.** For integers $k,\ell\ge 1$ and $t\in\mathbb R$,
--   $$\mathrm{nb}_{k,\ell}(t)=\sum_{j=\ell}^{k}\binom{j-1}{\ell-1}(1-t)^{j-\ell}t^{\ell},$$
--   the probability that a NegativeBinomial$(\ell,t)$ variable is at most $k$; it is $0$ when $\ell>k$.
--
--   **The functionals (4).** For $k\ge1$,
--   $$F_k(q)=\sum_{\ell=1}^{k}\int_p^1 q(t,\ell)\,\mathrm{nb}_{k,\ell}(t)\,dt .$$
--
--   **Cumulative mass.** $M_q(t)=\int_p^t\sum_{s\ge1}q(\tau,s)\,d\tau$, computed as an integral of a series of nonnegative extended reals, so that it equals $+\infty$ when the series or the integral diverges.
--
--   **Feasibility for CLP$_p$.** $q$ is feasible when
--   1. $q(t,\ell)\ge0$ for all $t\in[p,1]$ and $\ell\ge1$;
--   2. each component $t\mapsto q(t,\ell)$ is integrable on $[p,1]$;
--   3. $t\,q(t,\ell)+M_q(t)\le1$ for all $t\in[p,1]$ and $\ell\ge1$.
--
--   **Equations (5)–(6).** For a threshold sequence $(t_i)_{i\ge0}$, $q$ solves (5)–(6) when, for every $\ell\ge1$ and every $\tau\in[p,1)$,
--   $$\tau\,q(\tau,\ell)+M_q(\tau)=1\ \text{ if }\tau\ge t_\ell,\qquad q(\tau,\ell)=0\ \text{ if }\tau<t_\ell .$$
--
--   **Threshold form (7).** With $T_i=\prod_{j=1}^{i}t_j$ ($T_0=1$), $q$ has the threshold form when, for every $\ell\ge1$ and $\tau\in[p,1)$: if $\tau\in[t_i,t_{i+1})$ then $q(\tau,\ell)=T_i/\tau^{i+1}$ for $\ell\le i$ and $q(\tau,\ell)=0$ for $\ell>i$; and $q(\tau,\ell)=0$ if $\tau$ lies in no interval $[t_i,t_{i+1})$.
--
--   **One mass-moving step (p. 9).** The envelope of $q$ is $G_q(t)=\frac1t\bigl(1-M_q(t)\bigr)$. Given thresholds $t_\ell(n)$, the moved solution is $q_n(t,\ell)=G_{q}(t)$ if $t\ge t_\ell(n)$ and $0$ otherwise.
--
--   These objects are the vocabulary of Theorem 2, its proof on pp. 9–10, and Lemmas 17 and 18.
--
--   **Formalization Note** $q$ is a function `ℝ → ℕ → ℝ`, a representative of the paper's class in $L^1([p,1]\times\mathbb N)$; constraints are imposed pointwise, as printed. The mass $M_q$ is a lower Lebesgue integral in $[0,\infty]$, never a Bochner integral of a real series (which would read $0$ on divergent data). Integrability of each component is part of feasibility, so $F_k$ is never a junk value on a feasible $q$. The envelope converts $M_q(t)$ to a real number; for feasible $q$ and $t\in[p,1]$ the mass is at most $1$, so nothing is lost. Equations (5)–(7) are imposed on $[p,1)$, not $[p,1]$: at the single point $t=1$ the printed (7) forces $q^*(1,\ell)=0$, while (5) then demands $\int_p^1\sum_{s\ge1}q^*(\tau,s)\,d\tau=1$, which fails in general (for the classical secretary thresholds $t_1=1/e$, $t_i=1$ for $i\ge2$, $p=0$, the integral is $1-1/e$). A single point is a null set, so the $L^1$ class of $q^*$ is unaffected.
-- source:
--   Correa, Cristi, Epstein & Soto, Sample-Driven Optimal Stopping: From the Secretary Problem to the i.i.d. Prophet Inequality, arXiv:2011.06516v2, pp. 8–9 (PDF pp. 9–10), eq. (4), problem CLP_p, Theorem 2 eqs. (5)–(7), proof of Theorem 2 (definition of q_n)

import Mathlib

namespace SampleDrivenOS.Structure

open MeasureTheory Set

noncomputable section

/-- The negative-binomial term `Σ_{j=ℓ}^{k} C(j−1, ℓ−1) (1 − t)^{j−ℓ} t^ℓ` that accompanies
`q(t, ℓ)` in `F_k(q)` (p. 8, below (7); Appendix A.4). It is the probability that a
NegativeBinomial(ℓ, t) variable is at most `k`. Ranks `ℓ` are 1-based; the value at `ℓ = 0` is
never used. For `ℓ > k` the sum is empty and the term is `0`. -/
def nbTerm (k ℓ : ℕ) (t : ℝ) : ℝ :=
  ∑ j ∈ Finset.Icc ℓ k, ((j - 1).choose (ℓ - 1) : ℝ) * (1 - t) ^ (j - ℓ) * t ^ ℓ

/-- The functional (4): `F_k(q) = Σ_{ℓ=1}^{k} ∫_p^1 q(t, ℓ) · nbTerm k ℓ t dt`. -/
def Fk (p : ℝ) (q : ℝ → ℕ → ℝ) (k : ℕ) : ℝ :=
  ∑ ℓ ∈ Finset.Icc 1 k, ∫ t in p..1, q t ℓ * nbTerm k ℓ t

/-- The cumulative stopping mass `∫_p^t Σ_{s≥1} q(τ, s) dτ`, computed as a lower Lebesgue
integral of an `ℝ≥0∞`-valued series, so that it is never a junk value: it is `⊤` when the
series or the integral diverges. -/
def cumMass (p : ℝ) (q : ℝ → ℕ → ℝ) (t : ℝ) : ENNReal :=
  ∫⁻ τ in Icc p t, ∑' s : ℕ, ENNReal.ofReal (q τ (s + 1))

/-- Feasibility for CLP_p (p. 8): `q` is nonnegative on `[p, 1] × {1, 2, …}`, each component
`q(·, ℓ)` is integrable on `[p, 1]`, and
`t q(t, ℓ) + ∫_p^t Σ_{s≥1} q(τ, s) dτ ≤ 1` for all `t ∈ [p, 1]` and `ℓ ≥ 1`. -/
def IsFeasible (p : ℝ) (q : ℝ → ℕ → ℝ) : Prop :=
  (∀ t ∈ Icc p 1, ∀ ℓ : ℕ, 1 ≤ ℓ → 0 ≤ q t ℓ) ∧
  (∀ ℓ : ℕ, 1 ≤ ℓ → IntegrableOn (fun t => q t ℓ) (Icc p 1)) ∧
  (∀ t ∈ Icc p 1, ∀ ℓ : ℕ, 1 ≤ ℓ → ENNReal.ofReal (t * q t ℓ) + cumMass p q t ≤ 1)

/-- `T_i = Π_{j=1}^{i} t_j` (Theorem 2, p. 8); `T_0 = 1`. -/
def thresholdProd (t : ℕ → ℝ) (i : ℕ) : ℝ :=
  ∏ j ∈ Finset.Icc 1 i, t j

/-- Equations (5) and (6) of Theorem 2 for the threshold sequence `t`, on `t ∈ [p, 1)` and for
every rank `ℓ ≥ 1`:
(5) `τ q(τ, ℓ) + ∫_p^τ Σ_{s≥1} q(σ, s) dσ = 1` if `τ ≥ t_ℓ`;
(6) `q(τ, ℓ) = 0` if `τ < t_ℓ`. -/
def SolvesEq5Eq6 (p : ℝ) (t : ℕ → ℝ) (q : ℝ → ℕ → ℝ) : Prop :=
  ∀ ℓ : ℕ, 1 ≤ ℓ → ∀ τ ∈ Ico p 1,
    (t ℓ ≤ τ → ENNReal.ofReal (τ * q τ ℓ) + cumMass p q τ = 1) ∧
    (τ < t ℓ → q τ ℓ = 0)

/-- The threshold form (7) of Theorem 2, on `τ ∈ [p, 1)` and for every rank `ℓ ≥ 1`:
if `τ ∈ [t_i, t_{i+1})` then `q(τ, ℓ) = T_i / τ^{i+1}` when `ℓ ≤ i` and `q(τ, ℓ) = 0` when
`ℓ > i`; if `τ` lies in no interval `[t_i, t_{i+1})`, then `q(τ, ℓ) = 0`. -/
def IsThresholdForm (p : ℝ) (t : ℕ → ℝ) (q : ℝ → ℕ → ℝ) : Prop :=
  ∀ τ ∈ Ico p 1, ∀ ℓ : ℕ, 1 ≤ ℓ →
    (∀ i : ℕ, t i ≤ τ → τ < t (i + 1) →
      (ℓ ≤ i → q τ ℓ = thresholdProd t i / τ ^ (i + 1)) ∧ (i < ℓ → q τ ℓ = 0)) ∧
    ((∀ i : ℕ, ¬ (t i ≤ τ ∧ τ < t (i + 1))) → q τ ℓ = 0)

/-- The upper envelope `(1/t)(1 − ∫_p^t Σ_{s≥1} q(τ, s) dτ)` of a feasible `q` (proof of
Theorem 2, p. 9). For a feasible `q` and `t ∈ [p, 1]` the cumulative mass is at most `1`, so the
conversion to a real number loses nothing. -/
def envelope (p : ℝ) (q : ℝ → ℕ → ℝ) (t : ℝ) : ℝ :=
  (1 / t) * (1 - (cumMass p q t).toReal)

/-- One step of the mass-moving procedure (proof of Theorem 2, p. 9): given thresholds `tl ℓ`,
`q_n(t, ℓ) = (1/t)(1 − ∫_p^t Σ_{s≥1} q_{n−1}(τ, s) dτ)` if `t ≥ tl ℓ`, and `0` if `t < tl ℓ`. -/
def movedSolution (p : ℝ) (q : ℝ → ℕ → ℝ) (tl : ℕ → ℝ) : ℝ → ℕ → ℝ :=
  fun τ ℓ => if tl ℓ ≤ τ then envelope p q τ else 0

end

end SampleDrivenOS.Structure


