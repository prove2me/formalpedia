-- Prove2me | Definitions.Def_OMSRArbitrary_PerResource
-- name    : OMSRArbitrary_PerResource
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T12:37:04.941198+00:00
-- url     : https://prove2.me/theorems/1bf5d9b3-702e-4f53-be4f-329c3df2d2d4
-- title:
--   Per-resource quantities $\pi_t,\delta_t,e_t,\eta_t,w_t,D_t,v_t,T_i,M,V,W$
-- statement:
--   Fix a resource $i$, seeds $u$ with $u:=u_i$, and thresholds $z$. Let $P_t$ and $P_t^{-i}$ be the reduced prices of the probes of PG$(u)$ and PG$^{-i}$ at $t$ ($0$ if none). For an arrival $t$ with $(i,t)\in E$:
--   $$\pi_t=\frac{P_t^{-i}}{r_ip_{it}},\quad \delta_t(u)=1-g(u)-\pi_t,\quad e_t=\frac{P_t-P_t^{-i}}{r_ip_{it}},\quad \eta_t=\frac{\pi_t}{1-g(u)},\quad w_t(u)=w(u,\pi_t),$$
--   the **demand** $D_t=\big(\gamma_\Lambda(u,\pi_t)-(\pi_t+e_t)\big)^+$, and $v_t(u)=\sigma_\Lambda(u)$ if PG$(u)$'s probe at $t$ has reduced price at least $r_ip_{it}(1-g(u))$, $v_t(u)=1$ otherwise (including no probe). Further
--   $$T_i=\{t:(i,t)\in E,\ \delta_t(u)>0,\ z_t\le p_{it}\},\qquad M=\max_{t\in T_i}D_t,\quad V=\max_{t\in T_i}v_t(u),\quad W=\max_{t\in T_i}w_t(u),$$
--   with $\max\emptyset:=0$.
--
--   These quantities carry Lemmas 18–20 and eq. (12), the per-seed analysis of Section 5.
--
--   **Formalization Note** The quantities are defined at every arrival but used only at arrivals with $(i,t)\in E$, where $r_ip_{it}>0$.
-- source:
--   Udwani, Online Matching with Arbitrary Stochastic Rewards, arXiv:2611.03598, §4, p.15; §5 (Notation, Combined Target), pp.23–24; §5.1, p.24; App. F (Notation), p.39

import Mathlib
import Definitions.Def_OMSRArbitrary_Targets
import Definitions.Def_OMSRArbitrary_PerturbedGreedy

open scoped BigOperators
open MeasureTheory
open StochasticRewardMatching.Decomposable (Instance Seeds)
noncomputable section

namespace OMSRArbitrary

variable {n m : ℕ}

/-! Per-resource quantities of arXiv:2611.03598, §4 (p.15), §5 (pp.23–24) and Appendix F (p.39),
for a fixed resource `i`, fixed seeds `u` (with `u_i` the seed of `i`) and thresholds `z`.
PG(u) is the run from all resources at the first arrival; PG^{−i} is the run from
`univ.erase i` with the same seed vector (it never reads `u_i`). All of them are used only at
arrivals `t` with `(i, t) ∈ E`, where `r_i p_{it} > 0`. -/

/-- `π_t := P_t^{−i}/(r_i p_{it})`, the reduced price of PG^{−i}'s probe at `t` normalized by
`r_i p_{it}` (arXiv:2611.03598, §5, p.23; App. F, p.39). -/
def piW (D : Instance n m) (g : ℝ → ℝ) (u : Seeds n) (i : Fin n) (z : Seeds m) (t : Fin m) : ℝ :=
  pgPrice D g u (Finset.univ.erase i) 0 (corrOutcome D z) t / (D.reward i * D.probability (i, t))

/-- `δ_t(u) := 1 − g(u) − π_t` (arXiv:2611.03598, §5, p.23). -/
def deltaW (D : Instance n m) (g : ℝ → ℝ) (u : Seeds n) (i : Fin n) (z : Seeds m) (t : Fin m) : ℝ :=
  1 - g (u i) - piW D g u i z t

/-- **The boost** `e_t := (P_t − P_t^{−i})/(r_i p_{it})` (arXiv:2611.03598, App. F, p.39). -/
def boost (D : Instance n m) (g : ℝ → ℝ) (u : Seeds n) (i : Fin n) (z : Seeds m) (t : Fin m) : ℝ :=
  (pgPrice D g u Finset.univ 0 (corrOutcome D z) t -
    pgPrice D g u (Finset.univ.erase i) 0 (corrOutcome D z) t) / (D.reward i * D.probability (i, t))

/-- `η_t := π_t/(1 − g(u))` (arXiv:2611.03598, §5, p.23). -/
def etaW (D : Instance n m) (g : ℝ → ℝ) (u : Seeds n) (i : Fin n) (z : Seeds m) (t : Fin m) : ℝ :=
  piW D g u i z t / (1 - g (u i))

/-- `w_t(u) := w(u, π_t)`, the shorthand of arXiv:2611.03598, §5, p.23 (equal to
`min{1, (1 − η_t)/(1 − σ_Λ(u))}`, read as 1 if `σ_Λ(u) = 1`). -/
def wt (D : Instance n m) (g : ℝ → ℝ) (ρ : ℝ) (u : Seeds n) (i : Fin n) (z : Seeds m)
    (t : Fin m) : ℝ :=
  wfun g ρ (u i) (piW D g u i z t)

/-- **The demand** `D_t := (γ_Λ(u, π_t) − (π_t + e_t))⁺` (arXiv:2611.03598, §5.1, p.24). -/
def demand (D : Instance n m) (g c : ℝ → ℝ) (ρ : ℝ) (u : Seeds n) (i : Fin n) (z : Seeds m)
    (t : Fin m) : ℝ :=
  max (gammaW g c ρ (u i) (piW D g u i z t) - (piW D g u i z t + boost D g u i z t)) 0

open Classical in
/-- `v_t(u) := σ_Λ(u)` if PG(u)'s probe at `t` has reduced price at least `r_i p_{it}(1 − g(u))`,
and `1` otherwise, including when PG(u) probes nothing (arXiv:2611.03598, §5.1, p.24). -/
def vt (D : Instance n m) (g : ℝ → ℝ) (ρ : ℝ) (u : Seeds n) (i : Fin n) (z : Seeds m)
    (t : Fin m) : ℝ :=
  if ∃ k, pgProbe D g u Finset.univ 0 (corrOutcome D z) t = some k ∧
      D.reward i * D.probability (i, t) * (1 - g (u i)) ≤ reducedPrice D g u k t
  then sigmaW g ρ (u i) else 1

open Classical in
/-- `T_i := {t : (i, t) ∈ E, δ_t(u) > 0, z_t ≤ p_{it}}` (arXiv:2611.03598, §5.1, p.24). -/
def Tset (D : Instance n m) (g : ℝ → ℝ) (u : Seeds n) (i : Fin n) (z : Seeds m) :
    Finset (Fin m) :=
  Finset.univ.filter (fun t => (i, t) ∈ D.edges ∧ 0 < deltaW D g u i z t ∧
    z t ≤ D.probability (i, t))

/-- `max_{t∈T} f(t)` with `max ∅ := 0` (arXiv:2611.03598, pp.17, 24). -/
def finMax (T : Finset (Fin m)) (f : Fin m → ℝ) : ℝ :=
  if h : T.Nonempty then T.sup' h f else 0

/-- `M := max_{t∈T_i} D_t` (`max ∅ := 0`), arXiv:2611.03598, §5.1, p.24. -/
def Mmax (D : Instance n m) (g c : ℝ → ℝ) (ρ : ℝ) (u : Seeds n) (i : Fin n) (z : Seeds m) : ℝ :=
  finMax (Tset D g u i z) (demand D g c ρ u i z)

/-- `V := max_{t∈T_i} v_t(u)` (`max ∅ := 0`), arXiv:2611.03598, §5.1, p.24. -/
def Vmax (D : Instance n m) (g : ℝ → ℝ) (ρ : ℝ) (u : Seeds n) (i : Fin n) (z : Seeds m) : ℝ :=
  finMax (Tset D g u i z) (vt D g ρ u i z)

/-- `W := max_{t∈T_i} w_t(u)` (`max ∅ := 0`), arXiv:2611.03598, §5.1, p.24. -/
def Wmax (D : Instance n m) (g : ℝ → ℝ) (ρ : ℝ) (u : Seeds n) (i : Fin n) (z : Seeds m) : ℝ :=
  finMax (Tset D g u i z) (wt D g ρ u i z)

end OMSRArbitrary


