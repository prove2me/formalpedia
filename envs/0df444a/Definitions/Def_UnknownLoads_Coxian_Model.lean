-- Prove2me | Definitions.Def_UnknownLoads_Coxian_Model
-- name    : UnknownLoads_Coxian_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-13T22:34:30.768625+00:00
-- url     : https://prove2.me/theorems/ab933be8-5805-4f34-aaba-9e5b59424c55
-- title:
--   §3, §6 — Coxian service with r phases, occupancy profiles, the state space S, q(i), ⌊·⌋_Δ, ρ, η, G_m and the fluid function (3)
-- statement:
--   This file fixes the standing data of the Coxian scenario of Goldsztajn, Borst and van Leeuwaarden (Sections 3, 4.2 and 6) and the deterministic objects built from it.
--
--   1. **Parameters.** There are $r \ge 1$ service phases. A task enters in phase $1$; phase $m$ lasts an exponential time of mean $1/\mu_m$, $\mu_m > 0$; after phase $m$ the task moves to phase $m+1$ with probability $p_m$ or leaves with probability $1-p_m$, where $p_r = 0$ and $p_m \in (0,1)$ for $m \ne r$. Tasks arrive at the constant rate $n\lambda$, $\lambda \ge 0$, to a system of $n$ server pools. The dispatching rule uses an integral parameter $\Delta \ge 1$. An enumeration $\{\nu_i : i \ge 0\}$ of $\mathbb N^r$ is fixed.
--   2. **Mean service time and offered load.**
--   $$\frac{1}{\mu} = \sum_{i=1}^{r} (1-p_i)\Big(\prod_{j=1}^{i-1} p_j\Big)\sum_{k=1}^{i}\frac{1}{\mu_k}, \qquad \rho := \frac{\lambda}{\mu}.$$
--   3. **Profiles and occupancy states.** A server pool has profile $\nu = (\nu(1),\dots,\nu(r)) \in \mathbb N^r$ if it holds $\nu(m)$ tasks in phase $m$; $\Sigma(\nu) = \nu(1)+\dots+\nu(r)$ is its total number of tasks. An occupancy state is a point of $S = \{ s \in [0,1]^{\mathbb N^r} : \sum_\nu s(\nu) = 1 \}$, and the fraction of pools with at least $i$ tasks is
--   $$q(i) = \sum_{\Sigma(\nu) \ge i} s(\nu), \qquad i \ge 0.$$
--   4. **Thresholds.** $\lfloor x \rfloor_\Delta := \max\{k\Delta : k\Delta \le x,\ k \in \mathbb Z\}$.
--   5. **Mass processes** (7) and (22), with $\ell := \lfloor \rho \rfloor_\Delta$:
--   $$u = \sum_{i\ge 1} q(i),\quad x = \sum_{i=1}^{\ell} q(i),\quad y = \sum_{i=\ell+1}^{\ell+\Delta} q(i),\quad z = \sum_{i \ge \ell+\Delta+1} q(i).$$
--   6. **The constant** $\eta := \min\{(1-p_m)\mu_m : 1 \le m \le r\}$, a lower bound for the hazard rate of the service time.
--   7. **Residual survival functions and the fluid function (3).** $G_m(t)$ is the complementary distribution function of the residual service time of a task currently in phase $m$. With the limiting initial state $s(0) \in S$, $u^m(0) := \sum_{i\ge0} \nu_i(m)\, s(0,\nu_i)$ and
--   $$u(t) := \sum_{m=1}^{r} u^m(0)\, G_m(t) + \int_0^t \lambda\, G_1(t-s)\, ds .$$
--   8. A real path is **càdlàg** on $[0,\infty)$ if it is right-continuous at every $t \ge 0$ and has a left limit at every $t > 0$.
--
--   These are the objects in which Theorem 3 and Propositions 17 and 18 are stated: the threshold settles at $\lfloor\rho\rfloor_\Delta$, and the masses $x, y, z$ describe how balanced the load is.
--
--   **Formalization Note** Phases are indexed by `Fin r` (paper phase $m$ is index $m-1$). $q(i)$ is computed as $1 - \sum_{\Sigma(\nu)<i} s(\nu)$, a finite sum that equals $\sum_{\Sigma(\nu)\ge i} s(\nu)$ on $S$; $S$ membership uses `HasSum s 1`. $\lfloor x\rfloor_\Delta = \Delta\lfloor x/\Delta\rfloor$ (an integer). $G_m(t) := (e^{tQ}\mathbf 1)_m$ with the sub-generator $Q_{mm} = -\mu_m$, $Q_{m,m+1} = p_m\mu_m$, other entries $0$ (the phase-type representation of the Coxian law); equivalently $\dot G_m = -\mu_m G_m + p_m\mu_m G_{m+1}$, $G_m(0)=1$, $G_{r+1} := 0$. The sums $u$, $z$, $u^m(0)$ are real `tsum`s; they are only applied to finitely supported states (the solutions of the construction have finitely many tasks, and $s(0)$ vanishes on $\Sigma(\nu) > B$), where they are finite sums.
-- source:
--   Goldsztajn, Borst & van Leeuwaarden, Learning and balancing unknown loads in large-scale systems, arXiv:2012.10142v3, p. 8 (§2.1, Δ), p. 10 (⌊·⌋_Δ), pp. 13–14 (§3: Coxian phases, 1/µ, eq. (1), S, eq. (3)), p. 37 (profiles, enumeration), p. 41 (eq. (22)), p. 42 (η, Proposition 17's display)

import Mathlib

namespace UnknownLoads.Coxian

/-! Goldsztajn, Borst & van Leeuwaarden, *Learning and balancing unknown loads in large-scale
systems*, arXiv:2012.10142v3, §2.1 (p. 8), §2.2.1 (p. 10), §3 (pp. 12–14), §6 (pp. 37–42).
Standing data of the Coxian scenario: constant arrival rate `λ` per server pool, Coxian service
times with `r` phases, the integral parameter `Δ`, occupancy profiles and states, the masses (7)
and (22), the residual survival functions `G_m` and the fluid function (3).

Phases are indexed by `Fin r`: the paper's phase `m ∈ {1, …, r}` is index `m - 1`. -/

open MeasureTheory Filter Topology

/-- The standing data of §3 and §6 (constant arrival rate, Coxian service, basic learning).
* `r ≥ 1` phases; phase `m` lasts an exponential time of rate `μ m > 0`;
* after phase `m` a task moves to phase `m + 1` w.p. `p m`, leaves w.p. `1 - p m`; `p_r = 0` and
  `p m ∈ (0, 1)` for `m ≠ r` (p. 13);
* constant arrival rate `lam ≥ 0` per server pool (§4.2, "λ is constant over time");
* the integral parameter `Δ ≥ 1` of the dispatching rule (p. 8);
* a fixed enumeration `enum : ℕ ≃ ℕ^r` of the occupancy profiles, `ν_i = enum i` (p. 37). -/
structure Params where
  r : ℕ
  r_pos : 0 < r
  μ : Fin r → ℝ
  μ_pos : ∀ m, 0 < μ m
  p : Fin r → ℝ
  p_last : ∀ m : Fin r, m.val + 1 = r → p m = 0
  p_mem : ∀ m : Fin r, m.val + 1 ≠ r → 0 < p m ∧ p m < 1
  lam : ℝ
  lam_nonneg : 0 ≤ lam
  Δ : ℕ
  Δ_pos : 1 ≤ Δ
  enum : ℕ ≃ (Fin r → ℕ)

/-- An occupancy profile `ν ∈ ℕ^r`: `ν m` tasks in phase `m` (p. 37). -/
abbrev Profile (r : ℕ) := Fin r → ℕ

/-- `Σ ν = ν(1) + ⋯ + ν(r)`, the total number of tasks of a pool with profile `ν`. -/
def total {r : ℕ} (ν : Profile r) : ℕ := ∑ m, ν m

/-- The finite set of profiles with strictly fewer than `i` tasks in total. -/
def lowProfiles (r i : ℕ) : Finset (Profile r) :=
  (Fintype.piFinset fun _ : Fin r => Finset.range i).filter (fun ν => total ν < i)

/-- Membership in `S = {s ∈ [0,1]^{ℕ^r} : Σ_ν s(ν) = 1}` (p. 13). -/
def InS {r : ℕ} (s : Profile r → ℝ) : Prop :=
  (∀ ν, 0 ≤ s ν ∧ s ν ≤ 1) ∧ HasSum s 1

/-- `q(i) = Σ_{Σν ≥ i} s(ν)`, the fraction of pools with at least `i` tasks (eq. (1), p. 13),
written as `1 - Σ_{Σν < i} s(ν)` (a finite sum); the two agree on `S`. -/
def qOf {r : ℕ} (s : Profile r → ℝ) (i : ℕ) : ℝ :=
  1 - ∑ ν ∈ lowProfiles r i, s ν

/-- `⌊x⌋_Δ := max {kΔ : kΔ ≤ x, k ∈ ℤ}` (p. 10). -/
noncomputable def floorDelta (Δ : ℕ) (x : ℝ) : ℤ := (Δ : ℤ) * ⌊x / (Δ : ℝ)⌋

/-- The mean service time `1/μ = Σ_{i=1}^r (1 - p_i)(Π_{j<i} p_j) Σ_{k ≤ i} 1/μ_k` (p. 13). -/
noncomputable def meanService (P : Params) : ℝ :=
  ∑ i : Fin P.r, (1 - P.p i) * (∏ j ∈ Finset.univ.filter (fun j : Fin P.r => j < i), P.p j) *
    ∑ k ∈ Finset.univ.filter (fun k : Fin P.r => k ≤ i), 1 / P.μ k

/-- The offered load per server pool `ρ = λ/μ` (pp. 8, 13). -/
noncomputable def rho (P : Params) : ℝ := P.lam * meanService P

/-- `⌊ρ⌋_Δ` as a natural number (it is `≥ 0` because `ρ ≥ 0`). -/
noncomputable def ellStar (P : Params) : ℕ := (floorDelta P.Δ (rho P)).toNat

/-- `η := min {(1 - p_m) μ_m : 1 ≤ m ≤ r}` (p. 42). -/
noncomputable def eta (P : Params) : ℝ :=
  Finset.univ.inf' ⟨⟨0, P.r_pos⟩, Finset.mem_univ _⟩ (fun m : Fin P.r => (1 - P.p m) * P.μ m)

/-- The first phase (paper's phase 1). -/
def firstPhase (P : Params) : Fin P.r := ⟨0, P.r_pos⟩

/-- The sub-generator of the Coxian phase process: `Q m m = -μ_m`, `Q m (m+1) = p_m μ_m`. -/
noncomputable def subGenerator (P : Params) : Matrix (Fin P.r) (Fin P.r) ℝ :=
  fun m m' => if m' = m then -P.μ m else if m'.val = m.val + 1 then P.p m * P.μ m else 0

/-- `G_m(t)`, the complementary cumulative distribution function of the residual service time of
a task in phase `m` (p. 14): `G_m(t) = (exp(tQ) 𝟙)_m`. -/
noncomputable def Gsurv (P : Params) (m : Fin P.r) (t : ℝ) : ℝ :=
  Matrix.mulVec (NormedSpace.exp (t • subGenerator P)) (fun _ => (1 : ℝ)) m

/-- `u^m(0) := Σ_i ν_i(m) s(0, ν_i)`, the limiting normalized number of tasks in phase `m`. -/
noncomputable def phaseMass0 (P : Params) (s0 : Profile P.r → ℝ) (m : Fin P.r) : ℝ :=
  ∑' ν : Profile P.r, (ν m : ℝ) * s0 ν

/-- The fluid function (3) with constant `λ` (Proposition 17, p. 42):
`u(t) := Σ_m u^m(0) G_m(t) + ∫_0^t λ G_1(t - s) ds`. -/
noncomputable def fluidU (P : Params) (s0 : Profile P.r → ℝ) (t : ℝ) : ℝ :=
  ∑ m : Fin P.r, phaseMass0 P s0 m * Gsurv P m t +
    ∫ τ in (0 : ℝ)..t, P.lam * Gsurv P (firstPhase P) (t - τ)

/-- `u = Σ_{i ≥ 1} q(i)` (eq. (7)/(22)): total number of tasks normalized by `n`. -/
noncomputable def uMass {r : ℕ} (s : Profile r → ℝ) : ℝ := ∑' i : ℕ, qOf s (i + 1)

/-- `x = Σ_{i=1}^{⌊ρ⌋_Δ} q(i)` (22). -/
noncomputable def xMass (P : Params) (s : Profile P.r → ℝ) : ℝ :=
  ∑ i ∈ Finset.Icc 1 (ellStar P), qOf s i

/-- `y = Σ_{i=⌊ρ⌋_Δ+1}^{⌊ρ⌋_Δ+Δ} q(i)` (22). -/
noncomputable def yMass (P : Params) (s : Profile P.r → ℝ) : ℝ :=
  ∑ i ∈ Finset.Icc (ellStar P + 1) (ellStar P + P.Δ), qOf s i

/-- `z = Σ_{i ≥ ⌊ρ⌋_Δ+Δ+1} q(i)` (22). -/
noncomputable def zMass (P : Params) (s : Profile P.r → ℝ) : ℝ :=
  ∑' i : ℕ, qOf s (ellStar P + P.Δ + 1 + i)

/-- A real path is càdlàg on `[0, ∞)`: right-continuous at every `t ≥ 0` and with a left limit
at every `t > 0`. -/
def IsCadlagOn (f : ℝ → ℝ) : Prop :=
  ∀ t : ℝ, 0 ≤ t →
    ContinuousWithinAt f (Set.Ici t) t ∧ (0 < t → ∃ L : ℝ, Tendsto f (𝓝[<] t) (𝓝 L))

end UnknownLoads.Coxian


