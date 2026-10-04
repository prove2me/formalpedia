-- Prove2me | Definitions.Def_CoffmanMitrani1980_Region_Model
-- name    : CoffmanMitrani1980_Region_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-04T08:52:28.331178+00:00
-- url     : https://prove2.me/theorems/b45c47e8-1be4-41ed-ae58-49815eb1f7b5
-- title:
--   §1 and §3 — class parameters, the set function of (4), the polytope H**, the preemptive priority vectors and their hull H
-- statement:
--   This file fixes the data of the single-server queueing model of Coffman and Mitrani and the two polytopes compared in their Theorem 2.
--
--   **Parameters.** A single server serves jobs of $M$ classes. Jobs of class $i$ arrive in a Poisson stream at rate $\lambda_i>0$ and have exponential service times with parameter $\mu_i>0$. The traffic intensity of class $i$ is $\rho_i=\lambda_i/\mu_i$, and the paper restricts attention to stable systems,
--   $$\rho=\sum_{i=1}^M\rho_i<1 .$$
--   Write $a_i=\rho_i/\mu_i$ and $V=\sum_{i=1}^M\lambda_i/\mu_i^2$. For a set $g$ of classes put
--   $$f(g)=\frac{\sum_{i\in g}a_i}{1-\sum_{i\in g}\rho_i},$$
--   whose denominator is positive; $f(\emptyset)=0$.
--
--   **The polytope $H^{**}$.** A performance vector $W=(W_1,\dots,W_M)$ lies in $H^{**}$ if it satisfies Kleinrock's conservation law (1),
--   $$\sum_{i=1}^M\rho_iW_i=\frac{V}{1-\rho},$$
--   and the $2^M-2$ inequalities (4): $\sum_{i\in g}\rho_iW_i\ge f(g)$ for every proper nonempty set $g$ of classes.
--
--   **Preemptive priority vectors.** A priority order lists the classes as $i_1,i_2,\dots,i_M$, class $i_1$ having the highest priority. With $S_k=\{i_1,\dots,i_k\}$ and $S_0=\emptyset$, the preemptive priority vector $P(i_1,\dots,i_M)$ has components
--   $$P(i_1,\dots,i_M)_{i_k}=\frac{f(S_k)-f(S_{k-1})}{\rho_{i_k}},\qquad k=1,\dots,M,$$
--   the unique solution of $\sum_{i\in S_k}\rho_iW_i=f(S_k)$, $k=1,\dots,M$ (the equations (5) for the chain of top sets).
--
--   **The hull $H$, (3).** $W\in H$ if there are $M$ preemptive priority vectors $P_1,\dots,P_M$ (repetitions allowed) and weights $\alpha_1,\dots,\alpha_M\ge0$ with $\sum_k\alpha_k=1$ and $W=\sum_k\alpha_kP_k$.
--
--   These objects are used by every statement of the mission.
--
--   **Formalization Note.** Classes are `Fin M`, numbered from $0$. The standing assumptions ($\lambda_i>0$, $\mu_i>0$, $\rho<1$) are fields of the structure `Params`. A priority order is a permutation `π : Equiv.Perm (Fin M)` with `π r` the class of rank `r`, rank $0$ being the highest priority, and `topSet π k` is the set of its $k$ highest-priority classes. The paper names the priority vectors without computing them; here they are given by the closed form above, which the proof of Lemma 2 identifies as the solution of (5). The conservation law is stated literally with $V$; that it is (4) at the full set with equality is a fact, not part of the definition.
-- source:
--   Coffman and Mitrani, A Characterization of Waiting Time Performance Realizable by Single-Server Queues, Operations Research 28 (1980), DOI 10.1287/opre.28.3.810, pp. 811-818: Section 1 (model, p. 811; stability, p. 812; conservation law (1), p. 813) and Section 3 ((3), p. 815; (4), pp. 816-817; H**, Lemma 2, p. 817; (5) and a_i, p. 818)

import Mathlib

namespace CoffmanMitrani1980.Region

open Finset

/-- The data of the queueing model of Coffman and Mitrani, *A Characterization of Waiting Time
Performance Realizable by Single-Server Queues*, Operations Research 28 (1980), §1, p. 811 (PDF 3)
and p. 812–813 (PDF 4–5): a single server, `M` job classes, class `i` arriving in a Poisson stream
at rate `lam i` with exponential service times of parameter `mu i`, together with the standing
assumptions of the paper: every rate is positive ("at rate λᵢ", "with parameter μᵢ"), and the total
traffic intensity `ρ = Σ λᵢ/μᵢ` is below `1`, "the condition for the existence of a stationary
distribution" (p. 812), the only systems the paper considers.

**Formalization Note.** Classes are indexed by `Fin M`, numbered from `0`: the paper's class `i`
is `i - 1` here. Only the numerical parameters enter the statements of this mission; the stochastic
model itself is not formalized. -/
structure Params (M : ℕ) where
  /-- arrival rate `λᵢ` of class `i` -/
  lam : Fin M → ℝ
  /-- service rate `μᵢ` of class `i` (mean service time `1/μᵢ`) -/
  mu : Fin M → ℝ
  lam_pos : ∀ i, 0 < lam i
  mu_pos : ∀ i, 0 < mu i
  /-- stability: `ρ = Σᵢ λᵢ/μᵢ < 1` (p. 812) -/
  load_lt_one : ∑ i, lam i / mu i < 1

/-- Traffic intensity of class `i`, `ρᵢ = λᵢ/μᵢ` (p. 811). -/
noncomputable def Params.rho {M : ℕ} (p : Params M) (i : Fin M) : ℝ := p.lam i / p.mu i

/-- The coefficient `aᵢ = ρᵢ/μᵢ` of the proof of Lemma 2 (p. 818). -/
noncomputable def Params.a {M : ℕ} (p : Params M) (i : Fin M) : ℝ := p.rho i / p.mu i

/-- The constant `V = Σᵢ λᵢ/μᵢ²` of the conservation law (1) (p. 813). -/
noncomputable def Params.V {M : ℕ} (p : Params M) : ℝ := ∑ i, p.lam i / p.mu i ^ 2

/-- The right-hand side of the inequalities (4) (pp. 816–817), as a function of the set of classes
`g`: `f(g) = (Σ_{i∈g} ρᵢ/μᵢ) / (1 - Σ_{i∈g} ρᵢ)`. The denominator is positive for every `g`
because `Σ_{i∈g} ρᵢ ≤ ρ < 1`. `f(∅) = 0`, the paper's convention "If g₁₂ is empty, we shall define
all sums involved in (4) as zero" (p. 818). -/
noncomputable def Params.f {M : ℕ} (p : Params M) (g : Finset (Fin M)) : ℝ :=
  (∑ i ∈ g, p.a i) / (1 - ∑ i ∈ g, p.rho i)

/-- **H\*\*** (Lemma 2, p. 817, PDF 9): the set of performance vectors `W = (W₁, …, W_M)` which
satisfy the conservation law (1), `Σᵢ ρᵢ Wᵢ = V/(1 - ρ)` (p. 813), and the `2^M - 2` inequalities
(4), `Σ_{i∈g} ρᵢ Wᵢ ≥ f(g)` for every proper nonempty subset `g` of the classes.

**Formalization Note.** (1) is stated literally with `V` and `ρ = Σᵢ ρᵢ`; that it is the case
`g = univ` of (4) with equality is a fact, not part of the definition. This set replaces the paper's
H\* ("achievable by some scheduling strategy"), which rests on a strategy class described only in
prose. -/
def Params.Hss {M : ℕ} (p : Params M) : Set (Fin M → ℝ) :=
  {W | ∑ i, p.rho i * W i = p.V / (1 - ∑ i, p.rho i) ∧
    ∀ g : Finset (Fin M), g.Nonempty → g ≠ univ → p.f g ≤ ∑ i ∈ g, p.rho i * W i}

/-- The `k` highest-priority classes of the priority order `π`: `{π 0, …, π (k-1)}`.

**Formalization Note.** A priority order is a permutation `π : Equiv.Perm (Fin M)` with `π r` the
class of rank `r`, rank `0` being the highest priority; the paper's `P(i₁, i₂, …, i_M)` (class `i₁`
first) has `π 0 = i₁ - 1`, `π 1 = i₂ - 1`, …. -/
def topSet {M : ℕ} (π : Equiv.Perm (Fin M)) (k : ℕ) : Finset (Fin M) :=
  (univ.filter fun j : Fin M => (j : ℕ) < k).image π

/-- The **preemptive priority vector** `P(i₁, …, i_M)` (p. 815, PDF 7), the performance vector of the
discipline giving preemptive priority to class `i₁`, then `i₂`, and so on. With `S_k = {i₁, …, i_k}`
and `S₀ = ∅`, its component for the class of rank `k` is
`P_{i_k} = (f(S_k) - f(S_{k-1})) / ρ_{i_k}`, the unique solution of the equations (5) for the chain
`S₁ ⊂ S₂ ⊂ ⋯ ⊂ S_M` (end of the proof of Lemma 2, p. 818, PDF 10).

**Formalization Note.** The paper names these vectors and never computes them; the closed form here is
the solution of (5) for the chain of top sets, the identification the proof of Lemma 2 makes. For
the class `i` of rank `r = π⁻¹ i`, `S_{r+1} = topSet π (r+1)` and `S_r = topSet π r`. The division
is by `ρᵢ > 0`. -/
noncomputable def Params.prioVec {M : ℕ} (p : Params M) (π : Equiv.Perm (Fin M)) : Fin M → ℝ :=
  fun i => (p.f (topSet π ((π.symm i : ℕ) + 1)) - p.f (topSet π (π.symm i : ℕ))) / p.rho i

/-- **H**, (3) (p. 815, PDF 7): `W ∈ H` iff there exist `M` points `P₁, …, P_M` from the set of the
`M!` preemptive priority vectors and numbers `α₁, …, α_M ≥ 0` with `α₁ + ⋯ + α_M = 1` and
`W = Σᵢ αᵢ Pᵢ`.

**Formalization Note.** The `M` points are `prioVec (σ k)`, `k : Fin M`, for an arbitrary map
`σ : Fin M → Equiv.Perm (Fin M)`, so repetitions are allowed, as (3) allows. The paper's "α_m" is a
misprint for `α_M`. -/
def Params.H {M : ℕ} (p : Params M) : Set (Fin M → ℝ) :=
  {W | ∃ (σ : Fin M → Equiv.Perm (Fin M)) (α : Fin M → ℝ),
    (∀ k, 0 ≤ α k) ∧ ∑ k, α k = 1 ∧ W = ∑ k, α k • p.prioVec (σ k)}

end CoffmanMitrani1980.Region


