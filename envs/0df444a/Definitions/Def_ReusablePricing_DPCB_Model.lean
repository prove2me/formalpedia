-- Prove2me | Definitions.Def_ReusablePricing_DPCB_Model
-- name    : ReusablePricing_DPCB_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-09T20:07:17.415766+00:00
-- url     : https://prove2.me/theorems/db8a383f-ecf2-49b6-b100-fef738c9a295
-- title:
--   §6 and §3, pp. 7–9, 17–18 — general reusable-resource model with lead times, DET-H, A4–A5, n̲_k of p. 18, the θ-th system (7)
-- statement:
--   This file sets up the general model of Section 6 of Lei and Jasin: reusable resources, heterogeneous service durations and advance reservation.
--
--   A firm manages $I$ resource types and sells $K \ge 1$ service types over periods $t = 1, \dots, T$. A request for type $k$ made at the beginning of period $t$ uses $a_{ik} \in \{0,1\}$ units of resource $i$ during the periods $t+\ell_k, \dots, t+\ell_k+n_k-1$: the service lasts $n_k \ge 1$ periods and starts $\ell_k \ge 0$ periods after the request. The capacities are integers $C_i \ge 1$, and every column of $A = (a_{ik})$ contains a $1$. The decision in period $t$ is a demand-rate vector $\lambda^t \in \Omega_\lambda = [0, \lambda_U]^K$, and $r^t(\lambda^t)$ is the revenue rate.
--
--   Write $W_k(t) = \{ s \in [1,T] : s + \ell_k \le t \le s + \ell_k + n_k - 1 \}$ for the request periods of type $k$ still in service at period $t$. The deterministic relaxation **DET-H** is
--   $$
--   J^D_H = \max_{\lambda^t \in \Omega_\lambda} \sum_{t=1}^T r^t(\lambda^t) \quad \text{s.t.} \quad \sum_{k=1}^K \sum_{s \in W_k(t)} a_{ik} \lambda^s_k \le C_i \quad \text{for all } i \text{ and } t \le T,
--   $$
--   and $\lambda^D = (\lambda^{t,D})_t$ denotes an optimal solution.
--
--   The file also defines:
--   1. the model facts: $I, K, T \ge 1$, $n_k \mid T$, the ordering (i) $n_1+\ell_1 \le \dots \le n_K+\ell_K$ and (ii) $\ell_k \le \ell_{k'}$ when $n_k+\ell_k = n_{k'}+\ell_{k'}$ and $k<k'$, $\lambda_U \in (0,1]$ and $K\lambda_U \le 1$;
--   2. Assumption A4 with bound $R$: on $\Omega_\lambda$, $r^t$ is strictly concave, satisfies $|r^t| \le R$, and has a maximizer in $(0,\lambda_U)^K$;
--   3. the convention of p. 9 that every $\lambda^{t,D}_k$ is $0$ or lies in $(0,\lambda_U)$;
--   4. Assumption A5 with positive constants $\varphi_L, \varphi_U, \Psi$: if $\lambda^{t,D}_k \in (0,\lambda_U)$ then $[\lambda^{t,D}_k - \varphi_L, \lambda^{t,D}_k + \varphi_U] \subset (0,\lambda_U)$, and on the box $[\lambda^{t,D} - \varphi_L e, \lambda^{t,D} + \varphi_U e]$ the function $r^t$ is twice differentiable with $|\partial r^t/\partial\lambda_k| \le \Psi$ and Hessian eigenvalues bounded by $\Psi$ in absolute value;
--   5. the minimum count of p. 18,
--   $$
--   \underline{n}_k = \min_{t \in [1, T-\ell_k-n_k+1] \,:\, \sum_{s=t+\ell_k}^{t+\ell_k+n_k-1} \lambda^{s,D}_k > 0} \bigl|\{ s \in [t+\ell_k, t+\ell_k+n_k-1] : \lambda^{s,D}_k > 0 \}\bigr|;
--   $$
--   6. the standing hypotheses of Section 6, which bundle 1–5 with the optimality of $\lambda^D$;
--   7. the $\theta$-th system of display (7): $T^{(\theta)} = \theta T$, $C^{(\theta)} = \theta C$, $n_k^{(\theta)} = \theta n_k$, $\ell_k^{(\theta)} = \theta\ell_k$, $r^{t,(\theta)} = r^{\lceil t/\theta \rceil}$.
--
--   These objects are the common ground of every statement of the mission.
--
--   **Formalization Note** Decisions are demand rates, as in the paper's own rate form of DET (p. 9); prices, A1–A3 and the price-derivative part of A5 never enter the proofs and are omitted. The page's index range $s = (t-n_k-\ell_k+1)^+, \dots, (t-\ell_k)^+$ is encoded as $W_k(t)$, which is empty for $t \le \ell_k$ (the literal $(x)^+ = \max\{1,x\}$ would count period 1 there). The hypothesis $K\lambda_U \le 1$ is implied by "at most one request per period" (p. 7) together with $\Omega_\lambda = [0,\lambda_U]^K$ being the set of attainable rates. The bound $R$ on $|r^t|$ stands in for the proofs' $r^u = \max_t \max_{\Omega_\lambda} r^t$. The Hessian bound is written $|v^\top \nabla^2 r^t v| \le \Psi \sum_k v_k^2$ for all $v$, which for a symmetric Hessian is the eigenvalue bound. $\underline{n}_k$ is a predicate on a candidate value $\underline{n}_k$ that requires the minimum to be attained, so every type has a demand-carrying service cycle inside the horizon. The scaled system takes an integer $\theta \ge 1$, with $\lceil t/\theta\rceil$ computed as $(t+\theta-1) \operatorname{div} \theta$.
-- source:
--   Lei and Jasin, Real-Time Dynamic Pricing for Revenue Management with Reusable Resources, Advance Reservation, and Deterministic Service Time Requirements, Oper. Res. (2020), DOI 10.1287/opre.2019.1906 (author manuscript, SSRN 2816718), pp. 7–9 (§3, Ω_λ, A4, A5, p. 9 convention), p. 17 (§6 The Setting, DET-H), p. 18 (display (7), definition of n̲_k)

import Mathlib

open Finset

namespace ReusablePricing.DPCB

/-- Instance data of the general setting of §6 (p. 17): `I` resource types, `K` service types,
`T` periods, service durations `n k`, advance-reservation lead times `ℓ k`, the 0–1 consumption
matrix `A`, integer capacities `C`, the rate cap `lamU` of `Ω_λ = [0, lamU]^K`, the revenue rates
`r t` (as functions of the demand-rate vector) and a solution `lamD` of DET-H. -/
structure General where
  I : ℕ
  K : ℕ
  T : ℕ
  n : Fin K → ℕ
  ℓ : Fin K → ℕ
  A : Fin I → Fin K → ℕ
  C : Fin I → ℕ
  lamU : ℝ
  r : ℕ → (Fin K → ℝ) → ℝ
  lamD : ℕ → Fin K → ℝ

namespace General

variable (P : General)

/-- The feasible rate set `Ω_λ = [0, λ_U]^K`. -/
def Omega : Set (Fin P.K → ℝ) := {x | ∀ k, 0 ≤ x k ∧ x k ≤ P.lamU}

/-- The periods `s ∈ [1, T]` whose type-`k` request is in service at period `t`: the service
`[s + ℓ_k, s + ℓ_k + n_k - 1]` covers `t`. This is the index range
`s ∈ [(t - n_k - ℓ_k + 1)⁺, (t - ℓ_k)⁺]` of OPT-H and DET-H, empty when `t ≤ ℓ_k`. -/
def window (k : Fin P.K) (t : ℕ) : Finset ℕ :=
  (Icc 1 P.T).filter (fun s => s + P.ℓ k ≤ t ∧ t < s + P.ℓ k + P.n k)

/-- Feasibility for DET-H (p. 17): `λ^t ∈ Ω_λ` for `t ∈ [1, T]`, and for every `t ∈ [1, T]` and
every resource `i`, `∑_k ∑_{s} a_ik λ^s_k ≤ C_i` over the window of `t`. -/
def DETHFeasible (lam : ℕ → Fin P.K → ℝ) : Prop :=
  (∀ t ∈ Icc 1 P.T, lam t ∈ P.Omega) ∧
    ∀ t ∈ Icc 1 P.T, ∀ i : Fin P.I,
      ∑ k, ∑ s ∈ P.window k t, (P.A i k : ℝ) * lam s k ≤ (P.C i : ℝ)

/-- The DET-H objective `∑_{t=1}^T r^t(λ^t)`. -/
def detValue (lam : ℕ → Fin P.K → ℝ) : ℝ := ∑ t ∈ Icc 1 P.T, P.r t (lam t)

/-- `lam` is an optimal solution of DET-H. -/
def IsOptDETH (lam : ℕ → Fin P.K → ℝ) : Prop :=
  P.DETHFeasible lam ∧ ∀ lam' : ℕ → Fin P.K → ℝ, P.DETHFeasible lam' → P.detValue lam' ≤ P.detValue lam

/-- The optimal DET-H value `J^D_H`, evaluated at the instance's solution `lamD`. -/
def JD : ℝ := P.detValue P.lamD

/-- `max_i C_i`, as a real number. -/
def maxC : ℝ := ((Finset.univ.sup P.C : ℕ) : ℝ)

/-- The model facts of §3 and §6: `I, K, T ≥ 1`; `n_k ≥ 1` and `n_k ∣ T`; the WLOG ordering
(i) `n_1 + ℓ_1 ≤ ⋯ ≤ n_K + ℓ_K` and (ii) ties broken by `ℓ`; `a_ik ∈ {0, 1}` with a `1` in every
column; `C ⪰ e`; `λ_U ∈ (0, 1]`; and `K λ_U ≤ 1` (at most one request per period). -/
structure ModelFacts : Prop where
  one_le_I : 1 ≤ P.I
  one_le_K : 1 ≤ P.K
  one_le_T : 1 ≤ P.T
  one_le_n : ∀ k, 1 ≤ P.n k
  n_dvd_T : ∀ k, P.n k ∣ P.T
  order_i : ∀ k k' : Fin P.K, k ≤ k' → P.n k + P.ℓ k ≤ P.n k' + P.ℓ k'
  order_ii : ∀ k k' : Fin P.K, P.n k + P.ℓ k = P.n k' + P.ℓ k' → k < k' → P.ℓ k ≤ P.ℓ k'
  A_le_one : ∀ i k, P.A i k ≤ 1
  A_col : ∀ k, ∃ i, P.A i k = 1
  one_le_C : ∀ i, 1 ≤ P.C i
  lamU_pos : 0 < P.lamU
  lamU_le_one : P.lamU ≤ 1
  K_mul_lamU_le_one : (P.K : ℝ) * P.lamU ≤ 1

/-- Assumption A4 (p. 8), for `t ∈ [1, T]`: `r^t` is strictly concave on `Ω_λ`, bounded by `R`
in absolute value on `Ω_λ`, and has a maximizer over `Ω_λ` in the interior `(0, λ_U)^K`. -/
def A4 (R : ℝ) : Prop :=
  ∀ t ∈ Icc 1 P.T, StrictConcaveOn ℝ P.Omega (P.r t) ∧ (∀ x ∈ P.Omega, |P.r t x| ≤ R) ∧
    ∃ xu : Fin P.K → ℝ, (∀ k, 0 < xu k ∧ xu k < P.lamU) ∧ ∀ x ∈ P.Omega, P.r t x ≤ P.r t xu

/-- The without-loss-of-generality convention of p. 9: every `λ^{t,D}_k` is `0` or in `(0, λ_U)`. -/
def DetWLOG : Prop :=
  ∀ t ∈ Icc 1 P.T, ∀ k, P.lamD t k = 0 ∨ (0 < P.lamD t k ∧ P.lamD t k < P.lamU)

/-- Assumption A5 (p. 9) for the revenue part, with positive constants `φL, φU, Ψ`: whenever
`λ^{t,D}_k ∈ (0, λ_U)`, `[λ^{t,D}_k - φL, λ^{t,D}_k + φU] ⊂ (0, λ_U)`; and on the box
`[λ^{t,D} - φL e, λ^{t,D} + φU e]`, `r^t` is twice differentiable, `|∂r^t/∂λ_k| ≤ Ψ`, and the
Hessian has absolute eigenvalues at most `Ψ`, written `|vᵀ ∇²r^t v| ≤ Ψ ‖v‖₂²`. -/
def A5 (φL φU Ψ : ℝ) : Prop :=
  0 < φL ∧ 0 < φU ∧ 0 < Ψ ∧
    (∀ t ∈ Icc 1 P.T, ∀ k, 0 < P.lamD t k → P.lamD t k < P.lamU →
      0 < P.lamD t k - φL ∧ P.lamD t k + φU < P.lamU) ∧
    ∀ t ∈ Icc 1 P.T, ∀ x : Fin P.K → ℝ,
      (∀ k, P.lamD t k - φL ≤ x k ∧ x k ≤ P.lamD t k + φU) →
        DifferentiableAt ℝ (P.r t) x ∧ DifferentiableAt ℝ (fderiv ℝ (P.r t)) x ∧
        (∀ k, |fderiv ℝ (P.r t) x (Pi.single k 1)| ≤ Ψ) ∧
        ∀ v : Fin P.K → ℝ, |fderiv ℝ (fderiv ℝ (P.r t)) x v v| ≤ Ψ * ∑ k, v k ^ 2

/-- The admissible starts of a type-`k` service cycle, `t ∈ [1, T - ℓ_k - n_k + 1]`. -/
def cycleStarts (k : Fin P.K) : Finset ℕ := Icc 1 (P.T + 1 - P.ℓ k - P.n k)

/-- `∑_{s = t + ℓ_k}^{t + ℓ_k + n_k - 1} λ^{s,D}_k`, the deterministic type-`k` demand of the cycle. -/
def cycleSum (k : Fin P.K) (t : ℕ) : ℝ :=
  ∑ s ∈ Icc (t + P.ℓ k) (t + P.ℓ k + P.n k - 1), P.lamD s k

/-- `|{λ^{s,D}_k : λ^{s,D}_k > 0, s ∈ [t + ℓ_k, t + ℓ_k + n_k - 1]}|`. -/
noncomputable def cycleCount (k : Fin P.K) (t : ℕ) : ℕ :=
  ((Icc (t + P.ℓ k) (t + P.ℓ k + P.n k - 1)).filter (fun s => 0 < P.lamD s k)).card

/-- `nl k` is `n̲_k` of p. 18: the minimum of `cycleCount k t` over the cycle starts `t` whose cycle
carries positive deterministic demand; the minimum is attained, so such a cycle exists. -/
def IsNbarK (nl : Fin P.K → ℕ) : Prop :=
  ∀ k, (∀ t ∈ P.cycleStarts k, 0 < P.cycleSum k t → nl k ≤ P.cycleCount k t) ∧
    ∃ t ∈ P.cycleStarts k, 0 < P.cycleSum k t ∧ P.cycleCount k t = nl k

/-- The standing hypotheses of §6: the model facts, `lamD` optimal for DET-H with the p. 9
convention, A4 with bound `R`, A5 with constants `φL, φU, Ψ`, and `nl = n̲`. -/
structure Standing (R Ψ φL φU : ℝ) (nl : Fin P.K → ℕ) : Prop where
  facts : P.ModelFacts
  opt : P.IsOptDETH P.lamD
  wlog : P.DetWLOG
  a4 : P.A4 R
  a5 : P.A5 φL φU Ψ
  nbar : P.IsNbarK nl

/-- The `θ`-th system of display (7), p. 18: `T^(θ) = θT`, `C^(θ) = θC`, `n_k^(θ) = θ n_k`,
`ℓ_k^(θ) = θ ℓ_k`, and `r^{t,(θ)} = r^{⌈t/θ⌉}`; its `lamD` is `λ^{⌈t/θ⌉,D}`. For `θ ≥ 1`,
`⌈t/θ⌉ = (t + θ - 1) / θ` in natural-number division. -/
def scale (θ : ℕ) : General where
  I := P.I
  K := P.K
  T := θ * P.T
  n := fun k => θ * P.n k
  ℓ := fun k => θ * P.ℓ k
  A := P.A
  C := fun i => θ * P.C i
  lamU := P.lamU
  r := fun t => P.r ((t + θ - 1) / θ)
  lamD := fun t => P.lamD ((t + θ - 1) / θ)

end General

end ReusablePricing.DPCB


