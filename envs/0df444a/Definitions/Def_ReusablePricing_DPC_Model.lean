-- Prove2me | Definitions.Def_ReusablePricing_DPC_Model
-- name    : ReusablePricing_DPC_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-09T20:09:54.514177+00:00
-- url     : https://prove2.me/theorems/8842c9ef-cf0b-4b4a-880c-518ac656f334
-- title:
--   §3–§4, pp. 7–11 — the reusable-resource model, DET, A4–A5, n̲ of (2) and the θ-th system (1)
-- statement:
--   This file sets up the basic model of dynamic pricing with reusable resources of Lei and Jasin (§3), in the demand-rate formulation the paper itself uses for its deterministic relaxation.
--
--   **Instance data.** A firm manages $I$ resource types and offers $J$ service types over periods $t = 1, \dots, T$. A type-$j$ request occupies $a_{ij} \in \{0,1\}$ units of resource $i$ for $n$ consecutive periods (a *service cycle*), after which the units are free again. Resource $i$ has integer capacity $C_i \ge 1$. The firm posts a demand-rate vector $\lambda^t$ in the box
--   $$\Omega_\lambda = [0, \lambda_U]^J, \qquad 0 < \lambda_U \le 1,$$
--   and earns the revenue rate $r^t(\lambda^t)$. The data also contain a sequence $\lambda^{D} = (\lambda^{t,D})_t$, the deterministic optimal rates.
--
--   **DET.** For $t \ge 1$ write $(t-n+1)^+ = \max\{1, t-n+1\}$. A rate sequence $\lambda$ is feasible for DET (p. 9) when $\lambda^t \in \Omega_\lambda$ for $t \in [1,T]$ and
--   $$\sum_{s=(t-n+1)^+}^{t} \sum_{j} a_{ij} \lambda^s_j \le C_i \qquad \text{for all } t \in [1, T] \text{ and all } i;$$
--   it is optimal when it maximizes $\sum_{t=1}^T r^t(\lambda^t)$ among feasible sequences, and $J^D = \sum_{t=1}^T r^t(\lambda^{t,D})$. We also write $\min\{\max_i C_i, n\}$ for the quantity appearing in the paper's bounds.
--
--   **Standing hypotheses** (`Standing φL φU Ψ R n̲`), all from §3–§4:
--   1. *Model facts:* $I, J, n, T \ge 1$; $n$ divides $T$; $a_{ij} \in \{0,1\}$ and every column of $A$ contains a $1$; $C \succeq e$; $\lambda_U \in (0,1]$; and $J\lambda_U \le 1$.
--   2. $\lambda^D$ is an optimal solution of DET, and either $\lambda^{t,D}_j = 0$ or $\lambda^{t,D}_j \in (0, \lambda_U)$ for all $j$ and $t$ (p. 9).
--   3. *A4* with bound $R$: for every $t$, $r^t$ is strictly concave on $\Omega_\lambda$, $|r^t| \le R$ on $\Omega_\lambda$, and $r^t$ has a maximizer over $\Omega_\lambda$ lying in the interior of $\Omega_\lambda$.
--   4. *A5* with constants $\varphi_L, \varphi_U, \Psi > 0$: whenever $\lambda^{t,D}_j \in (0,\lambda_U)$, $[\lambda^{t,D}_j - \varphi_L, \lambda^{t,D}_j + \varphi_U] \subset (0, \lambda_U)$; and on the box $[\lambda^{t,D} - \varphi_L e, \lambda^{t,D} + \varphi_U e]$, $r^t$ is twice differentiable with $|\partial r^t/\partial \lambda_j| \le \Psi$ and $|v^\top \nabla^2 r^t\, v| \le \Psi \|v\|_2^2$ for all $v$.
--   5. $\underline n$ is the number of display (2): with $c_j(t)$ the number of periods $s \in [t, t+n-1]$ with $\lambda^{s,D}_j > 0$,
--   $$\underline n = \min\{c_j(t) : j \in [1,J],\ t \in [1, T-n+1],\ c_j(t) > 0\},$$
--   i.e. $\underline n = \min_j \underline n_j$.
--   6. Every service cycle $[t, t+n-1]$, $t \in [1, T-n+1]$, contains at least $\underline n$ periods in which $\lambda^{s,D}_j > 0$ for some $j$ (p. 11).
--
--   **The θ-th system** (display (1), p. 10). For an integer $\theta \ge 1$ the scaled instance has $T^{(\theta)} = \theta T$, $C^{(\theta)} = \theta C$, $n^{(\theta)} = \theta n$, revenue rate $r^{\lceil t/\theta \rceil}$ in period $t$, and the same $I, J, A, \lambda_U$.
--
--   These objects are shared by every statement of the mission.
--
--   **Formalization Note.** The paper's decisions are prices; A1 makes the demand rate invertible, and the paper rewrites DET and its proofs in rates. The model is stated in rates, so prices, A1–A3 and the $\partial p^t_j/\partial \lambda_j$ bound of A5 do not appear. The hypothesis $J\lambda_U \le 1$ is added: at most one request arrives per period (p. 7) and every vector of $\Omega_\lambda$ is attainable (pp. 8–9), so the arrival probabilities must sum to at most one. A4's unnamed bound is the explicit constant $R$. The Hessian bound is stated as a bound on the quadratic form, which for a symmetric Hessian is the eigenvalue bound. $\underline n$ is a predicate (minimum attained, lower bound for all demand-carrying cycles), so $\underline n \ge 1$ always holds; types without any demand-carrying cycle do not enter the minimum. The p. 11 assumption counts periods, following its prose. Periods are $1, \dots, T$; a window sum with upper limit below its lower limit is empty. $\theta$ is an integer, as the proof of Lemma 2 (EC.2) uses.
-- source:
--   Lei and Jasin, Real-Time Dynamic Pricing for Revenue Management with Reusable Resources, Advance Reservation, and Deterministic Service Time Requirements, Oper. Res. (2020), DOI 10.1287/opre.2019.1906 (author manuscript, SSRN 2816718), pp. 7–11, §3 Basic Model (A4, A5, DET, display (1)), §4 display (2)

import Mathlib

namespace ReusablePricing.DPC

open Finset

noncomputable section

/-- Instance data of the basic reusable-resource model (Lei–Jasin 2020, §3, pp. 7–9), in the
demand-rate formulation of DET (p. 9).

* `I` resource types, `J` service types, `T` periods (numbered `1, …, T`), service length `n`;
* `A i j ∈ {0,1}` units of resource `i` used by a type-`j` request for `n` consecutive periods;
* `C i` the (integer) capacity of resource `i`;
* `lamU` the upper end of the demand-rate box `Ω_λ = [0, λ_U]^J`;
* `r t` the revenue rate of period `t` as a function of the demand-rate vector;
* `lamD t` the deterministic optimal demand rate `λ^{t,D}` of period `t`. -/
structure Basic where
  I : ℕ
  J : ℕ
  T : ℕ
  n : ℕ
  A : Fin I → Fin J → ℕ
  C : Fin I → ℕ
  lamU : ℝ
  r : ℕ → (Fin J → ℝ) → ℝ
  lamD : ℕ → Fin J → ℝ

namespace Basic

variable (P : Basic)

/-- The feasible demand-rate set `Ω_λ = [0, λ_U]^J` (p. 8). -/
def OmegaLam : Set (Fin P.J → ℝ) := {x | ∀ j, 0 ≤ x j ∧ x j ≤ P.lamU}

/-- The first period `(t - n + 1)⁺ = max {1, t - n + 1}` of the length-`n` window ending at `t`
(p. 8). Natural-number subtraction `t + 1 - n` is `0` when `t < n`, and then the start is `1`. -/
def winStart (t : ℕ) : ℕ := max 1 (t + 1 - P.n)

/-- Feasibility for DET (p. 9): `λ^t ∈ Ω_λ` for `t ∈ [1, T]` and, for every `t ∈ [1, T]` and every
resource `i`, `∑_{s=(t-n+1)⁺}^{t} ∑_j a_{ij} λ^s_j ≤ C_i`. -/
def DETFeasible (x : ℕ → Fin P.J → ℝ) : Prop :=
  (∀ t ∈ Icc 1 P.T, x t ∈ P.OmegaLam) ∧
  ∀ t ∈ Icc 1 P.T, ∀ i : Fin P.I,
    ∑ s ∈ Icc (P.winStart t) t, ∑ j, (P.A i j : ℝ) * x s j ≤ (P.C i : ℝ)

/-- The DET objective `∑_{t=1}^T r^t(λ^t)`. -/
def DETObj (x : ℕ → Fin P.J → ℝ) : ℝ := ∑ t ∈ Icc 1 P.T, P.r t (x t)

/-- `x` is an optimal solution of DET. -/
def IsDETOptimal (x : ℕ → Fin P.J → ℝ) : Prop :=
  P.DETFeasible x ∧ ∀ y, P.DETFeasible y → P.DETObj y ≤ P.DETObj x

/-- The deterministic optimal value `J^D = ∑_{t=1}^T r^t(λ^{t,D})`. -/
def JD : ℝ := P.DETObj P.lamD

/-- `min {max_i C_i, n}` as a real number. -/
def minCapN : ℝ := min ((Finset.univ.sup P.C : ℕ) : ℝ) (P.n : ℝ)

/-- The model facts of §3 (pp. 7–9): `I, J, n, T ≥ 1`, `n ∣ T` (`T/n ∈ ℤ₊`), `a_{ij} ∈ {0,1}` with
a `1` in every column, `C ⪰ e`, `λ_U ∈ (0,1]`, and `J λ_U ≤ 1` (at most one request per period
under every attainable rate vector). -/
def ModelFacts : Prop :=
  1 ≤ P.I ∧ 1 ≤ P.J ∧ 1 ≤ P.n ∧ 1 ≤ P.T ∧ P.n ∣ P.T ∧
  (∀ i j, P.A i j ≤ 1) ∧ (∀ j, ∃ i, P.A i j = 1) ∧ (∀ i, 1 ≤ P.C i) ∧
  0 < P.lamU ∧ P.lamU ≤ 1 ∧ (P.J : ℝ) * P.lamU ≤ 1

/-- Assumption A4 (p. 8) for `t ∈ [1, T]`, with the explicit bound `R`: `r^t` is strictly concave
on `Ω_λ`, `|r^t| ≤ R` on `Ω_λ`, and `r^t` has a maximizer over `Ω_λ` in the interior of `Ω_λ`. -/
def A4 (R : ℝ) : Prop :=
  ∀ t ∈ Icc 1 P.T,
    StrictConcaveOn ℝ P.OmegaLam (P.r t) ∧
    (∀ x ∈ P.OmegaLam, |P.r t x| ≤ R) ∧
    ∃ xu : Fin P.J → ℝ, (∀ j, 0 < xu j ∧ xu j < P.lamU) ∧ ∀ x ∈ P.OmegaLam, P.r t x ≤ P.r t xu

/-- The without-loss-of-generality assumption of p. 9: `λ^{t,D}_j = 0` or `λ^{t,D}_j ∈ (0, λ_U)`. -/
def WLOGInterior : Prop :=
  ∀ t ∈ Icc 1 P.T, ∀ j, P.lamD t j = 0 ∨ (0 < P.lamD t j ∧ P.lamD t j < P.lamU)

/-- The box `[λ^{t,D} - φ_L e, λ^{t,D} + φ_U e]` of Assumption A5. -/
def Box (φL φU : ℝ) (t : ℕ) : Set (Fin P.J → ℝ) :=
  {x | ∀ j, P.lamD t j - φL ≤ x j ∧ x j ≤ P.lamD t j + φU}

/-- Assumption A5 (p. 9), revenue part: `φ_L, φ_U, Ψ > 0`; for `λ^{t,D}_j ∈ (0, λ_U)`,
`[λ^{t,D}_j - φ_L, λ^{t,D}_j + φ_U] ⊂ (0, λ_U)`; on the box, `r^t` is twice differentiable, its
partial derivatives are bounded by `Ψ` in absolute value, and its Hessian quadratic form satisfies
`|vᵀ ∇²r^t v| ≤ Ψ ‖v‖₂²` (absolute eigenvalues at most `Ψ`). -/
def A5 (φL φU Ψ : ℝ) : Prop :=
  0 < φL ∧ 0 < φU ∧ 0 < Ψ ∧
  ∀ t ∈ Icc 1 P.T,
    (∀ j, 0 < P.lamD t j → P.lamD t j < P.lamU →
        0 < P.lamD t j - φL ∧ P.lamD t j + φU < P.lamU) ∧
    ∀ x ∈ P.Box φL φU t,
      DifferentiableAt ℝ (P.r t) x ∧
      DifferentiableAt ℝ (fderiv ℝ (P.r t)) x ∧
      (∀ j, |fderiv ℝ (P.r t) x (Pi.single j 1)| ≤ Ψ) ∧
      ∀ v : Fin P.J → ℝ, |fderiv ℝ (fderiv ℝ (P.r t)) x v v| ≤ Ψ * ∑ j, v j ^ 2

/-- The number of periods `s ∈ [t, t + n - 1]` with `λ^{s,D}_j > 0`. -/
def cnt (j : Fin P.J) (t : ℕ) : ℕ :=
  ((Icc t (t + P.n - 1)).filter (fun s => 0 < P.lamD s j)).card

/-- `nl` is `n̲ = min_j n̲_j` of display (2), p. 11: the minimum of `cnt j t` over all types `j` and
cycle starts `t ∈ [1, T - n + 1]` whose cycle carries positive demand for `j`. Stated as a predicate
(lower bound attained), so `nl ≥ 1` always follows. -/
def IsNbar (nl : ℕ) : Prop :=
  (∀ j, ∀ t ∈ Icc 1 (P.T + 1 - P.n), 0 < P.cnt j t → nl ≤ P.cnt j t) ∧
  ∃ j, ∃ t ∈ Icc 1 (P.T + 1 - P.n), 0 < P.cnt j t ∧ P.cnt j t = nl

/-- The without-loss-of-generality assumption of p. 11: every service cycle `[t, t + n - 1]`,
`t ∈ [1, T - n + 1]`, contains at least `n̲` periods in which `λ^{s,D}_j > 0` for some `j`. -/
def CycleWLOG (nl : ℕ) : Prop :=
  ∀ t ∈ Icc 1 (P.T + 1 - P.n),
    nl ≤ ((Icc t (t + P.n - 1)).filter (fun s => ∃ j, 0 < P.lamD s j)).card

/-- The standing hypotheses of §3–§4: the model facts, `λ^D` optimal for DET, the WLOG of p. 9,
A4 (bound `R`), A5 (constants `φ_L, φ_U, Ψ`), `nl = n̲` (display (2)) and the WLOG of p. 11. -/
def Standing (φL φU Ψ R : ℝ) (nl : ℕ) : Prop :=
  P.ModelFacts ∧ P.IsDETOptimal P.lamD ∧ P.WLOGInterior ∧ P.A4 R ∧ P.A5 φL φU Ψ ∧
  P.IsNbar nl ∧ P.CycleWLOG nl

/-- The `θ`-th system of the asymptotic setting, display (1), p. 10, for an integer `θ ≥ 1`:
`T^(θ) = θ T`, `C^(θ) = θ C`, `n^(θ) = θ n`, and period `t` of the `θ`-th system has the revenue rate
`r^{⌈t/θ⌉}` of the unscaled system (`⌈t/θ⌉ = (t + θ - 1) / θ` in `ℕ`). `I`, `J`, `A`, `λ_U` are
unchanged. Its `lamD` field is the candidate `λ^{⌈t/θ⌉,D}` of Lemma 2. -/
def scale (θ : ℕ) : Basic where
  I := P.I
  J := P.J
  T := θ * P.T
  n := θ * P.n
  A := P.A
  C := fun i => θ * P.C i
  lamU := P.lamU
  r := fun t => P.r ((t + θ - 1) / θ)
  lamD := fun t => P.lamD ((t + θ - 1) / θ)

end Basic

end

end ReusablePricing.DPC


