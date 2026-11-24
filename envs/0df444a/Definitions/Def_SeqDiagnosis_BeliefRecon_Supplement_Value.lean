-- Prove2me | Definitions.Def_SeqDiagnosis_BeliefRecon_Supplement_Value
-- name    : SeqDiagnosis_BeliefRecon_Supplement_Value
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-24T06:19:42.462823+00:00
-- url     : https://prove2.me/theorems/c94b3f1d-9e0a-4852-8323-9f39871deb60
-- title:
--   §2 (1), §3.2, Theorem 2 — costs, finite-horizon values $V_t$, stopping regions $\Gamma_{jt}$ and $\Omega_{jt}$, and the sets $\omega^i_t$, $\omega_s$
-- statement:
--   This file adds the decision layer of the sequential diagnosis problem on top of the published exponential tilting model and Bayesian operator.
--
--   A **cost structure** consists of termination costs $a_{ij}$ (true class $i$, diagnosis $j$) and delay costs $c_i$; its standing condition is $a_{ij}\ge0$, $c_i\ge0$ (§2, p. 6). The stopping value of class $j$ is $V^j(\Pi)=\sum_{i=0}^N\pi_ia_{ij}$. With $k$ periods to go the optimal cost is
--
--   $$W_0(\Pi)=\min_jV^j(\Pi),\qquad W_{k+1}(\Pi)=\min\Bigl\{\min_jV^j(\Pi),\ \sum_i\pi_ic_i+\int W_k\bigl(\mathcal B(\Pi,y)\bigr)\,\Pi F(y)\,d\mu(y)\Bigr\},$$
--
--   and for a horizon $T$ the value of period $t\le T$ is $V_t=W_{T-t}$, which is exactly the optimality equation (1) on p. 7. The stopping regions are
--
--   $$\Gamma_{jt}=\{\Pi\in S^N: V_t(\Pi)=V^j(\Pi)\},\qquad \Omega_{jt}=\{x\in\Omega_t: V_t(\mathcal T^t(x,\theta))=V^j(\mathcal T^t(x,\theta))\},$$
--
--   the latter being the stopping region in the diagnostic-statistic space of §3.2 (p. 13), with $J_t(x;\theta)=V_t(\mathcal T^t(x,\theta))$. Writing $e_i\mathbb Rx$ for row $i$ of $\mathbb Rx$ ($e_0$ is the null row, so $e_0\mathbb Rx=0$), Theorem 2's sets are
--
--   $$\omega^i_t(x^a)=\{x\in\Omega_t: e_j\mathbb R(x-x^a)=0\ \forall j\ne i,\ e_i\mathbb R(x-x^a)>0\},$$
--   $$\omega_s(x^a,x^b,t)=\{x\in\Omega_s: \mathcal T^s(x,\theta)=\rho\mathcal T^t(x^a,\theta)+(1-\rho)\mathcal T^t(x^b,\theta)\ \text{for some}\ \rho\in(0,1)\}.$$
--
--   These objects are shared by the structural results of §4.
--
--   **Formalization Note** The integral is the Bochner integral against the base reference measure $\mu$; ties between stopping and waiting count as stopping, as in the paper's definition of $\Gamma_{jt}$. The value is defined on all real vectors but is only used on the simplex.
-- source:
--   Wang, Optimal Sequential Multi-class Diagnosis, arXiv:1506.08915v4, p. 6 (PDF 6) costs; p. 7 (PDF 7), (1) and Γjt; pp. 12–13 (PDF 12–13), Jt and Ωjt; p. 15 (PDF 15), Theorem 2 sets

import Mathlib
import Definitions.Def_SeqDiagnosis_BeliefRecon_Model

open MeasureTheory Matrix

namespace SeqDiagnosis.BeliefRecon.Supplement

/-- Cost data of §2: `a i j` is the termination cost when the true class is `i` and the
diagnosis is `j`; `c i` is the per-period delay cost when the true class is `i`. -/
structure Costs (N : ℕ) where
  a : Fin (N + 1) → Fin (N + 1) → ℝ
  c : Fin (N + 1) → ℝ

/-- The standing sign conditions of §2: `a i j ≥ 0` and `c i ≥ 0`. -/
def Costs.Standing {N : ℕ} (C : Costs N) : Prop :=
  (∀ i j, 0 ≤ C.a i j) ∧ ∀ i, 0 ≤ C.c i

/-- Stopping value `V^j(q) = ∑ᵢ qᵢ aᵢⱼ` of diagnosing class `j` (the same in every period). -/
def stopValue {N : ℕ} (C : Costs N) (j : Fin (N + 1)) (q : Fin (N + 1) → ℝ) : ℝ :=
  ∑ i, q i * C.a i j

/-- Terminal value `min_j V^j(q)`. -/
noncomputable def termValue {N : ℕ} (C : Costs N) (q : Fin (N + 1) → ℝ) : ℝ :=
  Finset.univ.inf' Finset.univ_nonempty (fun j => stopValue C j q)

/-- Waiting value `∑ᵢ qᵢ cᵢ + ∫ W(ℬ(q,y)) qF(y) dμ(y)` for a continuation value `W`. -/
noncomputable def waitValue {Y : Type*} [MeasurableSpace Y] {N p : ℕ}
    (M : Model Y N p) (C : Costs N) (W : (Fin (N + 1) → ℝ) → ℝ)
    (q : Fin (N + 1) → ℝ) : ℝ :=
  ∑ i, q i * C.c i + ∫ y, W (bayes M.f q y) * (∑ i, q i * M.f i y) ∂M.μ

/-- Optimal cost with `k` periods to go, by backward recursion (1): with no period left the
decision maker must diagnose; otherwise the minimum of diagnosing and waiting. -/
noncomputable def valueToGo {Y : Type*} [MeasurableSpace Y] {N p : ℕ}
    (M : Model Y N p) (C : Costs N) : ℕ → (Fin (N + 1) → ℝ) → ℝ
  | 0 => termValue C
  | k + 1 => fun q => min (termValue C q) (waitValue M C (valueToGo M C k) q)

/-- `V_t` of (1) for horizon `T`: the value with `T - t` periods to go (used for `t ≤ T`). -/
noncomputable def value {Y : Type*} [MeasurableSpace Y] {N p : ℕ}
    (M : Model Y N p) (C : Costs N) (T t : ℕ) : (Fin (N + 1) → ℝ) → ℝ :=
  valueToGo M C (T - t)

/-- The stopping region `Γ_{jt} = {Π ∈ Sᴺ : V_t(Π) = V^j_t(Π)}` (ties count as stopping). -/
def Gamma {Y : Type*} [MeasurableSpace Y] {N p : ℕ}
    (M : Model Y N p) (C : Costs N) (T t : ℕ) (j : Fin (N + 1)) :
    Set (Fin (N + 1) → ℝ) :=
  {q | q ∈ stdSimplex ℝ (Fin (N + 1)) ∧ value M C T t q = stopValue C j q}

/-- The stopping region `Ω_{jt} = {x ∈ Ω_t : J_t(x;θ) = J^j_t(x;θ)}` in the diagnostic-statistic
space, where `J_t(x;θ) = V_t(𝒯ᵗ(x,θ))`. -/
def OmegaStop {Y : Type*} [MeasurableSpace Y] {N p r : ℕ}
    (M : Model Y N p) (C : Costs N) (R : Matrix (Fin N) (Fin r) ℝ)
    (P : Matrix (Fin r) (Fin p) ℝ) (θ : Fin (N + 1) → ℝ) (T t : ℕ) (j : Fin (N + 1)) :
    Set (Fin r → ℝ) :=
  {x | x ∈ Omega M P t ∧
    value M C T t (Tcal M R P t x θ) = stopValue C j (Tcal M R P t x θ)}

/-- `e_i ℝ x`: row `i` of `ℝ x` for a nonbaseline class, and `0` for class `0`
(the null row vector `e_0`). -/
def eRow {N r : ℕ} (R : Matrix (Fin N) (Fin r) ℝ) (i : Fin (N + 1)) (x : Fin r → ℝ) : ℝ :=
  Fin.cases (motive := fun _ => ℝ) 0 (fun k => (R *ᵥ x) k) i

/-- `ωⁱ_t(xᵃ) = {x ∈ Ω_t : e_jℝ(x − xᵃ) = 0 ∀ j ≠ i, e_iℝ(x − xᵃ) > 0}` (Theorem 2, part 1). -/
def omegaVertex {Y : Type*} [MeasurableSpace Y] {N p r : ℕ}
    (M : Model Y N p) (R : Matrix (Fin N) (Fin r) ℝ) (P : Matrix (Fin r) (Fin p) ℝ)
    (t : ℕ) (i : Fin (N + 1)) (xa : Fin r → ℝ) : Set (Fin r → ℝ) :=
  {x | x ∈ Omega M P t ∧ (∀ j, j ≠ i → eRow R j (x - xa) = 0) ∧ 0 < eRow R i (x - xa)}

/-- `ω_s(xᵃ, xᵇ, t) = {x ∈ Ω_s : 𝒯ˢ(x,θ) = ρ𝒯ᵗ(xᵃ,θ) + (1 − ρ)𝒯ᵗ(xᵇ,θ), ρ ∈ (0,1)}`
(Theorem 2, part 2). -/
def omegaCurve {Y : Type*} [MeasurableSpace Y] {N p r : ℕ}
    (M : Model Y N p) (R : Matrix (Fin N) (Fin r) ℝ) (P : Matrix (Fin r) (Fin p) ℝ)
    (θ : Fin (N + 1) → ℝ) (s t : ℕ) (xa xb : Fin r → ℝ) : Set (Fin r → ℝ) :=
  {x | x ∈ Omega M P s ∧ ∃ ρ ∈ Set.Ioo (0 : ℝ) 1,
    Tcal M R P s x θ = ρ • Tcal M R P t xa θ + (1 - ρ) • Tcal M R P t xb θ}

end SeqDiagnosis.BeliefRecon.Supplement


