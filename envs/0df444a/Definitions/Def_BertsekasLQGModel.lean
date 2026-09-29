-- Prove2me | Definitions.Def_BertsekasLQGModel
-- name    : BertsekasLQGModel
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-09-08T00:37:01.762741+00:00
-- url     : https://prove2.me/theorems/d41d3fe0-ad50-4fdb-8804-cc18b1969299
-- title:
--   The imperfect-information LQ model: trajectories, estimator, cost, Riccati gains
-- statement:
--   This module fixes the linear-quadratic problem with **imperfect state information** of Bertsekas, Vol. I, §5.2, together with the closed-loop process, the estimator, the cost and the Riccati gains.
--
--   **System and measurements.** Over a horizon $N > 0$,
--
--   $$x_{k+1} = A_k x_k + B_k u_k + w_k, \qquad z_k = C_k x_k + v_k,$$
--
--   with state $x_k \in \mathbb{R}^n$, control $u_k \in \mathbb{R}^m$ and measurement $z_k \in \mathbb{R}^q$. The initial state $x_0$, the system disturbances $w_k$ and the measurement noises $v_k$ are mutually independent, take finitely many values, and the disturbances and noises have zero mean.
--
--   **Cost.** With $Q_k$ positive semidefinite and $R_k$ positive definite,
--
--   $$J(\pi) \;=\; \mathbb{E}\Bigl[\, x_N^{\top} Q_N x_N \;+\; \sum_{k=0}^{N-1}\bigl(x_k^{\top} Q_k x_k + u_k^{\top} R_k u_k\bigr) \Bigr].$$
--
--   **Policies and the closed loop.** A policy maps the realized measurement history $I_k = (z_0, \dots, z_k)$ to the control $u_k = \pi(I_k)$; the closed-loop process then generates states and measurements by the two equations above.
--
--   **The estimator.** The least-squares state estimate given the information available at stage $k$ is the conditional expectation
--
--   $$\hat x_k \;=\; \mathbb{E}\bigl[x_k \mid I_k\bigr],$$
--
--   computed as the probability-weighted average of $x_k$ over the outcomes whose measurement history agrees with the realized one.
--
--   **Riccati matrices and gains.** The deterministic linear-quadratic recursion runs backward from $K_N = Q_N$,
--
--   $$K_k = A_k^{\top}\bigl(K_{k+1} - K_{k+1} B_k (B_k^{\top} K_{k+1} B_k + R_k)^{-1} B_k^{\top} K_{k+1}\bigr) A_k + Q_k, \qquad L_k = -\bigl(B_k^{\top} K_{k+1} B_k + R_k\bigr)^{-1} B_k^{\top} K_{k+1} A_k .$$
--
--   The gains $L_k$ are those of the perfect-information problem — they do not depend on the noise statistics at all, which is the first half of the separation phenomenon.
--
--   **Formalization Note** All randomness is finitely supported, so every expectation is a finite weighted sum and no measure theory is needed; independence is structural, since the sample space is the product of an initial-state coordinate with one disturbance and one noise coordinate per stage. Conditional expectation takes the junk value $0$ on events of zero probability, so statements about the estimator are guarded to outcomes of positive probability. Policies depend on the measurement list only; past controls are recoverable from it, so this is equivalent to the source's information vector for deterministic policies. No Gaussian assumption is made anywhere. Riccati matrices are indexed by remaining stages, with the stage index recovered by truncated natural-number subtraction; positive definiteness of $R_k$ makes every inverse in the gains genuine.
-- source:
--   D. P. Bertsekas, Dynamic Programming and Optimal Control, Vol. I, 3rd ed., Athena Scientific, 2005, Section 5.2; D. P. Bertsekas, Dynamic Programming and Optimal Control, Vol. I, 3rd ed., Athena Scientific, 2005, Appendix C / Section 5.2; D. P. Bertsekas, Dynamic Programming and Optimal Control, Vol. I, 3rd ed., Athena Scientific, 2005, Sections 4.1 and 5.2; D. P. Bertsekas, Dynamic Programming and Optimal Control, Vol. I, 3rd ed., Athena Scientific, 2005, Section 4.1, Eq. (4.3)

import Mathlib

open Matrix

/-- The finite-horizon linear-quadratic problem with imperfect state
information of Bertsekas, "Dynamic Programming and Optimal Control", Vol. I,
3rd ed., Section 5.2 (with disturbances taking finitely many values):
system `x_{k+1} = A_k x_k + B_k u_k + w_k`, measurements `z_k = C_k x_k + v_k`,
cost `E[x_Nᵀ Q_N x_N + ∑_k (x_kᵀ Q_k x_k + u_kᵀ R_k u_k)]`.
The initial state `x₀`, the system disturbances `w_k` and the measurement
noises `v_k` are mutually independent (this is built into the product form of
the sample space, `BertsekasLQGSample`) and the disturbances have zero mean. -/
structure BertsekasLQGModel (n m q : ℕ) (Ω₀ ΩW ΩV : Type)
    [Fintype Ω₀] [Fintype ΩW] [Fintype ΩV] where
  N : ℕ
  hN : 0 < N
  A : ℕ → Matrix (Fin n) (Fin n) ℝ
  B : ℕ → Matrix (Fin n) (Fin m) ℝ
  C : ℕ → Matrix (Fin q) (Fin n) ℝ
  Q : ℕ → Matrix (Fin n) (Fin n) ℝ
  R : ℕ → Matrix (Fin m) (Fin m) ℝ
  hQ : ∀ k, (Q k).PosSemidef
  hR : ∀ k, (R k).PosDef
  p0 : Ω₀ → ℝ
  pW : ℕ → ΩW → ℝ
  pV : ℕ → ΩV → ℝ
  x0 : Ω₀ → Fin n → ℝ
  w : ℕ → ΩW → Fin n → ℝ
  v : ℕ → ΩV → Fin q → ℝ
  hp0_nonneg : ∀ a, 0 ≤ p0 a
  hp0_sum : ∑ a, p0 a = 1
  hpW_nonneg : ∀ k a, 0 ≤ pW k a
  hpW_sum : ∀ k, ∑ a, pW k a = 1
  hpV_nonneg : ∀ k a, 0 ≤ pV k a
  hpV_sum : ∀ k, ∑ a, pV k a = 1
  hw_mean : ∀ k, ∑ a, pW k a • w k a = 0
  hv_mean : ∀ k, ∑ a, pV k a • v k a = 0

/-- The sample space of the imperfect-information linear-quadratic model: an
outcome consists of a value for the initial-state randomness, one system
disturbance per stage, and one measurement noise per stage.  The product
structure makes `x₀, w₀, …, w_{N-1}, v₀, …, v_{N-1}` mutually independent. -/
abbrev BertsekasLQGSample {n m q : ℕ} {Ω₀ ΩW ΩV : Type}
    [Fintype Ω₀] [Fintype ΩW] [Fintype ΩV]
    (M : BertsekasLQGModel n m q Ω₀ ΩW ΩV) : Type :=
  Ω₀ × (Fin M.N → ΩW) × (Fin M.N → ΩV)

/-- The probability of an outcome of the sample space: the product of the
probabilities of the initial-state randomness, of each system disturbance, and
of each measurement noise. -/
def BertsekasLQGProb {n m q : ℕ} {Ω₀ ΩW ΩV : Type}
    [Fintype Ω₀] [Fintype ΩW] [Fintype ΩV]
    (M : BertsekasLQGModel n m q Ω₀ ΩW ΩV)
    (ω : BertsekasLQGSample M) : ℝ :=
  M.p0 ω.1 * (∏ k : Fin M.N, M.pW k (ω.2.1 k)) *
    (∏ k : Fin M.N, M.pV k (ω.2.2 k))

/-- The closed-loop trajectory of the imperfect-information linear-quadratic
model under an (information-feedback) policy `π`.  A policy maps the current
information — the list of measurements `z₀, …, z_k` received so far — to the
control `u_k`.  `BertsekasLQGTraj M π k ω = (x_k, [z₀, …, z_k])`: the state at
stage `k` together with the accumulated measurement history. -/
def BertsekasLQGTraj {n m q : ℕ} {Ω₀ ΩW ΩV : Type}
    [Fintype Ω₀] [Fintype ΩW] [Fintype ΩV]
    (M : BertsekasLQGModel n m q Ω₀ ΩW ΩV)
    (π : List (Fin q → ℝ) → Fin m → ℝ) :
    ℕ → BertsekasLQGSample M → (Fin n → ℝ) × List (Fin q → ℝ)
  | 0, ω =>
      let x := M.x0 ω.1
      let z := M.C 0 *ᵥ x + (if h : 0 < M.N then M.v 0 (ω.2.2 ⟨0, h⟩) else 0)
      (x, [z])
  | k + 1, ω =>
      let prev := BertsekasLQGTraj M π k ω
      let u := π prev.2
      let x' := M.A k *ᵥ prev.1 + M.B k *ᵥ u +
        (if h : k < M.N then M.w k (ω.2.1 ⟨k, h⟩) else 0)
      let z' := M.C (k + 1) *ᵥ x' +
        (if h : k + 1 < M.N then M.v (k + 1) (ω.2.2 ⟨k + 1, h⟩) else 0)
      (x', prev.2 ++ [z'])

open Classical in
/-- Conditional expectation of a random vector `X` given an event `E`, on a
finite sample space with probability weights `p`: the `p`-weighted average of
`X` over the outcomes satisfying `E` (junk value `0` if the event has zero
probability). -/
noncomputable def BertsekasCondExpVec {Ω : Type} [Fintype Ω] {d : ℕ}
    (p : Ω → ℝ) (E : Ω → Prop) (X : Ω → Fin d → ℝ) : Fin d → ℝ :=
  (∑ ω ∈ Finset.univ.filter E, p ω)⁻¹ •
    ∑ ω ∈ Finset.univ.filter E, p ω • X ω

/-- The least-squares state estimate `E[x_k | I_k]` of Section 5.2: the
conditional expectation of the stage-`k` state given the realized measurement
history (the information vector), under the closed-loop process generated by
the policy `π`. -/
noncomputable def BertsekasLQGEstimate {n m q : ℕ} {Ω₀ ΩW ΩV : Type}
    [Fintype Ω₀] [Fintype ΩW] [Fintype ΩV]
    (M : BertsekasLQGModel n m q Ω₀ ΩW ΩV)
    (π : List (Fin q → ℝ) → Fin m → ℝ) (k : ℕ)
    (ω : BertsekasLQGSample M) : Fin n → ℝ :=
  BertsekasCondExpVec (BertsekasLQGProb M)
    (fun ω' => (BertsekasLQGTraj M π k ω').2 = (BertsekasLQGTraj M π k ω).2)
    (fun ω' => (BertsekasLQGTraj M π k ω').1)

/-- The expected quadratic cost of a policy `π` for the imperfect-information
linear-quadratic model:
`E[x_Nᵀ Q_N x_N + ∑_{k<N} (x_kᵀ Q_k x_k + u_kᵀ R_k u_k)]`. -/
noncomputable def BertsekasLQGCost {n m q : ℕ} {Ω₀ ΩW ΩV : Type}
    [Fintype Ω₀] [Fintype ΩW] [Fintype ΩV]
    (M : BertsekasLQGModel n m q Ω₀ ΩW ΩV)
    (π : List (Fin q → ℝ) → Fin m → ℝ) : ℝ :=
  ∑ ω : BertsekasLQGSample M, BertsekasLQGProb M ω *
    ((BertsekasLQGTraj M π M.N ω).1 ⬝ᵥ
        (M.Q M.N *ᵥ (BertsekasLQGTraj M π M.N ω).1) +
      ∑ k ∈ Finset.range M.N,
        ((BertsekasLQGTraj M π k ω).1 ⬝ᵥ
            (M.Q k *ᵥ (BertsekasLQGTraj M π k ω).1) +
          (π (BertsekasLQGTraj M π k ω).2) ⬝ᵥ
            (M.R k *ᵥ (π (BertsekasLQGTraj M π k ω).2))))

/-- The (time-varying) Riccati recursion of the deterministic linear-quadratic
problem underlying the certainty-equivalent controller (Sections 4.1 and 5.2):
`BertsekasLQGRiccati M j` is the cost matrix `K_{N-j}`, computed backward from
`K_N = Q_N` (index `j` counts remaining stages). -/
noncomputable def BertsekasLQGRiccati {n m q : ℕ} {Ω₀ ΩW ΩV : Type}
    [Fintype Ω₀] [Fintype ΩW] [Fintype ΩV]
    (M : BertsekasLQGModel n m q Ω₀ ΩW ΩV) : ℕ → Matrix (Fin n) (Fin n) ℝ
  | 0 => M.Q M.N
  | j + 1 =>
      let k := M.N - (j + 1)
      let P := BertsekasLQGRiccati M j
      (M.A k)ᵀ *
        (P - P * M.B k * ((M.B k)ᵀ * P * M.B k + M.R k)⁻¹ * (M.B k)ᵀ * P) *
        M.A k + M.Q k

/-- The feedback gain matrices of the linear-quadratic problem (Section 4.1,
Eq. (4.3), used again in Section 5.2):
`L_k = -(B_kᵀ K_{k+1} B_k + R_k)⁻¹ B_kᵀ K_{k+1} A_k`, where `K_{k+1}` is the
Riccati matrix with `N - k - 1` remaining stages. -/
noncomputable def BertsekasLQGGain {n m q : ℕ} {Ω₀ ΩW ΩV : Type}
    [Fintype Ω₀] [Fintype ΩW] [Fintype ΩV]
    (M : BertsekasLQGModel n m q Ω₀ ΩW ΩV) (k : ℕ) :
    Matrix (Fin m) (Fin n) ℝ :=
  let P := BertsekasLQGRiccati M (M.N - (k + 1));
  -(((M.B k)ᵀ * P * M.B k + M.R k)⁻¹ * (M.B k)ᵀ * P * M.A k)


