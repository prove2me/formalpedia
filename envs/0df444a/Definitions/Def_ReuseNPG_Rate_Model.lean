-- Prove2me | Definitions.Def_ReuseNPG_Rate_Model
-- name    : ReuseNPG_Rate_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-21T00:29:25.297764+00:00
-- url     : https://prove2.me/theorems/7863cea3-8d5c-4bc7-9b1e-4cc86984a494
-- title:
--   §2–§4, pp. 4–11 — RNPG estimators, run, assumptions, and asymptotic covariance
-- statement:
--   For a policy parameter $\theta$, let $G(\xi,\theta)$ be the score-weighted advantage and $S(\xi,\theta)$ the outer product of the score. From a batch of $B$ occupancy samples, $\hat F^{-1}(\theta)$ is the inverse of the empirical Fisher matrix plus $\epsilon I$, with $\epsilon>0$. Historical gradient samples are reweighted by the ratio of current to drawing-time occupancy densities. The RNPG update projects the step formed from this reused gradient estimate and a separate current inverse-Fisher batch onto the feasible set.
--
--   The file computes the covariance matrices from the model:
--
--   $$
--   \Sigma_1=\bar F^{-1}\Sigma_\eta(\bar F^{-1})^T,\qquad
--   \Sigma_2=\Sigma'_2-\Sigma_1,\qquad
--   \hat\Sigma=\frac{\Sigma_1}{B}+\frac{\Sigma_2}{KB},
--   \qquad
--   \operatorname{vec}(\Sigma_\infty)=-(\mathcal G\oplus\mathcal G)^{-1}\operatorname{vec}(\hat\Sigma).
--   $$
--
--   It states Assumptions 1 and 2, the RNPG run's sampling law, nearest-point projection, the noise terms $L_n$ and $R_n$, and the simultaneous two-index conditional Cesàro limit. These definitions are the common interface for Theorem 2 and Lemmas 4–6.
--
--   **Formalization Note** Finite sums represent expectations over states, actions, and batches. A separate Fisher batch realizes Assumption 1(A.1.7). Before $K$ batches exist, the estimator averages those available. Conditional matrix expectations are entrywise. The condition $\bar\theta\in\operatorname{interior}\Theta$ is a separate theorem hypothesis. Continuity of the finite sample functions represents Assumption 2(A.2.4).
-- source:
--   Lin, Wang & Zhou, Reusing historical trajectories in natural policy gradient via importance sampling, arXiv:2403.00675v2, pp. 4–5 and 7–11, §2.3, equations (3)–(6), Algorithm 1, Assumptions 1–2, Theorem 2

import Mathlib
import Definitions.Def_ReuseNPG_Rate_MDP

open MeasureTheory Filter ProbabilityTheory
open scoped BigOperators
open scoped Topology

namespace ReuseNPG.Rate

variable {S A : Type*} [Fintype S] [Fintype A] [DecidableEq S] [DecidableEq A]
  {d B K : ℕ}

abbrev E (d : ℕ) := EuclideanSpace ℝ (Fin d)
abbrev DMat (d : ℕ) := Matrix (Fin d) (Fin d) ℝ

/-- The score ∇ log πθ(a|s), interpreted as ∇π/π on the positive support. -/
noncomputable def score (π : E d → S → A → ℝ) (θ : E d) (ξ : S × A) : E d :=
  (π θ ξ.1 ξ.2)⁻¹ • gradient (fun t => π t ξ.1 ξ.2) θ

/-- G(ξ,θ) in §2.3, p. 4. -/
noncomputable def gradSample (M : MDP S A) (π : E d → S → A → ℝ)
    (θ : E d) (ξ : S × A) : E d :=
  ((1 - M.γ)⁻¹ * Adv M π θ ξ.1 ξ.2) • score π θ ξ

/-- S(ξ,θ), the outer product of the policy score, p. 4. -/
noncomputable def fisherSample (π : E d → S → A → ℝ)
    (θ : E d) (ξ : S × A) : DMat d :=
  Matrix.vecMulVec (fun i => score π θ ξ i) (fun i => score π θ ξ i)

/-- Finite expectation of a statistic of B independent occupancy samples. -/
noncomputable def batchExp (M : MDP S A) (π : E d → S → A → ℝ)
    (θ : E d) (f : (Fin B → S × A) → DMat d) : DMat d :=
  ∑ x : Fin B → S × A, (∏ i : Fin B, occ M π θ (x i)) • f x

/-- The inverse of the regularized empirical Fisher information, p. 7. -/
noncomputable def FhatInv (π : E d → S → A → ℝ) (ε : ℝ)
    (θ : E d) (x : Fin B → S × A) : DMat d :=
  (ε • (1 : DMat d) + (B : ℝ)⁻¹ • ∑ i : Fin B, fisherSample π θ (x i))⁻¹

/-- The mean inverse FIM F̄⁻¹(θ), Assumption 2(A.2.2), p. 10. -/
noncomputable def FbarInv (M : MDP S A) (π : E d → S → A → ℝ)
    (ε : ℝ) (θ : E d) : DMat d :=
  batchExp (B := B) M π θ (FhatInv (B := B) π ε θ)

/-- Mean of the per-sample gradient G under d^{πθ}; this is not defined as ∇η. -/
noncomputable def meanG (M : MDP S A) (π : E d → S → A → ℝ)
    (θ : E d) : E d :=
  ∑ ξ : S × A, occ M π θ ξ • gradSample M π θ ξ

/-- Ση(θ)=Var(G(ξ,θ)), Assumption 2(A.2.2), p. 10. -/
noncomputable def SigmaEta (M : MDP S A) (π : E d → S → A → ℝ)
    (θ : E d) : DMat d :=
  ∑ ξ : S × A, occ M π θ ξ •
    Matrix.vecMulVec
      (fun i => (gradSample M π θ ξ - meanG M π θ) i)
      (fun i => (gradSample M π θ ξ - meanG M π θ) i)

/-- Σ₁(θ), p. 10. -/
noncomputable def Sigma1 (M : MDP S A) (π : E d → S → A → ℝ)
    (ε : ℝ) (θ : E d) : DMat d :=
  FbarInv (B := B) M π ε θ * SigmaEta M π θ * (FbarInv (B := B) M π ε θ).transpose

/-- Σ₂′(θ), p. 10. -/
noncomputable def Sigma2Prime (M : MDP S A) (π : E d → S → A → ℝ)
    (ε : ℝ) (θ : E d) : DMat d :=
  batchExp (B := B) M π θ (fun x =>
    FhatInv π ε θ x * SigmaEta M π θ * (FhatInv π ε θ x).transpose)

/-- Σ₂=Σ₂′−Σ₁, Theorem 2, p. 11. -/
noncomputable def Sigma2 (M : MDP S A) (π : E d → S → A → ℝ)
    (ε : ℝ) (θ : E d) : DMat d :=
  Sigma2Prime (B := B) M π ε θ - Sigma1 (B := B) M π ε θ

/-- The covariance Σ̂(θ)=Σ₁(θ)/B+Σ₂(θ)/(KB), Theorem 2, p. 11. -/
noncomputable def SigmaHat (M : MDP S A) (π : E d → S → A → ℝ)
    (ε : ℝ) (θ : E d) : DMat d :=
  (B : ℝ)⁻¹ • Sigma1 (B := B) M π ε θ +
    ((K : ℝ) * B)⁻¹ • Sigma2 (B := B) M π ε θ

/-- Hurwitz means all complex eigenvalues have negative real part, p. 11. -/
def IsHurwitz (Gm : DMat d) : Prop :=
  ∀ z : ℂ, (Gm.map (fun x : ℝ => (x : ℂ)) - z • (1 : Matrix (Fin d) (Fin d) ℂ)).det = 0 →
    z.re < 0

/-- The Kronecker sum G⊕G with column-major vectorization. -/
noncomputable def kroneckerSum (Gm : DMat d) : Matrix (Fin d × Fin d) (Fin d × Fin d) ℝ :=
  fun p q => (if p.1 = q.1 then Gm p.2 q.2 else 0) +
    (if p.2 = q.2 then Gm p.1 q.1 else 0)

/-- The stationary covariance specified by vec Σ∞=−(G⊕G)⁻¹ vec Σ̂, p. 11. -/
noncomputable def SigmaInf (Gm Cov : DMat d) : DMat d :=
  fun i j => -(Matrix.mulVec (kroneckerSum Gm)⁻¹
    (fun p : Fin d × Fin d => Cov p.2 p.1)) (j, i)

/-- Last min(n+1,K) iterations; for n<K−1 use all available batches. -/
def window (K n : ℕ) : Finset ℕ := Finset.Icc (n + 1 - min (n + 1) K) n

/-- The reused importance-weighted gradient estimator (3)–(4), p. 4. -/
noncomputable def gradEst (M : MDP S A) (π : E d → S → A → ℝ)
    (B K : ℕ) (θs : ℕ → E d) (ξs : ℕ → Fin B → S × A) (n : ℕ) : E d :=
  (((min (n + 1) K : ℕ) : ℝ) * B)⁻¹ •
    ∑ m ∈ window K n, ∑ i : Fin B,
      (occ M π (θs n) (ξs m i) / occ M π (θs m) (ξs m i)) •
        gradSample M π (θs n) (ξs m i)

/-- z is a nearest-point projection of y onto Θ, equation (6), p. 5. -/
def IsProj (Θ : Set (E d)) (y z : E d) : Prop :=
  z ∈ Θ ∧ ∀ w ∈ Θ, dist y z ≤ dist y w

/-- A run of Algorithm 1 with separate fresh FIM and gradient batches (A.1.7).
The conditional-law identity includes their mutual independence. -/
structure IsRNPGRun (M : MDP S A) (π : E d → S → A → ℝ)
    (Θ : Set (E d)) (α : ℕ → ℝ) (ε : ℝ) (θ0 : E d)
    [MeasurableSpace S] [MeasurableSpace A]
    {Ω : Type*} {m0 : MeasurableSpace Ω} (P : Measure Ω) (ℱ : Filtration ℕ m0)
    (θ : ℕ → Ω → E d) (ξ ζ : ℕ → Ω → Fin B → S × A) : Prop where
  init : ∀ ω, θ 0 ω = θ0
  measurable_θ : ∀ n, Measurable (θ n)
  measurable_ξ : ∀ n, Measurable (ξ n)
  measurable_ζ : ∀ n, Measurable (ζ n)
  adapted_θ : ∀ n, Measurable[ℱ n] (θ n)
  adapted_ξ : ∀ n, Measurable[ℱ (n+1)] (ξ n)
  adapted_ζ : ∀ n, Measurable[ℱ (n+1)] (ζ n)
  step : ∀ n ω,
    IsProj Θ
      (θ n ω + α n • Matrix.toEuclideanLin (FhatInv π ε (θ n ω) (ζ n ω))
        (gradEst M π B K (fun m => θ m ω) (fun m => ξ m ω) n))
      (θ (n+1) ω)
  sampling : ∀ n (x y : Fin B → S × A) (H : Set Ω),
    @MeasurableSet Ω (ℱ n) H →
      (P (H ∩ {ω | ξ n ω = x ∧ ζ n ω = y})).toReal =
        ∫ ω in H, (∏ i : Fin B, occ M π (θ n ω) (x i)) *
          (∏ i : Fin B, occ M π (θ n ω) (y i)) ∂P

/-- Assumption 1, p. 7. (A.1.2) is automatic for finite S×A; (A.1.7)
is encoded in `IsRNPGRun.sampling`. -/
structure Assumption1 (M : MDP S A) (π : E d → S → A → ℝ)
    (Θ : Set (E d)) (α : ℕ → ℝ) : Prop where
  /-- (A.1.1) -/
  steps_pos : ∀ n, 0 < α n
  steps_sq_summable : Summable (fun n => (α n)^2)
  steps_nonsummable : ¬ Summable α
  steps_zero : Tendsto α atTop (𝓝 0)
  /-- (A.1.3): pointwise differentiability and uniform Lipschitz and gradient bounds. -/
  policy_diff : ∀ s a, Differentiable ℝ (fun t => π t s a)
  policy_grad_bounds : ∃ L U : ℝ, 0 ≤ L ∧ 0 ≤ U ∧
    (∀ θ₁ ∈ Θ, ∀ θ₂ ∈ Θ, ∀ s a,
      ‖gradient (fun t => π t s a) θ₁ - gradient (fun t => π t s a) θ₂‖ ≤
        L * ‖θ₁ - θ₂‖) ∧
    (∀ θ ∈ Θ, ∀ s a, ‖gradient (fun t => π t s a) θ‖ ≤ U)
  /-- (A.1.4): Lipschitz in total variation. -/
  policy_tv : ∃ U : ℝ, 0 < U ∧
    ∀ θ₁ ∈ Θ, ∀ θ₂ ∈ Θ, ∀ s,
      (1/2 : ℝ) * ∑ a : A, |π θ₁ s a - π θ₂ s a| ≤ U * ‖θ₁ - θ₂‖
  /-- (A.1.5): common positive occupancy lower bound. -/
  occ_pos : ∃ εd : ℝ, 0 < εd ∧ ∀ θ ∈ Θ, ∀ ξ : S × A, εd ≤ occ M π θ ξ
  /-- (A.1.6): compact convex feasible set. -/
  feasible : Θ.Nonempty ∧ IsCompact Θ ∧ Convex ℝ Θ

/-- Assumption 2, p. 10; `θbar ∈ interior Θ` is separately declared on every
theorem using this assumption, because the printed CLT is false at a boundary limit. -/
structure Assumption2 (M : MDP S A) (π : E d → S → A → ℝ)
    (Θ : Set (E d)) (α : ℕ → ℝ) (ε : ℝ)
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (θ : ℕ → Ω → E d) (θbar : E d) (Gm : DMat d) : Prop where
  /-- (A.2.1) -/
  limit_mem : θbar ∈ Θ
  limit_ae : ∀ᵐ ω ∂P, Tendsto (fun n => θ n ω) atTop (𝓝 θbar)
  /-- (A.2.2) -/
  covariance_cont : ContinuousOn (SigmaEta M π) Θ
  inverse_fim_cont : ContinuousOn (FbarInv (B := B) M π ε) Θ
  /-- (A.2.3) -/
  hurwitz : IsHurwitz Gm
  linearization :
    (fun t => Matrix.toEuclideanLin (FbarInv (B := B) M π ε t) (gradient (eta M π) t) -
      Matrix.toEuclideanLin Gm (t - θbar)) =o[𝓝 θbar] (fun t => t - θbar)
  /-- (A.2.4), pointwise continuity in the finite state-action model. -/
  sample_cont : ∀ ξ : S × A,
    ContinuousAt (fun t => fisherSample π t ξ) θbar ∧
    ContinuousAt (fun t => gradSample M π t ξ) θbar
  /-- (A.2.5) -/
  steps_sq_summable : Summable (fun n => (α n)^2)
  steps_nonsummable : ¬ Summable α
  steps_zero : Tendsto α atTop (𝓝 0)
  steps_pos : ∀ n, 0 < α n
  steps_ratio : (fun n => Real.sqrt (α n / α (n+1)) - 1) =o[atTop] α

/-- L_n in Lemma 4, p. 12: the fresh-batch gradient fluctuation. -/
noncomputable def Lnoise (M : MDP S A) (π : E d → S → A → ℝ)
    {Ω : Type*} (ε : ℝ) (θ : ℕ → Ω → E d) (ξ : ℕ → Ω → Fin B → S × A)
    (n : ℕ) (ω : Ω) : E d :=
  Matrix.toEuclideanLin (FbarInv (B := B) M π ε (θ n ω))
    (((K : ℝ) * B)⁻¹ • ∑ i : Fin B,
      (gradSample M π (θ n ω) (ξ n ω i) - gradient (eta M π) (θ n ω)))

/-- R_n in Lemma 5, p. 12: the inverse-FIM fluctuation. -/
noncomputable def Rnoise (M : MDP S A) (π : E d → S → A → ℝ)
    {Ω : Type*} (ε : ℝ) (θ : ℕ → Ω → E d) (ξ ζ : ℕ → Ω → Fin B → S × A)
    (n : ℕ) (ω : Ω) : E d :=
  Matrix.toEuclideanLin
    (FhatInv π ε (θ n ω) (ζ n ω) - FbarInv (B := B) M π ε (θ n ω))
    (gradEst M π B K (fun m => θ m ω) (fun m => ξ m ω) n)

/-- δGₙ=Lₙ+Rₙ, the martingale fluctuation in the decomposition on p. 12. -/
noncomputable def deltaG (M : MDP S A) (π : E d → S → A → ℝ)
    {Ω : Type*} (ε : ℝ) (θ : ℕ → Ω → E d) (ξ ζ : ℕ → Ω → Fin B → S × A)
    (n : ℕ) (ω : Ω) : E d :=
  Lnoise (K := K) M π ε θ ξ n ω + Rnoise (K := K) M π ε θ ξ ζ n ω

/-- Outer product of two Euclidean vectors, for entrywise conditional expectations. -/
noncomputable def outer (u v : E d) : DMat d :=
  Matrix.vecMulVec (fun i => u i) (fun i => v i)

/-- The joint n,m→∞ Cesàro limit of an entrywise conditional matrix expectation.
The conditioning is on the state at n for every summand i, as in Lemmas 4–6. -/
def CesaroCondLimit {Ω : Type*} [m0 : MeasurableSpace Ω] (P : Measure Ω)
    (ℱ : Filtration ℕ m0) (X : ℕ → Ω → DMat d) (C : DMat d) : Prop :=
  ∀ᵐ ω ∂P, ∀ j k : Fin d,
    Tendsto (fun p : ℕ × ℕ =>
      (p.2 : ℝ)⁻¹ * ∑ i ∈ Finset.Ico p.1 (p.1 + p.2),
        P[fun ω' => (X i ω' - C) j k | ℱ p.1] ω)
      (atTop ×ˢ atTop) (𝓝 0)

end ReuseNPG.Rate


