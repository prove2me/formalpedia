-- Prove2me | Definitions.Def_ReuseNPG_Rate_FixedState
-- name    : ReuseNPG_Rate_FixedState
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-21T00:30:53.193531+00:00
-- url     : https://prove2.me/theorems/954378c2-fab5-490f-b548-ea4daf8c3b0c
-- title:
--   §3–§4, pp. 7 and 12–13 — fixed-state memory chain, g, Γ, and Λ
-- statement:
--   The effective memory at time $n$ stores the previous $K-1$ gradient batches together with the occupancy density under which each pair was drawn. Holding the parameter fixed at $\theta$ defines a finite-state memory chain: a new batch is sampled from $d^{\pi_\theta}$, the oldest batch is dropped, and the new batch and its density are appended. Its transition operator gives the conditional expectation of a memory statistic after any number of fresh batches.
--
--   The file defines the conditional mean $g(\theta,e)$ of the preconditioned gradient estimate, the product $\Pi(n,i)=\prod_{j=n}^{i}(1-\alpha_j)$, and the series and cross moment of Lemma 8:
--
--   $$
--   \Gamma_n(\theta,e)
--   =\sum_{i=n}^{\infty}\Pi(n,i)\,
--   \mathbb E_\theta[g(\theta,e_i)-\bar F^{-1}(\theta)\nabla\eta(\theta)\mid e_n=e],
--   \qquad
--   \Lambda_n(\theta,e)=
--   \mathbb E_\theta[\Gamma_{n+1}(\theta,e_{n+1})
--   (\hat F^{-1}\hat\nabla\eta)^T\mid e_n=e].
--   $$
--
--   These definitions give Lemmas 7 and 8 their actual fixed-state conditional expectations, distinct from the conditional expectations of the evolving run in Lemmas 4–6.
--
--   **Formalization Note** The first $K-1$ run memories are padded with batch zero; the source limits concern $n\to\infty$. The series remains a true infinite sum. At $K=1$ the memory has no entries and the factors involving $K-1$ vanish.
-- source:
--   Lin, Wang & Zhou, Reusing historical trajectories in natural policy gradient via importance sampling, arXiv:2403.00675v2, p. 7, §3.1 effective memory; pp. 12–13, §4, Lemmas 7–8, equations (11)–(12)

import Mathlib
import Definitions.Def_ReuseNPG_Rate_Model

open MeasureTheory Filter ProbabilityTheory
open scoped Topology BigOperators

namespace ReuseNPG.Rate

variable {S A : Type*} [Fintype S] [Fintype A] [DecidableEq S] [DecidableEq A]
  {d B K : ℕ}

/-- The K−1 stored gradient batches and their drawing densities, §3.1, p. 7. -/
abbrev Mem (S A : Type*) (B K : ℕ) :=
  Fin (K - 1) → (Fin B → S × A) × (Fin B → ℝ)

/-- The memory of a run at iteration n. For n<K−1, natural subtraction pads
with batch zero; the fixed-state lemmas concern only n→∞. -/
noncomputable def memRun (M : MDP S A) (π : E d → S → A → ℝ)
    {Ω : Type*} (θ : ℕ → Ω → E d) (ξ : ℕ → Ω → Fin B → S × A)
    (n : ℕ) (ω : Ω) : Mem S A B K :=
  fun j =>
    let m := n + j.val - (K - 1)
    (ξ m ω, fun i => occ M π (θ m ω) (ξ m ω i))

/-- The fixed-state memory update: drop the oldest batch and append a new
batch with its current occupancy densities. -/
noncomputable def shift (M : MDP S A) (π : E d → S → A → ℝ)
    (θ : E d) (e : Mem S A B K) (x : Fin B → S × A) : Mem S A B K :=
  fun j => if h : j.val + 1 < K - 1 then e ⟨j.val + 1, h⟩
    else (x, fun i => occ M π θ (x i))

/-- The fixed-state Markov-chain conditional expectation of a memory statistic
after k fresh batches, with policy held at θ, §4, pp. 12–13. -/
noncomputable def fsExp (M : MDP S A) (π : E d → S → A → ℝ)
    (θ : E d) {X : Type*} [AddCommMonoid X] [Module ℝ X]
    (h : Mem S A B K → X) : ℕ → Mem S A B K → X
  | 0, e => h e
  | k+1, e => ∑ x : Fin B → S × A,
      (∏ i : Fin B, occ M π θ (x i)) • fsExp M π θ h k (shift M π θ e x)

/-- The full-K gradient estimator at a fixed θ, from the stored memory and one
fresh batch. It is used only in the fixed-state chain, after warm-up. -/
noncomputable def fixedGradEst (M : MDP S A) (π : E d → S → A → ℝ)
    (θ : E d) (e : Mem S A B K) (x : Fin B → S × A) : E d :=
  (((K : ℝ) * B)⁻¹) •
    ((∑ j : Fin (K - 1), ∑ i : Fin B,
      (occ M π θ ((e j).1 i) / (e j).2 i) • gradSample M π θ ((e j).1 i)) +
      ∑ i : Fin B, gradSample M π θ (x i))

/-- The conditional mean g(θ,e) of the preconditioned gradient estimator,
with the fresh gradient and FIM batches independent, p. 12. -/
noncomputable def fixedG (M : MDP S A) (π : E d → S → A → ℝ)
    (ε : ℝ) (θ : E d) (e : Mem S A B K) : E d :=
  Matrix.toEuclideanLin (FbarInv (B := B) M π ε θ)
    (∑ x : Fin B → S × A,
      (∏ i : Fin B, occ M π θ (x i)) • fixedGradEst (K := K) M π θ e x)

/-- Π(n,i)=∏_{j=n}^i(1−α_j), Lemma 8, p. 13. -/
def PiWeight (α : ℕ → ℝ) (n i : ℕ) : ℝ :=
  ∏ j ∈ Finset.Icc n i, (1 - α j)

/-- Γ_n(θ,e), the fixed-state Poisson-series correction, Lemma 8, p. 13. -/
noncomputable def Gamma (M : MDP S A) (π : E d → S → A → ℝ)
    (α : ℕ → ℝ) (ε : ℝ) (θ : E d) (n : ℕ) (e : Mem S A B K) : E d :=
  ∑' k : ℕ, PiWeight α n (n+k) •
    fsExp M π θ (fun e' => fixedG (B := B) M π ε θ e' -
      Matrix.toEuclideanLin (FbarInv (B := B) M π ε θ) (gradient (eta M π) θ))
      k e

/-- Λ_n(θ,e), the fixed-state conditional cross moment in Lemma 8, p. 13. -/
noncomputable def Lambda (M : MDP S A) (π : E d → S → A → ℝ)
    (α : ℕ → ℝ) (ε : ℝ) (θ : E d) (n : ℕ) (e : Mem S A B K) : DMat d :=
  ∑ x : Fin B → S × A, ∑ y : Fin B → S × A,
    ((∏ i : Fin B, occ M π θ (x i)) *
      (∏ i : Fin B, occ M π θ (y i))) •
      outer (Gamma (B := B) (K := K) M π α ε θ (n+1) (shift M π θ e x))
        (Matrix.toEuclideanLin (FhatInv π ε θ y)
          (fixedGradEst (K := K) M π θ e x))

/-- A simultaneous n,m→∞ Cesàro limit in the fixed-state chain, conditioning
on the run's memory at the starting time n. -/
def FsCesaroLimit (M : MDP S A) (π : E d → S → A → ℝ)
    (θbar : E d) {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (em : ℕ → Ω → Mem S A B K)
    (X : ℕ → Mem S A B K → DMat d) (C : DMat d) : Prop :=
  ∀ᵐ ω ∂P, ∀ j k : Fin d,
    Tendsto (fun p : ℕ × ℕ =>
      (p.2 : ℝ)⁻¹ * ∑ i ∈ Finset.Ico p.1 (p.1 + p.2),
        (fsExp M π θbar (fun e => X i e - C) (i - p.1) (em p.1 ω)) j k)
      (atTop ×ˢ atTop) (𝓝 0)

end ReuseNPG.Rate


