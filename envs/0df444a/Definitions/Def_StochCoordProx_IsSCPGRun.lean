-- Prove2me | Definitions.Def_StochCoordProx_IsSCPGRun
-- name    : StochCoordProx_IsSCPGRun
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T11:34:08.838004+00:00
-- url     : https://prove2.me/theorems/194bfdcf-a882-435f-a35d-40b6d934e5e0
-- title:
--   A run of SCPG (Algorithm 1)
-- statement:
--   Let $f,\psi:\mathbb R^n\to\mathbb R$, $\mathcal U\subset\mathbb R^{n\times p}$, let $L:\mathbb R^{n\times p}\to\mathbb R$ assign to each matrix its constant $L_U$, and let $x_0\in\mathbb R^n$. On a sample space $\Omega$, sequences $U_k(\omega)\in\mathbb R^{n\times p}$, $\eta_k(\omega)\in\mathbb R$, $x_k(\omega)\in\mathbb R^n$ and $d_k(\omega)\in\mathbb R^p$ form a **run of SCPG from $x_0$** if, for every outcome $\omega$, $x_0(\omega)=x_0$ and for every $k\ge0$:
--
--   1. $U_k(\omega)\in\mathcal U$ and $\eta_k(\omega)>0$;
--   2. $d_k(\omega)$ is a global minimizer over $\mathbb R^p$ of the subproblem (9) at $x_k(\omega)$, with matrix $U_k(\omega)$ and $H=H_{f,U_k(\omega)}$ computed from $L_{U_k(\omega)}$ and $\eta_k(\omega)$;
--   3. $x_{k+1}(\omega)=x_k(\omega)+U_k(\omega)\,d_k(\omega)$.
--
--   This is the object about which Lemmas 4 to 6 and Theorem 1 speak.
--
--   **Formalization Note** The run is pathwise. The parameter $\eta_k(\omega)$ may be any positive choice at step $k$; the paper's $\eta_{U_k}$, a function of $U_k$, is a special case. No sampling distribution is fixed: the paper uses the randomness of $U_k$ only through Assumption 2, which is a separate hypothesis.
-- source:
--   Necoara & Chorobura, Efficiency of stochastic coordinate proximal gradient methods on nonseparable composite optimization, arXiv:2104.13370v3, Algorithm 1 (SCPG), p.6

import Mathlib
import Definitions.Def_StochCoordProx_Hf
import Definitions.Def_StochCoordProx_model

namespace StochCoordProx

/-- **A run of SCPG** (Algorithm 1) from `x₀`, on every outcome `ω` of a sample space `Ω`:
for every `ω` we have `x₀(ω) = x₀`, and for every `k ≥ 0`
1. the sampled matrix lies in the family: `U_k(ω) ∈ 𝒰`, and the chosen parameter is positive:
   `η_k(ω) > 0`;
2. `d_k(ω)` is a global minimizer over `ℝᵖ` of the subproblem (9) at `x_k(ω)`, with matrix
   `U_k(ω)` and `H = H_{f,U_k(ω)}` computed from `L_{U_k(ω)}` and `η_k(ω)` (step 1);
3. `x_{k+1}(ω) = x_k(ω) + U_k(ω) d_k(ω)`.

Necoara & Chorobura, arXiv:2104.13370v3, Algorithm 1 (SCPG), p.6.

**Formalization Note.** The run is pathwise: `U k ω`, `η k ω`, `x k ω`, `d k ω` are the
iterates on outcome `ω`. `L : ℝ^{n×p} → ℝ` assigns to each matrix its constant `L_U`. The paper
writes `η_{U_k}`; here `η_k(ω)` is any positive choice at step `k`, of which a choice depending
only on `U_k` is a special case. No sampling distribution is fixed: the paper uses the
randomness of `U_k` only through Assumption 2, which is a separate hypothesis. -/
def IsSCPGRun {n p : ℕ} {Ω : Type*} (f ψ : EuclideanSpace ℝ (Fin n) → ℝ)
    (𝒰 : Set (Matrix (Fin n) (Fin p) ℝ)) (L : Matrix (Fin n) (Fin p) ℝ → ℝ)
    (x₀ : EuclideanSpace ℝ (Fin n)) (U : ℕ → Ω → Matrix (Fin n) (Fin p) ℝ) (η : ℕ → Ω → ℝ)
    (x : ℕ → Ω → EuclideanSpace ℝ (Fin n)) (d : ℕ → Ω → EuclideanSpace ℝ (Fin p)) : Prop :=
  ∀ ω : Ω, x 0 ω = x₀ ∧
    ∀ k : ℕ, U k ω ∈ 𝒰 ∧ 0 < η k ω ∧
      (∀ d' : EuclideanSpace ℝ (Fin p),
        model f ψ (x k ω) (U k ω) (Hf ψ 𝒰 (L (U k ω)) (η k ω)) (d k ω) ≤
          model f ψ (x k ω) (U k ω) (Hf ψ 𝒰 (L (U k ω)) (η k ω)) d') ∧
      x (k + 1) ω = x k ω + Matrix.toEuclideanLin (U k ω) (d k ω)

end StochCoordProx


