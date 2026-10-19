-- Prove2me | Definitions.Def_HTInsensBW_PhaseType_InnerProduct
-- name    : HTInsensBW_PhaseType_InnerProduct
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-18T20:14:31.49412+00:00
-- url     : https://prove2.me/theorems/ffe1a743-480f-4348-bb6e-99200c6f1c55
-- title:
--   §6, pp. 23–24, 26, 30, 33 — inner product M (65)–(67), vectors b^(ℓ) (64) and b̂^(ℓ), distance to the cone K (61), subspace projection, B1
-- statement:
--   The inner product and the geometric objects of the proofs in §6 of Wang, Maguluri, Srikant and Ying (pp. 23–24, 26, 30, 33), built on the model definitions.
--
--   1. **The matrix $M$ ((65)–(67), p. 24).** For route $r$ with law $(\pi_r,S_r)$, put $\mathbf P(\sigma)=\exp(S_r\sigma)\mathbf 1$ and
--   $$(M_r)_{k_1k_2}=\frac{\kappa_r}{\lambda^{(0)}_r}\int_0^{\infty}\frac{P_{k_1}(\sigma)P_{k_2}(\sigma)}{\pi_r(-S_r)^{-1}\exp(S_r\sigma)\mathbf 1}\,d\sigma ,$$
--   which is the entrywise form of (67). $M=\operatorname{diag}(M_1,\dots,M_R)$ and $S=\operatorname{diag}(S_1,\dots,S_R)$. The inner product is $\langle\mathbf y,\mathbf z\rangle=\mathbf y^TM\mathbf z$ and the norm $\|\mathbf y\|=\sqrt{\mathbf y^TM\mathbf y}$.
--   2. **Vectors ((62)–(64), p. 23; p. 26).** $\boldsymbol\rho^{(0)}$ concatenates the phase loads $\lambda^{(0)}_r(-S_r)^{-T}\pi_r^T$; for a state $\mathbf n$, $\mathbf n\mathbf x$ has entries $n_{r,k}x_r$; $b^{(\ell)}_{r,k}=\rho^{(0)}_{r,k}\mathbb 1_{\{\ell\in r\}}/\kappa_r$ and $\widehat b^{(\ell)}_{r,k}=n_{r,k}x_r\mathbb 1_{\{\ell\in r\}}/\kappa_r$.
--   3. **The cone and the distance to it ((61)).** $\mathcal K=\{\sum_{\ell\in\mathcal L_s}\alpha_\ell\mathbf b^{(\ell)}:\alpha\ge0\}$, and $\|\mathbf y_\perp\|$ is the distance from $\mathbf y$ to $\mathcal K$ in the norm above:
--   $$\|\mathbf y_\perp\|=\inf_{\alpha\ge0}\Big\|\mathbf y-\sum_{\ell\in\mathcal L_s}\alpha_\ell\mathbf b^{(\ell)}\Big\| .$$
--   4. **Projection onto the subspace (pp. 30, 33).** With $B_s$ the matrix whose rows are $(\mathbf b^{(\ell)})^T$, $\ell\in\mathcal L_s$, the $M$-orthogonal projection of $\mathbf y$ onto their span is $\mathbf y^s_\parallel=\sum_{\ell\in\mathcal L_s}\alpha^s_\ell\mathbf b^{(\ell)}$ with $\alpha^s=(B_sMB_s^T)^{-1}B_sM\mathbf y$.
--   5. **The term $B_1$ (p. 30).** In the $\epsilon$-th system, with $\lambda_r=(1-\epsilon)\lambda^{(0)}_r$,
--   $$B_1(\mathbf n)=\sum_r\Big(\sum_k\lambda_r\pi_{r,k}\|(\mathbf e^{(r,k)})^s_\parallel\|^2+\sum_{k_1\neq k_2}n_{r,k_1}x_r(S_r)_{k_1,k_2}\|-(\mathbf e^{(r,k_1)})^s_\parallel+(\mathbf e^{(r,k_2)})^s_\parallel\|^2+\sum_kn_{r,k}x_r\Big(-\sum_{k'}(S_r)_{k,k'}\Big)\|(\mathbf e^{(r,k)})^s_\parallel\|^2\Big).$$
--   6. $\mu_{\max}=\max_{r,b}\mu^{(b)}_r$ (p. 43).
--
--   These are the objects of the milestones; the goal theorem does not use them.
--
--   **Formalization Note** The matrix exponential is Mathlib's `NormedSpace.exp` on matrices; the integral is the Bochner integral over $(0,\infty)$, entrywise (whether it converges is the content of Lemma 11). $\|\cdot\|^2$ in $B_1$ is $\mathbf y^TM\mathbf y$ directly, with no square root. The inverse $(B_sMB_s^T)^{-1}$ is Mathlib's matrix inverse; it is the genuine inverse when $M$ is positive definite and $H$ has full row rank. The infimum defining $\|\mathbf y_\perp\|$ is over a nonempty set bounded below by $0$.
-- source:
--   Wang, Maguluri, Srikant, Ying, Heavy-traffic insensitive bounds for weighted proportionally fair bandwidth sharing policies, arXiv:1808.02120v2, pp. 23–24 ((61)–(67)), p. 26 (b̂^(ℓ)), p. 27 (S), p. 30 (B1), p. 33 (B_s), p. 43 (µmax)

import Mathlib
import Definitions.Def_HTInsensBW_PhaseType_Model

namespace HTInsensBW.PhaseType

open Matrix MeasureTheory

variable {L R : ℕ}

/-- `P(σ) = exp(S_r σ) 1` (p. 40): the vector whose `k`-th entry is the probability that a file
started in phase `k` is not finished after `σ` units of bandwidth. -/
noncomputable def Pvec (D : PhaseTypeD) (σ : ℝ) : Phase D → ℝ :=
  NormedSpace.exp (σ • subgen D) *ᵥ fun _ => 1

/-- The scalar denominator `π_r (-S_r)^{-1} exp(S_r σ) 1` of (67), p. 24. -/
noncomputable def denom (D : PhaseTypeD) (σ : ℝ) : ℝ :=
  D.init ⬝ᵥ ((-subgen D)⁻¹ *ᵥ Pvec D σ)

/-- The integrand of the `(k₁, k₂)` entry of `M_r` in (67) (the form used on p. 40). -/
noncomputable def Mintegrand (D : PhaseTypeD) (k₁ k₂ : Phase D) (σ : ℝ) : ℝ :=
  Pvec D σ k₁ * Pvec D σ k₂ / denom D σ

/-- The block `M_r` of (67), p. 24, entrywise:
`(M_r)_{k₁k₂} = κ_r/λ^(0)_r ∫_0^∞ P_{k₁}(σ) P_{k₂}(σ) / (π_r (-S_r)^{-1} exp(S_r σ) 1) dσ`. -/
noncomputable def Mr (N : BWNetwork L R) (r : Fin R) : Matrix (Phase (N.D r)) (Phase (N.D r)) ℝ :=
  Matrix.of fun k₁ k₂ => N.κ r / N.lam0 r * ∫ σ in Set.Ioi (0 : ℝ), Mintegrand (N.D r) k₁ k₂ σ

/-- The block-diagonal matrix `M = diag(M_1, …, M_R)` of (66), p. 24. -/
noncomputable def Mfull (N : BWNetwork L R) : Matrix (Idx N) (Idx N) ℝ :=
  Matrix.blockDiagonal' fun r => Mr N r

/-- The block-diagonal matrix `S = diag(S_1, …, S_R)` of p. 27. -/
noncomputable def Sfull (N : BWNetwork L R) : Matrix (Idx N) (Idx N) ℝ :=
  Matrix.blockDiagonal' fun r => subgen (N.D r)

/-- The inner product `⟨y, z⟩ = yᵀ M z` of (65), p. 24. -/
noncomputable def mInner (N : BWNetwork L R) (y z : Idx N → ℝ) : ℝ :=
  y ⬝ᵥ (Mfull N *ᵥ z)

/-- The squared induced norm `‖y‖² = yᵀ M y` (p. 24). -/
noncomputable def msq (N : BWNetwork L R) (y : Idx N → ℝ) : ℝ :=
  mInner N y y

/-- The induced norm `‖y‖ = √(yᵀ M y)` (p. 24). -/
noncomputable def mNorm (N : BWNetwork L R) (y : Idx N → ℝ) : ℝ :=
  Real.sqrt (msq N y)

/-- A state viewed as a real vector of `ℝ^K`. -/
def toReal (N : BWNetwork L R) (n : State N) : Idx N → ℝ :=
  fun i => (n i : ℝ)

/-- The concatenated phase-load vector `ρ^(0)` of (62)–(63), p. 23. -/
noncomputable def rho0 (N : BWNetwork L R) : Idx N → ℝ :=
  fun i => phaseLoad (N.D i.1) (N.lam0 i.1) i.2

/-- The bandwidth vector `nx`, with `(r, k)` entry `n_{r,k} x_r` (p. 26), `x` evaluated at the
route totals of `n`. -/
noncomputable def nx (N : BWNetwork L R) (x : (Fin R → ℕ) → Fin R → ℝ) (n : State N) :
    Idx N → ℝ :=
  fun i => (n i : ℝ) * x (routeCount N n) i.1

/-- The vector `b^(ℓ)` of (64), p. 23: `b^(ℓ)_{r,k} = ρ^(0)_{r,k} 1{ℓ ∈ r} / κ_r`. -/
noncomputable def bvec (N : BWNetwork L R) (ℓ : Fin L) : Idx N → ℝ :=
  fun i => rho0 N i * N.H ℓ i.1 / N.κ i.1

/-- The vector `b̂^(ℓ)` of p. 26: `b̂^(ℓ)_{r,k} = n_{r,k} x_r 1{ℓ ∈ r} / κ_r`. -/
noncomputable def bhat (N : BWNetwork L R) (x : (Fin R → ℕ) → Fin R → ℝ) (n : State N)
    (ℓ : Fin L) : Idx N → ℝ :=
  fun i => nx N x n i * N.H ℓ i.1 / N.κ i.1

/-- The distance `‖y_⊥‖` from `y` to the cone `K = {Σ_{ℓ ∈ L_s} α_ℓ b^(ℓ) : α_ℓ ≥ 0}` of (61),
p. 23, in the norm `‖·‖` of (65): the infimum of `‖y - Σ_{ℓ ∈ L_s} α_ℓ b^(ℓ)‖` over `α ≥ 0`.
(The set is nonempty, `α = 0`, and bounded below by `0`.) -/
noncomputable def perpNorm (N : BWNetwork L R) (y : Idx N → ℝ) : ℝ :=
  sInf ((fun α : critical N → ℝ => mNorm N (fun i => y i - ∑ ℓ, α ℓ * bvec N ℓ i)) ''
    {α | ∀ ℓ, 0 ≤ α ℓ})

/-- The matrix `B_s` whose rows are the `(b^(ℓ))ᵀ`, `ℓ ∈ L_s` (p. 33). -/
noncomputable def Bs (N : BWNetwork L R) : Matrix (critical N) (Idx N) ℝ :=
  Matrix.of fun ℓ i => bvec N ℓ i

/-- The coefficients `α^s` of the `M`-orthogonal projection of `y` onto the subspace `S` spanned by
`b^(ℓ)`, `ℓ ∈ L_s` (pp. 30–33): `α^s = (B_s M B_sᵀ)^{-1} B_s M y`. -/
noncomputable def alphaS (N : BWNetwork L R) (y : Idx N → ℝ) : critical N → ℝ :=
  (Bs N * Mfull N * (Bs N)ᵀ)⁻¹ *ᵥ (Bs N *ᵥ (Mfull N *ᵥ y))

/-- The projection `y^s_∥ = Σ_{ℓ ∈ L_s} α^s_ℓ b^(ℓ) = B_sᵀ (B_s M B_sᵀ)^{-1} B_s M y` of `y` onto
the subspace `S` (p. 33). -/
noncomputable def projS (N : BWNetwork L R) (y : Idx N → ℝ) : Idx N → ℝ :=
  (Bs N)ᵀ *ᵥ alphaS N y

/-- The unit vector `e^(r,k)`. -/
noncomputable def unitVec (N : BWNetwork L R) (i : Idx N) : Idx N → ℝ :=
  Pi.single i 1

/-- The term `B_1(n)` of the drift of `‖n^s_∥‖²` in the `ε`-th system (p. 30):
`B_1(n) = Σ_r ( Σ_k λ_r π_{r,k} ‖(e^(r,k))^s‖²
  + Σ_{k₁ ≠ k₂} n_{r,k₁} x_r (S_r)_{k₁,k₂} ‖-(e^(r,k₁))^s + (e^(r,k₂))^s‖²
  + Σ_k n_{r,k} x_r (-Σ_{k'} (S_r)_{k,k'}) ‖(e^(r,k))^s‖² )`, with `λ_r = (1 - ε) λ^(0)_r`. -/
noncomputable def B1 (N : BWNetwork L R) (x : (Fin R → ℕ) → Fin R → ℝ) (ε : ℝ) (n : State N) :
    ℝ :=
  ∑ r : Fin R,
    ((∑ k : Phase (N.D r),
        (1 - ε) * N.lam0 r * (N.D r).init k * msq N (projS N (unitVec N ⟨r, k⟩)))
    + (∑ k₁ : Phase (N.D r), ∑ k₂ : Phase (N.D r),
        if k₁ ≠ k₂ then
          (n ⟨r, k₁⟩ : ℝ) * x (routeCount N n) r * subgen (N.D r) k₁ k₂ *
            msq N (projS N (unitVec N ⟨r, k₂⟩) - projS N (unitVec N ⟨r, k₁⟩))
        else 0)
    + (∑ k : Phase (N.D r),
        (n ⟨r, k⟩ : ℝ) * x (routeCount N n) r * exitRate (N.D r) k *
          msq N (projS N (unitVec N ⟨r, k⟩))))

/-- `µ_max = max_{r,b} µ^(b)_r`, the largest block rate over all routes (p. 43). -/
noncomputable def muMax (N : BWNetwork L R) : ℝ :=
  ⨆ r, ⨆ b, (N.D r).rate b

end HTInsensBW.PhaseType


