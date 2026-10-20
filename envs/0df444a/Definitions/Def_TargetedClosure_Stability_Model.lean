-- Prove2me | Definitions.Def_TargetedClosure_Stability_Model
-- name    : TargetedClosure_Stability_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-20T02:16:29.301952+00:00
-- url     : https://prove2.me/theorems/bca36efd-fa46-49d4-b70c-f9230bc1b487
-- title:
--   Spatial compartmental model and next generation matrices
-- statement:
--   A city has $n$ neighborhoods. Residents of neighborhood $i$ have population $N_i$ and spend a fraction $\tau_{ij}$ of their time in neighborhood $j$. Activity $x_j$ scales contact at destination $j$. The infected coordinates are ordered as exposed, clinical, and subclinical. The model defines the new-infection vector $\mathcal F$, the transfer vector $\mathcal V$, and their disease-free Jacobian matrices $F(x)$ and $V$. It also defines the effective reproduction rate
--
--   $$
--   \mathcal R_e=\lambda_1(F(x)V^{-1}),
--   $$
--
--   where $\lambda_1$ is the largest complex eigenvalue modulus. The auxiliary matrices are $T=(\tau_{ij})$, $\widehat N=\operatorname{diag}(N_i)$, $X=\operatorname{diag}(x_i)$, and $\Lambda=\operatorname{diag}((\sum_lN_l\tau_{lk})^{-1})$.
--
--   These definitions state the model used by Lemma 2.1 and its intermediate matrix identities.
--
--   **Formalization Note** The standing assumptions include positive populations and rates, nonnegative travel fractions with row sums at most one, $\rho,\alpha,x_i\in[0,1]$, and the necessary exclusion $\rho+\alpha(1-\rho)>0$. A zero mixing denominator is assigned zero, which is harmless because its mobility column vanishes.
-- source:
--   Birge, Candogan & Feng, Controlling Epidemic Spread: Reducing Economic Losses with Targeted Closures, BFI Working Paper No. 2020-57 (May 18, 2020, preliminary), pp. 7–13 (PDF 8–14), §2.1, §2.3, equations (1)–(8)

import Mathlib

open Matrix

namespace TargetedClosure.Stability

/-- Parameters of the spatial compartmental epidemic model. -/
structure Params (n : ℕ) where
  N : Fin n → ℝ
  tau : Matrix (Fin n) (Fin n) ℝ
  β : ℝ
  κ : ℝ
  ρ : ℝ
  α : ℝ
  γ : ℝ
  μ : ℝ

/-- The model's population, mobility, rate and clinical-fraction assumptions.
The final strict inequality excludes the undefined threshold at `ρ = α = 0`. -/
def Params.Standing {n : ℕ} (P : Params n) : Prop :=
  (∀ i, 0 < P.N i) ∧
  (∀ i j, 0 ≤ P.tau i j) ∧
  (∀ i, ∑ j, P.tau i j ≤ 1) ∧
  0 < P.β ∧ 0 < P.κ ∧ 0 < P.γ ∧ 0 < P.μ ∧
  0 ≤ P.ρ ∧ P.ρ ≤ 1 ∧ 0 ≤ P.α ∧ P.α ≤ 1 ∧
  0 < P.ρ + P.α * (1 - P.ρ)

/-- Permitted economic activity in every neighborhood. -/
def IsActivity {n : ℕ} (x : Fin n → ℝ) : Prop :=
  ∀ i, 0 ≤ x i ∧ x i ≤ 1

variable {n : ℕ}

/-- Effective population mixing at neighborhood `j`. -/
def mixMass (P : Params n) (j : Fin n) : ℝ :=
  ∑ k, P.N k * P.tau k j

/-- The infected coordinates are exposed, clinical, and subclinical, in that order. -/
abbrev Idx (n : ℕ) := Fin 3 × Fin n

/-- New infections, with the susceptible populations held at `S`. -/
noncomputable def calF (P : Params n) (x S : Fin n → ℝ) (y : Idx n → ℝ) : Idx n → ℝ :=
  fun p => if p.1 = 0 then
    P.β * S p.2 * ∑ j, P.tau p.2 j * x j *
      ((∑ k, (y (1, k) + P.α * y (2, k)) * P.tau k j) / mixMass P j)
    else 0

/-- Outflow and transitions among infected compartments. -/
def calV (P : Params n) (y : Idx n → ℝ) : Idx n → ℝ :=
  fun p => if p.1 = 0 then (P.μ + P.κ) * y (0, p.2)
    else if p.1 = 1 then -(P.ρ * P.κ * y (0, p.2)) + (P.μ + P.γ) * y (1, p.2)
    else -((1 - P.ρ) * P.κ * y (0, p.2)) + (P.μ + P.γ) * y (2, p.2)

/-- The Jacobian `F(x)` of `𝓕` at the disease-free equilibrium `S = N`. -/
noncomputable def Fmat (P : Params n) (x : Fin n → ℝ) : Matrix (Idx n) (Idx n) ℝ :=
  fun p q =>
    if p.1 = 0 ∧ q.1 = 1 then
      P.β * P.N p.2 * ∑ k, P.tau p.2 k * x k * (P.tau q.2 k / mixMass P k)
    else if p.1 = 0 ∧ q.1 = 2 then
      P.α * P.β * P.N p.2 * ∑ k, P.tau p.2 k * x k * (P.tau q.2 k / mixMass P k)
    else 0

/-- The Jacobian `V` of `𝓥`, in exposed, clinical, subclinical block order. -/
def Vmat (P : Params n) : Matrix (Idx n) (Idx n) ℝ :=
  fun p q =>
    if p.2 ≠ q.2 then 0
    else if p.1 = 0 ∧ q.1 = 0 then P.μ + P.κ
    else if p.1 = 1 ∧ q.1 = 0 then -(P.ρ * P.κ)
    else if p.1 = 2 ∧ q.1 = 0 then -((1 - P.ρ) * P.κ)
    else if p.1 = q.1 then P.μ + P.γ
    else 0

/-- The displayed closed form of `V⁻¹` in the proof of Lemma 2.1. -/
noncomputable def Vinv (P : Params n) : Matrix (Idx n) (Idx n) ℝ :=
  fun p q =>
    if p.2 ≠ q.2 then 0
    else if p.1 = 0 ∧ q.1 = 0 then 1 / (P.μ + P.κ)
    else if p.1 = 1 ∧ q.1 = 0 then
      P.ρ * P.κ / ((P.μ + P.κ) * (P.μ + P.γ))
    else if p.1 = 2 ∧ q.1 = 0 then
      (1 - P.ρ) * P.κ / ((P.μ + P.κ) * (P.μ + P.γ))
    else if p.1 = q.1 then 1 / (P.μ + P.γ)
    else 0

/-- Largest complex eigenvalue modulus of a real square matrix. -/
noncomputable def lam1 {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι ℝ) : ENNReal :=
  spectralRadius ℂ (A.map (algebraMap ℝ ℂ))

/-- The effective reproduction rate, condition (6). -/
noncomputable def Re (P : Params n) (x : Fin n → ℝ) : ENNReal :=
  lam1 (Fmat P x * (Vmat P)⁻¹)

/-- The mobility matrix `T`. -/
def Tmat (P : Params n) : Matrix (Fin n) (Fin n) ℝ := P.tau

/-- The population matrix `N̂`. -/
def Nhat (P : Params n) : Matrix (Fin n) (Fin n) ℝ := diagonal P.N

/-- The diagonal mixing normalization `Λ`. -/
noncomputable def Lam (P : Params n) : Matrix (Fin n) (Fin n) ℝ :=
  diagonal (fun k => 1 / mixMass P k)

/-- The diagonal activity matrix `X`. -/
def Xmat (x : Fin n → ℝ) : Matrix (Fin n) (Fin n) ℝ := diagonal x

/-- The reduced matrix `F̄(x)` of equation (8). -/
noncomputable def Fbar (P : Params n) (x : Fin n → ℝ) : Matrix (Fin n) (Fin n) ℝ :=
  fun i j => P.N i * ∑ k, P.tau i k * x k * (P.tau j k / mixMass P k)

/-- Positive diagonal square root of `N̂`. -/
noncomputable def Nsqrt (P : Params n) : Matrix (Fin n) (Fin n) ℝ :=
  diagonal (fun i => Real.sqrt (P.N i))

/-- Reciprocal of the diagonal square root of `N̂`. -/
noncomputable def Nsqrtinv (P : Params n) : Matrix (Fin n) (Fin n) ℝ :=
  diagonal (fun i => 1 / Real.sqrt (P.N i))

/-- The epidemic threshold in Lemma 2.1. -/
noncomputable def thr (P : Params n) : ℝ :=
  (P.μ + P.κ) * (P.μ + P.γ) /
    ((P.ρ + P.α * (1 - P.ρ)) * P.β * P.κ)

end TargetedClosure.Stability


