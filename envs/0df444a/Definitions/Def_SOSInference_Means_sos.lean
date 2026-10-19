-- Prove2me | Definitions.Def_SOSInference_Means_sos
-- name    : SOSInference_Means_sos
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-18T17:24:20.917886+00:00
-- url     : https://prove2.me/theorems/e35e8864-2500-4d21-911e-7d06fcdd700e
-- title:
--   Definition 1 / (21) — the SOS function $R_n^W(\theta)$ as a transport linear program
-- statement:
--   Let $x_1,\dots,x_n$ be points of $\mathbb R^l$ (the in-sample observations) and let $(z_j)_{j\in J}$ be a finite family of points of $\mathbb R^l$ (the merged sample $\mathcal Z_{n+m}$). For a target mean $\theta\in\mathbb R^l$, a **feasible coupling** is an array $\pi(i,j)\ge 0$ with
--   $$\sum_{j}\pi(i,j)=\frac1n\quad\text{for every } i,\qquad \sum_{j}\Big(\sum_{i}\pi(i,j)\Big)z_j=\theta .$$
--   The first condition says that the first marginal of $\pi$ is the empirical measure $\mu_n$ of the $x_i$; the second says that the second marginal, a probability measure supported on the $z_j$, has mean $\theta$. The **SOS function** is the least squared-Euclidean transport cost
--   $$R_n^W(\theta)=\inf\Big\{\sum_{i=1}^n\sum_{j}\pi(i,j)\,\|x_i-z_j\|_2^2 \;:\; \pi \text{ feasible}\Big\}.$$
--   The file also defines the sample mean $\bar X_n=\frac1n\sum_i x_i$.
--
--   This is the linear-programming form (21) of Definition 1 (12): the Wasserstein-type distance from the empirical measure to the set of probability measures supported on the merged sample whose mean is $\theta$.
--
--   **Formalization Note** The sets $\mathcal X_n$, $\mathcal Z_{n+m}$ are encoded as indexed families. The infimum is a real infimum: when the problem is infeasible ($\theta$ outside the convex hull of the $z_j$) the value is $0$ by convention, whereas the paper's value is $+\infty$. On feasible instances the cost set is nonempty and bounded below by $0$, so the value is the true infimum.
-- source:
--   Blanchet, Kang, Sample Out-of-Sample Inference Based on Wasserstein Distance, arXiv:1605.01340v4, p. 15, Definition 1 (12); p. 35, (21)

import Mathlib

/-!
# Sample out-of-sample inference: the SOS function for means (Definition 1, LP form (21))

Blanchet, Kang, Sample Out-of-Sample Inference Based on Wasserstein Distance, arXiv:1605.01340v4,
p. 15, Definition 1 (12); p. 35, (21).
-/

namespace SOSInference.Means

noncomputable section

open scoped RealInnerProductSpace

/-- The ambient space `ℝ^l` with the Euclidean norm `‖·‖₂`. -/
abbrev E (l : ℕ) := EuclideanSpace ℝ (Fin l)

/-- A feasible coupling of (21), p. 35, for target mean `θ`: a nonnegative array
`π(i, j)` (`i` ranging over the `n` sample points, `j` over the support family `z`) with
row sums `Σ_j π(i, j) = 1/n` for every `i` (that is, `π_X = μ_n`) and
`Σ_j (Σ_i π(i, j)) z_j = θ` (that is, `∫ z π_Z(dz) = θ`). -/
def IsFeasibleCoupling {l n : ℕ} {ι : Type*} [Fintype ι] (z : ι → E l) (θ : E l)
    (cpl : Fin n → ι → ℝ) : Prop :=
  (∀ i j, 0 ≤ cpl i j) ∧ (∀ i, ∑ j, cpl i j = 1 / (n : ℝ)) ∧
    (∑ i, ∑ j, cpl i j • z j) = θ

/-- The transport cost `Σ_i Σ_j π(i, j) ‖x_i − z_j‖₂²` of a coupling, the objective of (21). -/
def transportCost {l n : ℕ} {ι : Type*} [Fintype ι] (x : Fin n → E l) (z : ι → E l)
    (cpl : Fin n → ι → ℝ) : ℝ :=
  ∑ i, ∑ j, cpl i j * ‖x i - z j‖ ^ 2

/-- **Definition 1** (p. 15, (12)), in the linear-programming form (21) (p. 35): the SOS function
`R_n^W(θ)` of the sample points `x_1, …, x_n` with support family `z` (the merged sample
`Z_{n+m}`) is the infimum of the transport cost over feasible couplings.

**Formalization Note.** The sets `X_n`, `Z_{n+m}` of the paper are encoded as indexed families.
The infimum is a real `sInf`; when the LP is infeasible (`θ` not in the convex hull of the `z_j`)
the feasible set is empty and the value is `0` by convention (the paper's value is `+∞`).
On feasible instances the cost set is nonempty and bounded below by `0`, so the value is the true
infimum (and, by LP theory, a minimum). -/
def sos {l n : ℕ} {ι : Type*} [Fintype ι] (x : Fin n → E l) (z : ι → E l) (θ : E l) : ℝ :=
  sInf (transportCost x z '' {cpl | IsFeasibleCoupling z θ cpl})

/-- The sample mean `X̄_n = (1/n) Σ_i x_i`. -/
def xbar {l n : ℕ} (x : Fin n → E l) : E l :=
  (1 / (n : ℝ)) • ∑ i, x i

end

end SOSInference.Means


