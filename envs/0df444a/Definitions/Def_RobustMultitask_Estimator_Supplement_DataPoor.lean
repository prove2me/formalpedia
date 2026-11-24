-- Prove2me | Definitions.Def_RobustMultitask_Estimator_Supplement_DataPoor
-- name    : RobustMultitask_Estimator_Supplement_DataPoor
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-24T06:55:59.75561+00:00
-- url     : https://prove2.me/theorems/540305cd-b0ae-49e7-810b-f9d862336a3c
-- title:
--   Definition 3, Remark 4, p. 18 — the compatibility set C(S, ψ) and the data-poor RMEstimator
-- statement:
--   Objects of the data-poor regime of §4.2. Vectors live in $\mathbb R^d$; for $S\subseteq[d]$, $v_S$ keeps the entries of $v$ indexed by $S$ and sets the others to $0$.
--
--   1. **Compatibility set (Definition 3).** For $S\subseteq[d]$ and $\psi>0$,
--   $$\mathcal C(S,\psi)=\bigl\{\Sigma\in\mathbb R^{d\times d}\ :\ |S|\,v^\top\Sigma v\ \ge\ \psi\,\|v_S\|_1^2\ \text{ for every } v \text{ with } \|v_{S^c}\|_1\le 7\|v_S\|_1\bigr\}.$$
--   Assumption 2 asks that the sample covariance $\widehat\Sigma^j$ of the data-poor task lie in $\mathcal C(\bar{\mathcal I}_j,\psi)$, where $\bar{\mathcal I}_j=\mathcal I_{\mathrm{well}}\cup\mathcal I_j$.
--   2. **Trimmed mean over a set of tasks.** For a finite set $D$ of tasks and values $v_i$, $\mathrm{TrimmedMean}(\{v_i\}_{i\in D},\omega)$ is the trimmed mean of the $|D|$ values $v_i$, $i\in D$.
--   3. **Data-poor RMEstimator (Remark 4).** Step 1 of Algorithm 1 omits the data-poor task $j$: componentwise, $\widehat\beta^\dagger_{RM,(c)}=\mathrm{TrimmedMean}(\{\widehat\beta^i_{\mathrm{ind},(c)}\}_{i\ne j},\omega)$, the trimmed mean of the OLS estimates of the other $N-1$ tasks. Step 2 is unchanged: $\widehat\beta^j_{RM}$ is any global minimizer of
--   $$\frac1{n_j}\|X^j\beta-Y^j\|_2^2+\lambda_j\|\beta-\widehat\beta^\dagger_{RM}\|_1 .$$
--
--   The data-poor task needs only the compatibility condition, a positive-definiteness requirement restricted to a cone around the sparse set $\bar{\mathcal I}_j$; its own Gram matrix is never inverted.
--
--   **Formalization Note** The OLS estimates and the trimmed mean are the published `ols` and `trimmedMean` of the base mission; the trimmed mean over $D$ lists the values of $D$ in increasing task order, which does not affect a trimmed mean. The estimator is a predicate on its output, so every minimizer is covered.
-- source:
--   Xu & Bastani, Multitask Learning and Bandits via Robust Statistics, arXiv:2112.14233v5, p. 18, Definition 3, Assumption 2 and Remark 4

import Mathlib
import Definitions.Def_RobustMultitask_Estimator_VectorNotation
import Definitions.Def_RobustMultitask_Estimator_TrimmedMean
import Definitions.Def_RobustMultitask_Estimator_Algorithm

namespace RobustMultitask.Estimator.Supplement

open Matrix

/-- **Definition 3** (p. 18): the set `C(S, ψ)` of matrices `Σ ∈ ℝ^{d×d}` with
`|S| vᵀΣv ≥ ψ ‖v_S‖₁²` for every `v ∈ ℝᵈ` with `‖v_{Sᶜ}‖₁ ≤ 7 ‖v_S‖₁` (the compatibility
condition with cone constant `7`). Here `v_S = restrict S v`. The source takes `ψ > 0`; that
is a hypothesis of every statement using this set. -/
def CompatSet {d : ℕ} (S : Finset (Fin d)) (ψ : ℝ) : Set (Matrix (Fin d) (Fin d) ℝ) :=
  {M | ∀ v : Fin d → ℝ, l1 (restrict Sᶜ v) ≤ 7 * l1 (restrict S v) →
      ψ * l1 (restrict S v) ^ 2 ≤ (S.card : ℝ) * (v ⬝ᵥ (M *ᵥ v))}

/-- The trimmed mean `TrimmedMean({v_i}_{i∈D}, ω)` of the values indexed by a finite set `D` of
tasks: the published `trimmedMean` of the `|D|` values `v_i`, `i ∈ D` (listed in increasing
index order; the order is irrelevant to a trimmed mean). -/
noncomputable def trimmedMeanOn {N : ℕ} (D : Finset (Fin N)) (v : Fin N → ℝ) (ω : ℝ) : ℝ :=
  trimmedMean (fun r : Fin D.card => v (D.orderEmbOfFin rfl r)) ω

/-- The shared estimate of the data-poor variant of Algorithm 1 (Remark 4, p. 18): Step 1 with
the data-poor task `j` omitted, i.e. componentwise
`β̂†_RM,(c) = TrimmedMean({β̂ⁱ_ind,(c)}_{i ≠ j}, ω)`, the trimmed mean of the `N − 1` OLS
estimates of the other tasks. -/
noncomputable def donorSharedEst {N d : ℕ} (n : Fin N → ℕ)
    (X : (i : Fin N) → Matrix (Fin (n i)) (Fin d) ℝ) (ω : ℝ)
    (Y : (i : Fin N) → Fin (n i) → ℝ) (j : Fin N) : Fin d → ℝ :=
  fun c => trimmedMeanOn (Finset.univ.erase j) (fun i => ols (X i) (Y i) c) ω

/-- `βhat` is an output `β̂ʲ_RM` of the data-poor variant of Algorithm 1 (Remark 4, p. 18) for
the data-poor task `j`: a global minimizer of `(1/n_j) ‖Xʲβ − Yʲ‖₂² + λ_j ‖β − β̂†_RM‖₁`, where
`β̂†_RM = donorSharedEst n X ω Y j` omits task `j`. Only OLS estimates of the other tasks are
formed; the Gram matrix of task `j` is never inverted. -/
def IsDataPoorRMEstimate {N d : ℕ} (n : Fin N → ℕ)
    (X : (i : Fin N) → Matrix (Fin (n i)) (Fin d) ℝ) (Y : (i : Fin N) → Fin (n i) → ℝ)
    (ω lam : ℝ) (j : Fin N) (βhat : Fin d → ℝ) : Prop :=
  IsLassoMinimizer (X j) (Y j) lam (donorSharedEst n X ω Y j) βhat

end RobustMultitask.Estimator.Supplement


