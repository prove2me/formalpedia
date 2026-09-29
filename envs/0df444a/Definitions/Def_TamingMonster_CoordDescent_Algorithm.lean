-- Prove2me | Definitions.Def_TamingMonster_CoordDescent_Algorithm
-- name    : TamingMonster_CoordDescent_Algorithm
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-27T09:12:55.517911+00:00
-- url     : https://prove2.me/theorems/1dc0f584-6b81-4f92-a92f-8923b9f8e878
-- title:
--   Algorithm 2 (coordinate descent for (OP)): $V_\pi, S_\pi, D_\pi$, the rescaling of Eq. (4), the step $\alpha_\pi$, and runs
-- statement:
--   This file encodes Algorithm 2 of Agarwal et al. (2014), the coordinate descent algorithm that solves (OP) for a history $H_t$ and minimum probability $\mu$.
--
--   For weights $Q$ on $\Pi$ and $\pi\in\Pi$ (Step 3),
--   $$V_\pi(Q)=\widehat{\mathbb E}_{x\sim H_t}\Bigl[\frac1{Q^\mu(\pi(x)\mid x)}\Bigr],\quad S_\pi(Q)=\widehat{\mathbb E}_{x\sim H_t}\Bigl[\frac1{Q^\mu(\pi(x)\mid x)^2}\Bigr],\quad D_\pi(Q)=V_\pi(Q)-(2K+b_\pi).$$
--
--   1. **Rescaling** (Steps 4–6): if $\sum_\pi Q(\pi)(2K+b_\pi)>2K$, $Q$ is replaced by $cQ$ with
--   $$c=\frac{2K}{\sum_\pi Q(\pi)(2K+b_\pi)}\qquad(4);$$
--   otherwise $Q$ is unchanged. Call the result $\operatorname{rescale}(Q)$.
--   2. **Coordinate step** (Step 8): for a policy $\pi$, add
--   $$\alpha_\pi(Q)=\frac{V_\pi(Q)+D_\pi(Q)}{2(1-K\mu)S_\pi(Q)}$$
--   to $Q(\pi)$ and leave all other weights unchanged. One loop pass that reaches Step 8 with policy $\pi$ maps $Q$ to this step applied to $\operatorname{rescale}(Q)$.
--   3. **Runs.** A run with $n$ executions of Step 8 from $Q_{\mathrm{init}}$ is a sequence $Q^{(0)}=Q_{\mathrm{init}},Q^{(1)},\dots,Q^{(n)}$ such that, for each $k<n$, some policy $\pi_k$ has $D_{\pi_k}(\operatorname{rescale}(Q^{(k)}))>0$ (the test of Step 7 succeeds) and $Q^{(k+1)}$ is Step 8 for $\pi_k$ applied to $\operatorname{rescale}(Q^{(k)})$. The choice of $\pi_k$ among the policies passing the test is arbitrary, as in the paper's Step 7.
--   4. **Halting** (Step 10): the loop entered with $Q$ halts when $D_\pi(\operatorname{rescale}(Q))\le0$ for every $\pi\in\Pi$, and then outputs $\operatorname{rescale}(Q)$.
--
--   **Formalization Note** The algorithm is encoded relationally (runs as sequences satisfying the step relation), so statements about "the algorithm" quantify over every admissible choice of policy in Step 8. The count $n$ of a run is the number of Step-8 updates; the final pass that halts at Step 10 is not counted.
-- source:
--   Agarwal, Hsu, Kale, Langford, Li, Schapire, Taming the Monster: A Fast and Simple Algorithm for Contextual Bandits, arXiv:1402.0555v2, p. 6, Algorithm 2 and Eq. (4)

import Mathlib
import Definitions.Def_TamingMonster_CoordDescent_Setting

namespace TamingMonster.CoordDescent

variable {X : Type*} {K t : ℕ}

/-- Step 3 of Algorithm 2 (p. 6): `V_π(Q) = Ê_{x∼H_t}[1 / Q^μ(π(x) | x)]`. -/
noncomputable def Vfun (Pi : Finset (X → Fin K)) (H : History X K t) (μ : ℝ) (Q : Pi → ℝ)
    (π : Pi) : ℝ :=
  empExp H (fun x => 1 / smoothedProj Pi μ Q x ((π : X → Fin K) x))

/-- Step 3 of Algorithm 2: `S_π(Q) = Ê_{x∼H_t}[1 / (Q^μ(π(x) | x))²]`. -/
noncomputable def Sfun (Pi : Finset (X → Fin K)) (H : History X K t) (μ : ℝ) (Q : Pi → ℝ)
    (π : Pi) : ℝ :=
  empExp H (fun x => 1 / (smoothedProj Pi μ Q x ((π : X → Fin K) x)) ^ 2)

/-- Step 3 of Algorithm 2: `D_π(Q) = V_π(Q) − (2K + b_π)`. -/
noncomputable def Dfun (Pi : Finset (X → Fin K)) (H : History X K t) (μ : ℝ) (Q : Pi → ℝ)
    (π : Pi) : ℝ :=
  Vfun Pi H μ Q π - (2 * (K : ℝ) + bCoef Pi H μ (π : X → Fin K))

/-- The quantity `∑_π Q(π)(2K + b_π)` tested in Step 4 of Algorithm 2. -/
noncomputable def weightedMass (Pi : Finset (X → Fin K)) (H : History X K t) (μ : ℝ)
    (Q : Pi → ℝ) : ℝ :=
  ∑ π, Q π * (2 * (K : ℝ) + bCoef Pi H μ (π : X → Fin K))

/-- Eq. (4): `c = 2K / ∑_π Q(π)(2K + b_π)`. -/
noncomputable def scaleFactor (Pi : Finset (X → Fin K)) (H : History X K t) (μ : ℝ)
    (Q : Pi → ℝ) : ℝ :=
  2 * (K : ℝ) / weightedMass Pi H μ Q

/-- Steps 4–6 of Algorithm 2: if `∑_π Q(π)(2K + b_π) > 2K`, replace `Q` by `cQ` with `c` as in
Eq. (4); otherwise leave `Q` unchanged. -/
noncomputable def rescale (Pi : Finset (X → Fin K)) (H : History X K t) (μ : ℝ)
    (Q : Pi → ℝ) : Pi → ℝ :=
  if 2 * (K : ℝ) < weightedMass Pi H μ Q then
    fun π => scaleFactor Pi H μ Q * Q π
  else Q

/-- Step 8 of Algorithm 2: `α_π(Q) = (V_π(Q) + D_π(Q)) / (2(1 − Kμ) S_π(Q))`. -/
noncomputable def alphaStep (Pi : Finset (X → Fin K)) (H : History X K t) (μ : ℝ)
    (Q : Pi → ℝ) (π : Pi) : ℝ :=
  (Vfun Pi H μ Q π + Dfun Pi H μ Q π) / (2 * (1 - (K : ℝ) * μ) * Sfun Pi H μ Q π)

open Classical in
/-- Step 8 of Algorithm 2 applied to `Q`: add `α_π(Q)` to `Q(π)` and leave all other weights
unchanged. -/
noncomputable def addAlpha (Pi : Finset (X → Fin K)) (H : History X K t) (μ : ℝ)
    (Q : Pi → ℝ) (π : Pi) : Pi → ℝ :=
  Function.update Q π (Q π + alphaStep Pi H μ Q π)

/-- One pass through the loop of Algorithm 2 that ends in Step 8 with policy `π`: rescale `Q`
(Steps 4–6), then add `α_π` to the coordinate `π` of the rescaled weights (Step 8). -/
noncomputable def cdStep (Pi : Finset (X → Fin K)) (H : History X K t) (μ : ℝ)
    (Q : Pi → ℝ) (π : Pi) : Pi → ℝ :=
  addAlpha Pi H μ (rescale Pi H μ Q) π

/-- A run of Algorithm 2 with `n` executions of Step 8, started from `Q_init` (Step 1):
`Qs 0 = Q_init`, and for every `k < n` some policy `π` has `D_π(rescale (Qs k)) > 0` (the test of
Step 7 succeeds, with `π` any policy passing it) and `Qs (k+1)` is the result of Step 8 for that
`π`. -/
def IsRun (Pi : Finset (X → Fin K)) (H : History X K t) (μ : ℝ) (Qinit : Pi → ℝ) (n : ℕ)
    (Qs : ℕ → Pi → ℝ) : Prop :=
  Qs 0 = Qinit ∧
  ∀ k < n, ∃ π : Pi, 0 < Dfun Pi H μ (rescale Pi H μ (Qs k)) π ∧
    Qs (k + 1) = cdStep Pi H μ (Qs k) π

/-- The loop, entered with weights `Q`, halts at Step 10: after Steps 4–6 no policy has
`D_π > 0`. Its output is then `rescale Q`. -/
def HaltsAt (Pi : Finset (X → Fin K)) (H : History X K t) (μ : ℝ) (Q : Pi → ℝ) : Prop :=
  ∀ π : Pi, Dfun Pi H μ (rescale Pi H μ Q) π ≤ 0

end TamingMonster.CoordDescent


