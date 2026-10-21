-- Prove2me | Definitions.Def_ExtFSMFG_Existence_BSDE
-- name    : ExtFSMFG_Existence_BSDE
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-21T05:01:20.85066+00:00
-- url     : https://prove2.me/theorems/de199381-cb42-4c67-bd41-bb94761d1bea
-- title:
--   §3.1, (17), Lemma 3.1, (30), pp. 7–10 — BSDEs driven by the reference Markov chain, uniqueness in the sense of Lemma 3.1, the feedback control α̂
-- statement:
--   Backward stochastic differential equations driven by the canonical Markov chain $X$ under the reference measure $\mathbb P$.
--
--   1. **The martingale and its stochastic integral.** With states written as basis vectors, $\mathcal M_t=X_t-X_0-\int_0^tQ^0X_{s-}\,ds$ is the $\mathbb P$-martingale of (1). For an $\mathbb R^m$-valued process $Z$,
--   $$\int_t^TZ_s^*\,d\mathcal M_s=\sum_{t<s\le T,\ X_s\ne X_{s-}}Z_s^*(X_s-X_{s-})-\int_t^TZ_s^*Q^0X_{s-}\,ds .$$
--   2. **Solutions of (17).** For a terminal condition $\xi$ and a driver $F(\omega,t,y,z)$, a pair $(Y,Z)$ solves
--   $$Y_t=\xi+\int_t^TF(\omega,s,Y_s,Z_s)\,ds-\int_t^TZ_s^*\,d\mathcal M_s\qquad(17)$$
--   if $Y$ is real, adapted and càdlàg on $[0,T]$, $Z$ is $\mathbb R^m$-valued and predictable, $\mathbb E\int_0^T|Y_t|^2dt<\infty$, $\mathbb E\int_0^T\|Z_t\|^2_{X_{t-}}dt<\infty$, and $\mathbb P$-almost surely the identity holds for every $t\in[0,T]$. Here $\|z\|_{X_{t-}}=\|z\|_{e_i}$ when $X_{t-}=e_i$ (p. 5).
--   3. **Uniqueness** in the sense of Lemma 3.1: for any two solutions, $Y^1$ and $Y^2$ are indistinguishable and $\mathbb E\int_0^T\|Z^1_t-Z^2_t\|^2_{X_{t-}}dt=0$.
--   4. **The feedback control (30).** For a minimizer $\hat a$, a process $Z$ and a flow $p$, $\hat\alpha_t=\hat a(t,X_{t-},Z_t,p_t)$ for $t\in[0,T]$.
--
--   These objects state Lemma 3.8, Proposition 3.9 and the fixed-point map of §4.
--
--   **Formalization Note** The paper calls $Z$ "adapted and left-continuous"; the solutions of its reference [7] and the control (30) need $Z$ predictable, which is what is required here. The stochastic integral against $\mathcal M$ is pathwise, since $\mathcal M$ has finite variation. After $T$ the feedback control is set to $0$; only $t\in[0,T]$ matters.
-- source:
--   Carmona & Wang, A Probabilistic Approach to Extended Finite State Mean Field Games, arXiv:1808.07635v1, pp. 3–10, (1), (4), §3.1 (17), Lemma 3.1, (30)

import Mathlib
import Definitions.Def_ExtFSMFG_Existence_Model

open MeasureTheory Filter Topology
open scoped ENNReal NNReal

namespace ExtFSMFG.Existence

noncomputable section

variable {m : ℕ} {T : ℝ≥0}

/-- The pathwise stochastic integral `∫ₜᵀ Z*_s · d𝓜_s` against the martingale of (1),
`𝓜_t = X_t − X_0 − ∫₀ᵗ Q⁰ · X_{s−} ds` (states as basis vectors of `ℝᵐ`):
`Σ_{t<s≤T, X_s≠X_{s−}} Z*_s (X_s − X_{s−}) − ∫ₜᵀ Z*_s · Q⁰ · X_{s−} ds`. -/
def stochIntM (T : ℝ≥0) (Z : ℝ≥0 → Omega m T → (Fin m → ℝ)) (t : ℝ≥0) (ω : Omega m T) : ℝ :=
  (∑ᶠ (s : ℝ≥0) (_ : s ∈ jumpSet ω ∧ t < s), (Z s ω (Xc s ω) - Z s ω (Xm s ω))) -
    ∫ s in Set.Ioc (t : ℝ) T, ∑ j, Z s.toNNReal ω j * Q0 m j (Xm s.toNNReal ω)

/-- `(Y, Z)` solves the BSDE (17) (p. 7) with terminal condition `ξ` and driver `F(ω, t, y, z)`:
`Y` is adapted and càdlàg on `[0, T]`, `Z` is predictable, `E∫₀ᵀ |Y_t|² dt < ∞`,
`E∫₀ᵀ ‖Z_t‖²_{X_{t−}} dt < ∞`, and `P`-a.s., for every `t ∈ [0, T]`,
`Y_t = ξ + ∫ₜᵀ F(ω, s, Y_s, Z_s) ds − ∫ₜᵀ Z*_s · d𝓜_s`. -/
def SolvesBSDE (P : Measure (Omega m T)) (ξ : Omega m T → ℝ)
    (F : Omega m T → ℝ≥0 → ℝ → (Fin m → ℝ) → ℝ)
    (Y : ℝ≥0 → Omega m T → ℝ) (Z : ℝ≥0 → Omega m T → (Fin m → ℝ)) : Prop :=
  StronglyAdapted (filt m T) Y ∧
  (∀ ω, (∀ t < T, ContinuousWithinAt (fun s => Y s ω) (Set.Ici t) t) ∧
    ∀ t ≤ T, 0 < t → ∃ y, Tendsto (fun s => Y s ω) (𝓝[<] t) (𝓝 y)) ∧
  IsStronglyPredictable (filt m T) Z ∧
  (∫⁻ ω, (∫⁻ t in Set.Icc (0 : ℝ) T, ENNReal.ofReal (|Y t.toNNReal ω| ^ 2)) ∂P) < ∞ ∧
  (∫⁻ ω, (∫⁻ t in Set.Icc (0 : ℝ) T,
      ENNReal.ofReal (seminormE (Xm t.toNNReal ω) (Z t.toNNReal ω) ^ 2)) ∂P) < ∞ ∧
  ∀ᵐ ω ∂P, ∀ t ≤ T,
    Y t ω = ξ ω + (∫ s in Set.Ioc (t : ℝ) T, F ω s.toNNReal (Y s.toNNReal ω) (Z s.toNNReal ω)) -
      stochIntM T Z t ω

/-- Uniqueness of BSDE solutions in the sense of Lemma 3.1 (p. 8): any two solutions have
indistinguishable `Y` and `E∫₀ᵀ ‖Z¹_t − Z²_t‖²_{X_{t−}} dt = 0`. -/
def BSDEUnique (P : Measure (Omega m T)) (ξ : Omega m T → ℝ)
    (F : Omega m T → ℝ≥0 → ℝ → (Fin m → ℝ) → ℝ) : Prop :=
  ∀ Y₁ Z₁ Y₂ Z₂, SolvesBSDE P ξ F Y₁ Z₁ → SolvesBSDE P ξ F Y₂ Z₂ →
    (∀ᵐ ω ∂P, ∀ t ≤ T, Y₁ t ω = Y₂ t ω) ∧
    (∫⁻ ω, (∫⁻ t in Set.Icc (0 : ℝ) T,
      ENNReal.ofReal (seminormE (Xm t.toNNReal ω) (Z₁ t.toNNReal ω - Z₂ t.toNNReal ω) ^ 2)) ∂P) = 0

/-- The feedback control `α̂_t := â(t, X_{t−}, Z_t, p_t)` of (30) on `[0, T]` (set to `0` after `T`,
where it plays no role). -/
def ahatProc {l : ℕ}
    (ahat : ℝ≥0 → Fin m → (Fin m → ℝ) → (Fin m → ℝ) → EuclideanSpace ℝ (Fin l))
    (Z : ℝ≥0 → Omega m T → (Fin m → ℝ)) (p : ℝ≥0 → Fin m → ℝ) :
    ℝ≥0 → Omega m T → EuclideanSpace ℝ (Fin l) :=
  fun t ω => if t ≤ T then ahat t (Xm t ω) (Z t ω) (p t) else 0

end

end ExtFSMFG.Existence


