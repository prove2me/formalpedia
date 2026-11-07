-- Prove2me | Definitions.Def_SelfSelReg_peelWeight
-- name    : SelfSelReg_peelWeight
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T22:47:00.466956+00:00
-- url     : https://prove2.me/theorems/be1e8a8f-fceb-4880-a8c6-ce5d39ad256a
-- title:
--   Peeling weights $\omega_R$, $\hat\omega_{\hat R}$ and the min-slice event
-- statement:
--   Let $R\subsetneq[k]$ be the indices of the recovered regressors and $Q=[k]\setminus R$. With $\Phi$ the standard Gaussian CDF, the conditional CDF of $Y_{\max,R}$ given $X=x$ is
--   $$F_R(t\mid x)=\prod_{i\in R}\Phi(t-\langle w_i,x\rangle)$$
--   (the empty product is $1$), and the **ideal signed peeling weight** is
--   $$\omega_R(X,Y_{\max})=\mathbf 1\{T\le Y_{\max}\le T+1\}-\big(F_R(T+1\mid X)-F_R(T\mid X)\big).$$
--   The **signed peeling weight** $\hat\omega_{\hat R}$ is the same expression with the true regressors $w_i$, $i\in R$, replaced by their estimates $\hat w$ in the recovered list $\hat R$ (matched bijectively to $R$). The file also defines the event $\{T\le\min\{Y_{\max,R},Y_{\max,Q}\}\le T+1\}$, which is empty when $R=\emptyset$ (with $Y_{\max,\emptyset}=-\infty$).
--
--   The peeling weight is an observable proxy for the slice indicator $\mathbf 1\{T\le Y_{\max,Q}\le T+1\}$ of the unrecovered maximum; Lemmas 8.3 and 8.4 bound the errors of this proxy.
--
--   **Formalization Note** The recovered list with its bijection to $R$ is a family $\hat w$ read on $R$: the estimate matched to $i\in R$ is $\hat w_i$. The min-slice event is written as $T\le Y_{\max,R}$, $T\le Y_{\max,Q}$, and ($Y_{\max,R}\le T+1$ or $Y_{\max,Q}\le T+1$).
-- source:
--   Zhou, Linear Regression with Self-Selection Bias in Polynomial Time, STOC 2027 submission (manuscript sha256 5d65f750…), §8.1.1, (103)–(106), p.56 (PDF p.59); Lemma 8.4, p.59 (PDF p.62)

import Mathlib
import Definitions.Def_SelfSelReg_jointLaw

open MeasureTheory ProbabilityTheory

namespace SelfSelReg

/-- `F_I(t | x) = ∏_{i∈I} Φ(t − ⟨v_i, x⟩)` (103), p.56, and its estimated version (105) when `v` is
the family of estimates; `Φ` is the standard Gaussian CDF. The empty product is `1`. -/
noncomputable def condCdf {n k : ℕ} (v : Fin k → EuclideanSpace ℝ (Fin n)) (I : Finset (Fin k))
    (t : ℝ) (x : EuclideanSpace ℝ (Fin n)) : ℝ :=
  ∏ i ∈ I, cdf (gaussianReal 0 1) (t - inner ℝ (v i) x)

/-- **The signed peeling weight** (104), (106).

F. Zhou, *Linear Regression with Self-Selection Bias in Polynomial Time*, STOC 2027 submission
(manuscript sha256 5d65f750…), §8.1.1, p.56 (PDF p.59): "ω_R(X, Y_max) := 1{T ≤ Y_max ≤ T + 1} −
(F_R(T + 1 | X) − F_R(T | X))" (104) and "ω̂_R̂(X, Y_max) := 1{T ≤ Y_max ≤ T + 1} − (F̂_R̂(T + 1 | X) −
F̂_R̂(T | X))" (106).

`peelWeight T v R x y` is `1{T ≤ y ≤ T + 1} − (F(T + 1 | x) − F(T | x))` with `F = condCdf v R`.
`ω_R = peelWeight T w R` (true regressors); `ω̂_R̂ = peelWeight T ŵ R` (estimates).

**Formalization Note.** The recovered list `R̂` with its bijection `match : R̂ → R` is encoded as a
family `ŵ : [k] → ℝⁿ` read on `R`: the estimate matched to `i ∈ R` is `ŵ_i`, so
`‖ŵ − w_match(ŵ)‖` is `‖ŵ_i − w_i‖`. -/
noncomputable def peelWeight {n k : ℕ} (T : ℝ) (v : Fin k → EuclideanSpace ℝ (Fin n))
    (R : Finset (Fin k)) (x : EuclideanSpace ℝ (Fin n)) (y : ℝ) : ℝ := by
  classical
  exact (if T ≤ y ∧ y ≤ T + 1 then 1 else 0) - (condCdf v R (T + 1) x - condCdf v R T x)

/-- The event `T ≤ min{Y_max,R, Y_max,Q} ≤ T + 1` (Lemma 8.4, p.59, PDF p.62), written as
`T ≤ Y_max,R`, `T ≤ Y_max,Q`, and (`Y_max,R ≤ T + 1` or `Y_max,Q ≤ T + 1`).

**Formalization Note.** With the convention `Y_max,∅ = −∞`, the event is empty when `R = ∅` or
`Q = ∅`; the existential form of `T ≤ Y_max,I` gives exactly that. -/
def inMinSlice {n k : ℕ} (T : ℝ) (w : Fin k → EuclideanSpace ℝ (Fin n)) (R Q : Finset (Fin k))
    (x : EuclideanSpace ℝ (Fin n)) (ξ : EuclideanSpace ℝ (Fin k)) : Prop :=
  (∃ i ∈ R, T ≤ response w x ξ i) ∧ (∃ j ∈ Q, T ≤ response w x ξ j) ∧
    ((∀ i ∈ R, response w x ξ i ≤ T + 1) ∨ (∀ j ∈ Q, response w x ξ j ≤ T + 1))

end SelfSelReg


