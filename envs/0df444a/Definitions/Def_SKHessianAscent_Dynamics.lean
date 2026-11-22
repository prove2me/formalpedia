-- Prove2me | Definitions.Def_SKHessianAscent_Dynamics
-- name    : SKHessianAscent_Dynamics
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-22T19:57:48.183438+00:00
-- url     : https://prove2.me/theorems/0781cebb-263e-4e25-acaa-26f202eb455d
-- title:
--   The diffusions ASL-TAP (3.4) and PHD (3.5), their dual-coordinate equations, the Jarzynski weight (JE), stopped at the exit from $\mathcal S_{\beta,A}(c)$; safe pair sets
-- statement:
--   Fix $\beta$, $c$ and one real $n\times n$ matrix $A$. $W$ is a standard Brownian motion in $\mathbb R^n$ on a probability space $(\Omega,P)$, with its completed natural filtration $(\mathcal F_t)$.
--
--   **Stopped Itô processes.** `exitTime S γ` is $\inf\{t\ge0:\gamma_t\notin S\}\in[0,\infty]$. `IsItoStopped P ℱ W τ a H X` says that $X$ is a continuous $\mathcal F$-adapted process with
--   $$X_t=\int_0^t\mathbf 1\{s<\tau\}\,a_s\,ds+\int_0^t\mathbf 1\{s<\tau\}\,H_s\,dW_s\qquad(t\ge0),$$
--   almost surely for all $t$ simultaneously, where the second term is the Itô integral. `SolvesUntilExit P W S b Σ X` is the case $a_s=b(X_s)$, $H_s=\Sigma(X_s)$ and $\tau=\inf\{t:X_t\notin S\}$: $X$ solves $dX_t=b(X_t)\,dt+\Sigma(X_t)\,dW_t$, $X_0=0$, up to its first exit from $S$ and is stopped there. `SolvesUntilExitT` is the same with time-dependent coefficients $b_t$, $\Sigma_t$, and `stopAt τ X` is $X_{t\wedge\tau}$.
--
--   **The algorithmic processes (§3.3).** With $\widehat Q(m)$, $f(m)$ and $\omega(m)$ as in the model definitions:
--
--   - `IsASLTAP P W β A c X`: $X=\widehat m$ solves (3.4), $d\widehat m_t=\widehat Q(\widehat m_t)(\widehat m_t-f(\widehat m_t))\,dt+\widehat Q(\widehat m_t)\,dW_t$, $\widehat m_0=0$, up to its exit time $\tau_c$ from $\mathcal S_{\beta,A}(c)$;
--   - `IsPHD P W β A c X`: $X=\widehat m$ solves (3.5), $d\widehat m_t=\widehat Q(\widehat m_t)\,dW_t$, $\widehat m_0=0$, up to $\tau_c$;
--   - dual coordinates $x=\tanh^{-1}(m)$: `dualSafe β A c` is $\tanh^{-1}(\mathcal S_{\beta,A}(c))$, `dualSigma` is $\widehat\Sigma(x)=D(m)\widehat Q(m)$, `dualPhdDrift` is $\widehat f^*(x)=\mathbf E_{\mathcal D_n}[\widehat Q(m)^2]D(m)^2m$ and `dualAslDrift` is $D(m)\widehat Q(m)(m-f(m))+\widehat f^*(x)$, with $m=\tanh(x)$; these are the coefficients of (d-PHD) and (d-ASL-TAP);
--   - `jeWeight β A τ X t` is the Jarzynski weight $\widehat w_t=\int_0^t\mathbf 1\{s<\tau\}\,\omega(\widehat m_s)\,ds$.
--
--   **Safe pair sets (§3.1).** For a distance $d$, an ambient set $U$ (the paper's $\Omega$) and a safe set $S\subseteq U$: `expandedSafe d U S r` is $S(r)=\{x\in U:B(x,r)\cap U\subseteq S\}$ and `safePair d U S r₁ r₂` is $S^2(r_1,r_2)=\{(x_1,x_2)\in U^2:x_1\in S(r_1),\ d(x_1,x_2)<r_2\}$. `distVec` is the Euclidean distance on $\mathbb R^n$ and `distPair` the Euclidean distance on $\mathbb R^n\times\mathbb R^n$.
--
--   **Formalization Note** The Itô integral, the Brownian motion and the filtration are the published `EthierKurtz.HasBrownianItoIntegral`, `EthierKurtz.IsStandardBrownian` and `EthierKurtz.completedBrownianPast`. As in the published `EthierKurtz.SolvesBrownianSDE`, the component integrals are continuous adapted versions. A stopped solution is constant from its exit time on, which is the paper's "stopped solution, defined for all $t\ge0$". The initial value is $0$, as in (3.4)–(3.5).
-- source:
--   H. Lee, J. S. Sandhu, J. Shi, Potential Hessian Ascent IV: Sampling the Sherrington–Kirkpatrick model at β < 1, https://arxiv.org/abs/2609.30590, §3 p. 7 ((ASL-TAP), (PHD-TAP), (JE)); §3.1 p. 8 ((3.3), $S(r)$, $S^2(r_1,r_2)$); §3.3 p. 14 ((3.4), (3.5), (d-PHD), (d-ASL-TAP)); proof of Lemma 3.9, p. 15

import Mathlib
import Definitions.Def_EthierKurtz_SDEState
import Definitions.Def_EthierKurtz_completedBrownianPast
import Definitions.Def_EthierKurtz_HasBrownianItoIntegral
import Definitions.Def_EthierKurtz_IsStandardBrownian
import Definitions.Def_SKHessianAscent_Model

open MeasureTheory EthierKurtz
open scoped ENNReal NNReal BigOperators

namespace SKHessianAscent

/-!
# The algorithmic diffusions ASL-TAP and PHD, stopped at the exit from the safe set

H. Lee, J. S. Sandhu, J. Shi, *Potential Hessian Ascent IV: Sampling the Sherrington–Kirkpatrick
model at β < 1*, §3 (p. 7) and §3.3 (p. 14):

* (3.4), ASL-TAP: `dm̂_t = Q̂(m̂_t)(m̂_t − f(m̂_t)) dt + Q̂(m̂_t) dB_t`, `m̂_0 = 0`;
* (3.5), PHD: `dm̂_t = Q̂(m̂_t) dB_t`, `m̂_0 = 0`;
* (JE): `dw_t = ω(m̂_t) dt`, `ω(m) = ½[Tr Q̂(m) + ‖m‖²]`;
* dual coordinates `x̂_t = tanh⁻¹(m̂_t)`, `Σ̂(x) = D(m) Q̂(m)`, `f̂*(x) = E_{D_n}[Q̂(m)²] D(m)² m`,
  `m = tanh(x)`, and the dual equations (d-PHD) `dx̂_t = f̂*(x̂_t) dt + Σ̂(x̂_t) dB_t` and
  (d-ASL-TAP) `dx̂_t = [D(m̂_t)Q̂(m̂_t)(m̂_t − f(m̂_t)) + f̂*(x̂_t)] dt + Σ̂(x̂_t) dB_t`.

"Each equation is used up to its first exit from `S_{β,A}(c)`, with its own exit time denoted
`τ_c`" (p. 14), and the stopped solution is (proof of Lemma 3.9, p. 15)
`x̂_{t∧τ_c} = ∫₀ᵗ 1{s<τ_c} b(x̂_s) ds + ∫₀ᵗ 1{s<τ_c} Σ̂(x̂_s) dB_s`.

**Formalization Note.** The matrix `A` is fixed (the equations are those of one disorder sample).
The Itô integral is the published `EthierKurtz.HasBrownianItoIntegral` (limit in probability of
left-point sums of bounded adapted step integrands), the Brownian motion is the published
`EthierKurtz.IsStandardBrownian`, and the filtration is the published
`EthierKurtz.completedBrownianPast` (the completed natural filtration of `W`, with the constant
initial value `0`). A stopped solution is a continuous adapted process `X` that satisfies the
displayed stopped integral equation with `τ` the first exit time of `X` itself from the domain;
it is therefore constant from `τ` on. As in the published `EthierKurtz.SolvesBrownianSDE`, the
component integrals are continuous adapted versions and the equation holds outside one null set
for all times.
-/

noncomputable section

/-- The first exit time `inf{t ≥ 0 : γ_t ∉ S}` of a path from a set, with value `∞` when the path
never leaves. -/
def exitTime {E : Type*} (S : Set E) (γ : ℝ≥0 → E) : ℝ≥0∞ :=
  ⨅ t ∈ {t : ℝ≥0 | γ t ∉ S}, (t : ℝ≥0∞)

/-- `X_t = ∫₀ᵗ 1{s<τ} a_s ds + ∫₀ᵗ 1{s<τ} H_s dW_s` for all `t ≥ 0`: the Itô process with drift `a`
and diffusion matrix `H`, started at `0` and stopped at `τ`, for the filtration `ℱ`. -/
def IsItoStopped {Ω : Type*} [MeasurableSpace Ω] {n : ℕ} (P : Measure Ω)
    (ℱ : ℝ≥0 → MeasurableSpace Ω) (W : ℝ≥0 → Ω → SDEState n) (τ : Ω → ℝ≥0∞)
    (a : ℝ≥0 → Ω → Fin n → ℝ) (H : ℝ≥0 → Ω → Matrix (Fin n) (Fin n) ℝ)
    (X : ℝ≥0 → Ω → Fin n → ℝ) : Prop :=
  (∀ ω, Continuous fun t => X t ω) ∧
  (∀ t, Measurable[ℱ t] (X t)) ∧
  ∃ J : ℝ≥0 → Ω → Matrix (Fin n) (Fin n) ℝ,
    (∀ ω i j, Continuous fun t => J t ω i j) ∧
    (∀ t i j, Measurable[ℱ t] fun ω => J t ω i j) ∧
    (∀ i j, HasBrownianItoIntegral P ℱ (fun t ω => W t ω j)
      (fun t ω => if (t : ℝ≥0∞) < τ ω then H t ω i j else 0) (fun t ω => J t ω i j)) ∧
    (∀ (t : ℝ≥0) ω i, IntervalIntegrable
      (fun u : ℝ => if (u.toNNReal : ℝ≥0∞) < τ ω then a u.toNNReal ω i else 0) volume 0 t) ∧
    ∀ᵐ ω ∂P, ∀ (t : ℝ≥0) i, X t ω i = (∑ j, J t ω i j) +
      ∫ u in (0 : ℝ)..t, if (u.toNNReal : ℝ≥0∞) < τ ω then a u.toNNReal ω i else 0

/-- `X` solves `dX_t = b(X_t) dt + Σ(X_t) dW_t`, `X_0 = 0`, up to its first exit from `S`, and is
stopped there. With `S = Set.univ` this is a global strong solution. -/
def SolvesUntilExit {Ω : Type*} [MeasurableSpace Ω] {n : ℕ} (P : Measure Ω)
    (W : ℝ≥0 → Ω → SDEState n) (S : Set (Fin n → ℝ)) (b : (Fin n → ℝ) → Fin n → ℝ)
    (Sig : (Fin n → ℝ) → Matrix (Fin n) (Fin n) ℝ) (X : ℝ≥0 → Ω → Fin n → ℝ) : Prop :=
  IsItoStopped P (completedBrownianPast P W fun _ => 0) W
    (fun ω => exitTime S fun t => X t ω)
    (fun t ω => b (X t ω)) (fun t ω => Sig (X t ω)) X

/-- `X` solves the time-inhomogeneous equation `dX_t = b_t(X_t) dt + Σ_t(X_t) dW_t`, `X_0 = 0`, up
to its first exit from `S`, and is stopped there ((3.3), p. 8, for diffusion processes). -/
def SolvesUntilExitT {Ω : Type*} [MeasurableSpace Ω] {n : ℕ} (P : Measure Ω)
    (W : ℝ≥0 → Ω → SDEState n) (S : Set (Fin n → ℝ)) (b : ℝ≥0 → (Fin n → ℝ) → Fin n → ℝ)
    (Sig : ℝ≥0 → (Fin n → ℝ) → Matrix (Fin n) (Fin n) ℝ) (X : ℝ≥0 → Ω → Fin n → ℝ) : Prop :=
  IsItoStopped P (completedBrownianPast P W fun _ => 0) W
    (fun ω => exitTime S fun t => X t ω)
    (fun t ω => b t (X t ω)) (fun t ω => Sig t (X t ω)) X

/-- The process stopped at `τ`: `X_{t∧τ}`. -/
def stopAt {Ω E : Type*} (τ : Ω → ℝ≥0∞) (X : ℝ≥0 → Ω → E) : ℝ≥0 → Ω → E :=
  fun t ω => X (min (t : ℝ≥0∞) (τ ω)).toNNReal ω

/-- The expanded safe set `S(r) = {x ∈ Ω : B(x, r) ∩ Ω ⊆ S}` (p. 8), for an ambient set `U`
(the paper's `Ω`), a safe set `S` and a distance `d`; `B(x, r)` is the open ball. -/
def expandedSafe {E : Type*} (d : E → E → ℝ) (U S : Set E) (r : ℝ) : Set E :=
  {x | x ∈ U ∧ ∀ u ∈ U, d u x < r → u ∈ S}

/-- The safe pair set `S²(r₁, r₂) = {(x₁, x₂) ∈ Ω² : x₁ ∈ S(r₁), ‖x₁ − x₂‖ < r₂}` (p. 8). -/
def safePair {E : Type*} (d : E → E → ℝ) (U S : Set E) (r₁ r₂ : ℝ) : Set (E × E) :=
  {p | p.1 ∈ expandedSafe d U S r₁ ∧ p.2 ∈ U ∧ d p.1 p.2 < r₂}

/-- The Euclidean distance on `ℝⁿ`. -/
def distVec {n : ℕ} (u x : Fin n → ℝ) : ℝ := l2 (u - x)

/-- The Euclidean distance on `ℝⁿ × ℝⁿ`. -/
def distPair {n : ℕ} (p q : (Fin n → ℝ) × (Fin n → ℝ)) : ℝ :=
  Real.sqrt (l2 (p.1 - q.1) ^ 2 + l2 (p.2 - q.2) ^ 2)

/-- The ASL-TAP drift `Q̂(m)(m − f(m))` of (3.4). -/
def aslDrift {n : ℕ} (β : ℝ) (A : Matrix (Fin n) (Fin n) ℝ) (m : Fin n → ℝ) : Fin n → ℝ :=
  (Qhat β A m).mulVec (m - fDrift β A m)

/-- `m̂` is the ASL-TAP process (3.4) for the Brownian motion `W`, stopped at its first exit `τ_c`
from `S_{β,A}(c)`. -/
def IsASLTAP {Ω : Type*} [MeasurableSpace Ω] {n : ℕ} (P : Measure Ω) (W : ℝ≥0 → Ω → SDEState n)
    (β : ℝ) (A : Matrix (Fin n) (Fin n) ℝ) (c : ℝ) (X : ℝ≥0 → Ω → Fin n → ℝ) : Prop :=
  SolvesUntilExit P W (safeSet β A c) (aslDrift β A) (Qhat β A) X

/-- `m̂` is the PHD process (3.5) for the Brownian motion `W`, stopped at its first exit `τ_c` from
`S_{β,A}(c)`. -/
def IsPHD {Ω : Type*} [MeasurableSpace Ω] {n : ℕ} (P : Measure Ω) (W : ℝ≥0 → Ω → SDEState n)
    (β : ℝ) (A : Matrix (Fin n) (Fin n) ℝ) (c : ℝ) (X : ℝ≥0 → Ω → Fin n → ℝ) : Prop :=
  SolvesUntilExit P W (safeSet β A c) (fun _ => 0) (Qhat β A) X

/-- Coordinatewise `tanh`. -/
def tanhVec {n : ℕ} (x : Fin n → ℝ) : Fin n → ℝ := fun i => Real.tanh (x i)

/-- The dual domain `tanh⁻¹(S_{β,A}(c)) = {x ∈ ℝⁿ : tanh(x) ∈ S_{β,A}(c)}`. -/
def dualSafe {n : ℕ} (β : ℝ) (A : Matrix (Fin n) (Fin n) ℝ) (c : ℝ) : Set (Fin n → ℝ) :=
  {x | tanhVec x ∈ safeSet β A c}

/-- The dual diffusion coefficient `Σ̂(x) = D(m) Q̂(m)`, `m = tanh(x)`. -/
def dualSigma {n : ℕ} (β : ℝ) (A : Matrix (Fin n) (Fin n) ℝ) (x : Fin n → ℝ) :
    Matrix (Fin n) (Fin n) ℝ :=
  Dmat (tanhVec x) * Qhat β A (tanhVec x)

/-- The dual drift `f̂*(x) = E_{D_n}[Q̂(m)²] D(m)² m`, `m = tanh(x)`, of (d-PHD). -/
def dualPhdDrift {n : ℕ} (β : ℝ) (A : Matrix (Fin n) (Fin n) ℝ) (x : Fin n → ℝ) : Fin n → ℝ :=
  (diagPart (Qhat β A (tanhVec x) * Qhat β A (tanhVec x)) *
    (Dmat (tanhVec x) * Dmat (tanhVec x))).mulVec (tanhVec x)

/-- The drift `D(m)Q̂(m)(m − f(m)) + f̂*(x)`, `m = tanh(x)`, of (d-ASL-TAP). -/
def dualAslDrift {n : ℕ} (β : ℝ) (A : Matrix (Fin n) (Fin n) ℝ) (x : Fin n → ℝ) : Fin n → ℝ :=
  (dualSigma β A x).mulVec (tanhVec x - fDrift β A (tanhVec x)) + dualPhdDrift β A x

/-- The Jarzynski weight (JE) of a magnetization path stopped at `τ`:
`ŵ_t = ∫₀ᵗ 1{s<τ} ω(m̂_s) ds`. -/
def jeWeight {Ω : Type*} {n : ℕ} (β : ℝ) (A : Matrix (Fin n) (Fin n) ℝ) (τ : Ω → ℝ≥0∞)
    (X : ℝ≥0 → Ω → Fin n → ℝ) (t : ℝ) (ω : Ω) : ℝ :=
  ∫ u in (0 : ℝ)..t, if (u.toNNReal : ℝ≥0∞) < τ ω then omega β A (X u.toNNReal ω) else 0

end

end SKHessianAscent


