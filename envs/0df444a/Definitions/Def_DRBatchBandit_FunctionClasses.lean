-- Prove2me | Definitions.Def_DRBatchBandit_FunctionClasses
-- name    : DRBatchBandit_FunctionClasses
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T09:23:58.379541+00:00
-- url     : https://prove2.me/theorems/6d3c14a7-63a1-4904-b8c0-cd622dee9f98
-- title:
--   The function classes $\mathcal F_\Pi$, $\mathcal F_{\Pi,x}$, $\mathcal F_I$, $\mathcal F_{\Pi,\mathbb D}$ of the proof of Theorem 2
-- statement:
--   For a policy class $\Pi$, a logging policy $\pi_0$ and a draw $(X,Y,A)$ with reward vector $Y=(Y(a^1),\dots,Y(a^d))$ (pp.53–56):
--
--   1. $\mathcal F_\Pi=\Big\{f_\pi(X,A)=\dfrac{\mathbf 1\{\pi(X)=A\}}{\pi_0(A\mid X)}:\ \pi\in\Pi\Big\}$ (p.53);
--   2. $\mathcal F_{\Pi,x}=\Big\{f_{\pi,x}(X,Y,A)=\dfrac{\mathbf 1\{\pi(X)=A\}\mathbf 1\{Y(\pi(X))\le x\}}{\pi_0(A\mid X)}:\ \pi\in\Pi,\ x\in[0,M]\Big\}$ (p.53);
--   3. $\mathcal F_I=\{f(t)=\mathbf 1\{t\le x\}:\ x\in[0,M]\}$, functions on $\mathbb R$ (p.54);
--   4. $\mathcal F_{\Pi,\mathbb D}=\Big\{f_{\pi,S}(X,Y,A)=\dfrac{\mathbf 1\{\pi(X)=A\}\mathbf 1\{Y(\pi(X))\in S\}}{\pi_0(A\mid X)}:\ \pi\in\Pi,\ S\subset\mathbb D\Big\}$ (p.56).
--
--   Their Rademacher complexities control the estimation error of $\hat Q_{\mathrm{DRO}}$ in the proof of Theorem 2.
--
--   **Formalization Note** Functions of a draw `ω = (x, (y, a))`; $\pi_0(a\mid x)$ is `M.e x a` and the weight is written through the estimator's `ipw`. In item 4 the observed reward $Y$ is written $Y(\pi(X))$, which is the same on the event $\pi(X)=A$ where the weight is nonzero. $\mathbb D$ is a finite set and $S$ ranges over its subsets.
-- source:
--   Si, Zhang, Zhou & Blanchet, Distributionally Robust Batch Contextual Bandits, arXiv:2006.05630v7, proof of Theorem 2, p.53 (ℱ_{Π,x}, ℱ_Π), p.54 (ℱ_I), p.56 (ℱ_{Π,D}). PDF sha256 ac485985feb75d33b603f06f5a5d93c52077877db7be11de3d71107c7c374b02

import Mathlib
import Definitions.Def_OfflinePolicyLearning_Regret_Setting
import Definitions.Def_DRBatchBandit_Estimator

namespace DRBatchBandit

open OfflinePolicyLearning.Regret

variable {X : Type*} [MeasurableSpace X] {d : ℕ}

/-- The class `ℱ_Π = {f_π(X, A) = 1{π(X) = A} / π₀(A | X) | π ∈ Π}` (arXiv:2006.05630v7,
p.53), as functions of a draw `ω = (X, (Y(a¹), …, Y(a^d)), A)`. -/
def FPi (M : Model X d) (Pol : Set (X → Fin d)) : Set (Draw X d → ℝ) :=
  {f | ∃ π ∈ Pol, f = fun ω => ipw M π (obs ω)}

/-- The class `ℱ_{Π,x} = {f_{π,x}(X, Y, A) = 1{π(X) = A} 1{Y(π(X)) ≤ x} / π₀(A | X) |
π ∈ Π, x ∈ [0, M]}` (arXiv:2006.05630v7, p.53). -/
def FPix (M : Model X d) (Pol : Set (X → Fin d)) (Mrew : ℝ) : Set (Draw X d → ℝ) :=
  {f | ∃ π ∈ Pol, ∃ x ∈ Set.Icc 0 Mrew,
    f = fun ω => ipw M π (obs ω) * (if ω.2.1 (π ω.1) ≤ x then 1 else 0)}

/-- The class of half-line indicators `ℱ_I = {f(t) = 1{t ≤ x} | x ∈ [0, M]}`
(arXiv:2006.05630v7, p.54). -/
def FI (Mrew : ℝ) : Set (ℝ → ℝ) :=
  {f | ∃ x ∈ Set.Icc 0 Mrew, f = fun t => if t ≤ x then 1 else 0}

/-- The class `ℱ_{Π,𝔻} = {f_{π,S}(X, Y, A) = 1{π(X) = A} 1{Y ∈ S} / π₀(A | X) | π ∈ Π, S ⊂ 𝔻}`
(arXiv:2006.05630v7, p.56), with `Y = Y(π(X))` the reward of the action `π(X)`. -/
def FPiD (M : Model X d) (Pol : Set (X → Fin d)) (D : Finset ℝ) : Set (Draw X d → ℝ) :=
  {f | ∃ π ∈ Pol, ∃ S ⊆ D,
    f = fun ω => ipw M π (obs ω) * (if ω.2.1 (π ω.1) ∈ S then 1 else 0)}

end DRBatchBandit


