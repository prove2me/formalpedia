-- Prove2me | Definitions.Def_QCQPTightness_ConvHull_Faces
-- name    : QCQPTightness_ConvHull_Faces
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-09T17:26:49.250682+00:00
-- url     : https://prove2.me/theorems/85a29918-dd57-4ca8-ad97-b9f118b0ea69
-- title:
--   Assumptions 2–3, Definitions 1–2, pp. 8–12 — polyhedral sets, affine dimension, faces of Γ, ℱ(x̂), definite and semidefinite faces, 𝒱(ℱ)
-- statement:
--   This file adds the face structure of the dual object $\Gamma$ used by the paper's framework.
--
--   1. A set $S\subseteq\mathbb R^m$ is **polyhedral** if it is a finite intersection of closed half-spaces $\{\gamma: a_j^\top\gamma\le\beta_j\}$.
--   2. The **affine dimension** $\operatorname{aff\,dim}(S)$ is the dimension of the linear space parallel to the affine hull of $S$.
--   3. **Assumption 2 (p. 8):** for every $\hat x\in\mathbb R^N$, if $\sup_{\gamma\in\Gamma}q(\gamma,\hat x)$ is finite then it is attained in $\Gamma$. Over $\Gamma=\emptyset$ the supremum is $-\infty$, which is not finite, so the assumption asks nothing there; the Lean premise is therefore "$\Gamma\neq\emptyset$ and $\gamma\mapsto q(\gamma,\hat x)$ is bounded above on $\Gamma$".
--   4. **Assumption 3 (p. 12):** $\Gamma$ is polyhedral.
--   5. A **face** of $\Gamma$ is a nonempty convex subset $\mathcal F\subseteq\Gamma$ that is extreme: whenever a point of $\mathcal F$ lies in the open segment between two points of $\Gamma$, both endpoints lie in $\mathcal F$.
--   6. **Definition 1 (p. 8):** $\mathcal F(\hat x)=\arg\max_{\gamma\in\Gamma}q(\gamma,\hat x)$.
--   7. **Definition 2 (p. 9):** a face $\mathcal F$ is **definite** if some $\gamma\in\mathcal F$ has $A(\gamma)\succ0$, and **semidefinite** otherwise; its **shared zero eigenspace** is
--   $$\mathcal V(\mathcal F)=\{v\in\mathbb R^N:\ A(\gamma)v=0\ \ \forall\gamma\in\mathcal F\}.$$
--
--   The convex hull theorem is a statement about semidefinite faces: it asks $\mathcal V(\mathcal F)$ to be large compared with the affine dimension of $\{b(\gamma):\gamma\in\mathcal F\}$.
--
--   **Formalization Note.** Faces are required to be nonempty. The page's convention $\operatorname{aff\,dim}(\emptyset)=-1$ makes the empty face impose nothing in the paper's hypotheses, while Lean's `affdim ∅` is $0$; excluding the empty face keeps the hypotheses equal to the paper's. Definition 1 is formalized as the argmax set for every $\hat x$; the paper uses it only where the supremum is finite, where under Assumption 2 it is a nonempty face. The page writes $q(\gamma,x)$ inside the argmax and "$\hat x\in\mathbb R^n$" in Assumption 2; both mean $\hat x\in\mathbb R^N$. "Polyhedral" admits zero half-spaces (the whole space).
-- source:
--   arXiv:1911.09195v3, Assumption 2 p. 8, Definition 1 p. 8, Definition 2 p. 9, Assumption 3 p. 12, notation p. 6

import Mathlib
import Definitions.Def_QCQPTightness_ConvHull_QCQP

noncomputable section

namespace QCQPTightness.ConvHull

open Matrix

/-- A polyhedral subset of `ℝ^m`: a finite intersection of closed halfspaces. -/
def IsPolyhedral {m : ℕ} (S : Set (Fin m → ℝ)) : Prop :=
  ∃ (p : ℕ) (a : Fin p → Fin m → ℝ) (β : Fin p → ℝ), S = {γ | ∀ j, a j ⬝ᵥ γ ≤ β j}

/-- The affine dimension `aff dim(S)`, as the dimension of the direction of the affine span.
Only applied to nonempty sets (for `S = ∅` it is `0`, not the convention `-1`). -/
def affdim {E : Type*} [AddCommGroup E] [Module ℝ E] (S : Set E) : ℕ :=
  Module.finrank ℝ (vectorSpan ℝ S)

namespace QCQP

variable {N m : ℕ} (P : QCQP N m)

/-- Assumption 2 (p. 8): whenever `sup_{γ∈Γ} q(γ, x̂)` is finite it is attained in `Γ`.
The sup is finite exactly when `Γ` is nonempty and the values are bounded above
(over `Γ = ∅` the sup is `−∞`, not finite). -/
def Assumption2 : Prop :=
  ∀ x : Fin N → ℝ, P.Gamma.Nonempty → BddAbove ((fun γ => P.qγ γ x) '' P.Gamma) →
    ∃ γ ∈ P.Gamma, ∀ γ' ∈ P.Gamma, P.qγ γ' x ≤ P.qγ γ x

/-- Assumption 3 (p. 12): `Γ` is polyhedral. -/
def Assumption3 : Prop := IsPolyhedral P.Gamma

/-- A (nonempty) face of `Γ`: a nonempty convex extreme subset. -/
def IsFace (F : Set (Fin m → ℝ)) : Prop :=
  F.Nonempty ∧ Convex ℝ F ∧ IsExtreme ℝ P.Gamma F

/-- `ℱ(x̂) = argmax_{γ∈Γ} q(γ, x̂)` (Definition 1, p. 8). -/
def faceOf (x : Fin N → ℝ) : Set (Fin m → ℝ) :=
  {γ | γ ∈ P.Gamma ∧ ∀ γ' ∈ P.Gamma, P.qγ γ' x ≤ P.qγ γ x}

/-- A definite face (Definition 2, p. 9): some `γ ∈ ℱ` has `A(γ) ≻ 0`. -/
def IsDefiniteFace (F : Set (Fin m → ℝ)) : Prop :=
  P.IsFace F ∧ ∃ γ ∈ F, (P.Aγ γ).PosDef

/-- A semidefinite face (Definition 2, p. 9): a face that is not definite. -/
def IsSemidefiniteFace (F : Set (Fin m → ℝ)) : Prop :=
  P.IsFace F ∧ ¬ ∃ γ ∈ F, (P.Aγ γ).PosDef

/-- The shared zero eigenspace `𝒱(ℱ) = {v ∈ ℝ^N : A(γ)v = 0 ∀ γ ∈ ℱ}` (Definition 2, p. 9). -/
def V (F : Set (Fin m → ℝ)) : Submodule ℝ (Fin N → ℝ) :=
  ⨅ γ ∈ F, LinearMap.ker (P.Aγ γ).mulVecLin

end QCQP

end QCQPTightness.ConvHull


