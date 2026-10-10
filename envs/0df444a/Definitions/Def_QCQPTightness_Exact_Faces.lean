-- Prove2me | Definitions.Def_QCQPTightness_Exact_Faces
-- name    : QCQPTightness_Exact_Faces
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-09T18:19:57.198013+00:00
-- url     : https://prove2.me/theorems/7140f851-0521-4026-8420-e6fdd8f3d8bd
-- title:
--   Assumptions 2–3, Definitions 1–2, pp. 8–12 — faces of Γ, ℱ(x̂), definite and semidefinite faces, 𝒱(ℱ)
-- statement:
--   Let $\Gamma\subseteq\mathbb R^m$ be the dual object of a QCQP. This file fixes the face notions used throughout the paper.
--
--   1. A set is **polyhedral** if it is a finite intersection of closed half-spaces. **Assumption 3** asserts that $\Gamma$ is polyhedral.
--   2. **Assumption 2** asserts that for every $\hat x\in\mathbb R^N$, if $\sup_{\gamma\in\Gamma}q(\gamma,\hat x)$ is finite, then the supremum is attained in $\Gamma$.
--   3. A **face** of $\Gamma$ is a nonempty convex subset $\mathcal F\subseteq\Gamma$ such that whenever an open segment between two points of $\Gamma$ meets $\mathcal F$, both endpoints lie in $\mathcal F$.
--   4. For $\hat x\in\mathbb R^N$, $\mathcal F(\hat x) := \arg\max_{\gamma\in\Gamma} q(\gamma,\hat x)$ (Definition 1).
--   5. A face $\mathcal F$ is **definite** if some $\gamma\in\mathcal F$ has $A(\gamma)\succ 0$, and **semidefinite** otherwise. Its **shared zero eigenspace** is (Definition 2)
--
--   $$\mathcal V(\mathcal F)=\{v\in\mathbb R^N : A(\gamma)v=0\ \ \forall\gamma\in\mathcal F\}.$$
--
--   The paper's sufficient conditions for exactness are statements about the semidefinite faces of $\Gamma$ and their shared zero eigenspaces.
--
--   **Formalization Note** Faces are required to be nonempty, which excludes the empty face; the paper never applies its conditions to it. $\mathcal F(\hat x)$ is defined for every $\hat x$ as the set of maximizers, which is empty when the supremum is not attained. The affine dimension `affdim` is the dimension of the direction of the affine span, and is only meaningful for nonempty sets. In Assumption 2, "the supremum is finite" is encoded as $\Gamma\neq\emptyset$ and the values bounded above: over $\Gamma=\emptyset$ the supremum is $-\infty$, so the assumption says nothing there.
-- source:
--   arXiv:1911.09195v3, Assumption 2 and Definition 1 p. 8, Definition 2 p. 9, Assumption 3 p. 12

import Mathlib
import Definitions.Def_QCQPTightness_Exact_QCQP

noncomputable section

namespace QCQPTightness.Exact

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

end QCQPTightness.Exact


