-- Prove2me | Definitions.Def_QCQPTightness_Sharp_Faces
-- name    : QCQPTightness_Sharp_Faces
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-09T18:22:43.663096+00:00
-- url     : https://prove2.me/theorems/ccc780cb-c92a-4b36-b442-22cc249031b0
-- title:
--   Assumptions 2–3, Definitions 1–2, pp. 8–12 — polyhedrality, attainment, faces of Γ, ℱ(x̂), definite and semidefinite faces, 𝒱(ℱ), affine dimension
-- statement:
--   Let a QCQP with dual set $\Gamma\subseteq\mathbb R^m$ be given.
--
--   1. **Assumption 2**: for every $\hat x\in\mathbb R^N$, if $\sup_{\gamma\in\Gamma}q(\gamma,\hat x)$ is finite, then it is attained in $\Gamma$.
--   2. **Assumption 3**: $\Gamma$ is **polyhedral**, i.e. a finite intersection of closed halfspaces.
--   3. A **face** of $\Gamma$ is a nonempty convex subset $\mathcal F\subseteq\Gamma$ that is extreme: whenever an open segment between two points of $\Gamma$ meets $\mathcal F$, both endpoints lie in $\mathcal F$.
--   4. $\mathcal F(\hat x)=\arg\max_{\gamma\in\Gamma}q(\gamma,\hat x)$ (Definition 1).
--   5. A face $\mathcal F$ is **definite** if $A(\gamma)\succ0$ for some $\gamma\in\mathcal F$, and **semidefinite** otherwise; its **shared zero eigenspace** is
--   $$
--   \mathcal V(\mathcal F)=\{v\in\mathbb R^N : A(\gamma)v=0\ \ \forall\gamma\in\mathcal F\}.
--   $$
--   6. The **affine dimension** $\operatorname{aff\,dim}(S)$ of a set $S$ is the dimension of its affine hull.
--
--   These notions enter the hypotheses of the paper's main Theorems 1 and 2 and of the sharpness results.
--
--   **Formalization Note** Faces are required to be nonempty (the empty face plays no role in the paper's statements); `affdim` is the dimension of the vector span of $S-S$, which equals $0$ on the empty set instead of the convention $-1$, and is only applied to nonempty sets.
-- source:
--   arXiv:1911.09195v3, Assumption 2 (p. 8), Definition 1 (p. 8), Definition 2 (p. 9), Assumption 3 (p. 12)

import Mathlib
import Definitions.Def_QCQPTightness_Sharp_QCQP

noncomputable section

namespace QCQPTightness.Sharp

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

/-- Assumption 2 (p. 8): whenever `sup_{γ∈Γ} q(γ, x̂)` is finite it is attained in `Γ`. -/
def Assumption2 : Prop :=
  ∀ x : Fin N → ℝ, BddAbove ((fun γ => P.qγ γ x) '' P.Gamma) →
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

end QCQPTightness.Sharp


