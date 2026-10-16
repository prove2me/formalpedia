-- Prove2me | Definitions.Def_OAI_InformationTheory_AmplitudeDamping_Pinching
-- name    : OAI_InformationTheory_AmplitudeDamping_Pinching
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-15T20:54:23.284342+00:00
-- url     : https://prove2.me/theorems/f430f766-5ded-4087-9c84-1ef6e084dac6
-- title:
--   Sign-flip unitaries and partial pinchings of a square matrix
-- statement:
--   Let $\mathcal I$ be a finite index set and $A$ a complex $\mathcal I\times\mathcal I$ matrix.
--
--   1. **Sign flip.** For $k\in\mathcal I$, $F_k$ is the diagonal matrix with $(F_k)_{kk}=-1$ and $(F_k)_{ii}=1$ for $i\neq k$. It is unitary (indeed $F_k^*=F_k=F_k^{-1}$) and is regarded as an element of the unitary group of $\mathbb{C}^{\mathcal I}$.
--   2. **Partial pinching.** For a subset $s\subseteq\mathcal I$,
--   $$\bigl(\mathcal P_s(A)\bigr)_{ij}=\begin{cases}A_{ij}&\text{if } i=j\ \text{ or }\ (i\notin s\text{ and } j\notin s),\\ 0&\text{otherwise}.\end{cases}$$
--   Thus $\mathcal P_s$ erases every off-diagonal entry lying in a row or a column indexed by $s$ and keeps the diagonal together with the principal block on $\mathcal I\setminus s$. In particular $\mathcal P_\varnothing(A)=A$, and $\mathcal P_{\mathcal I}(A)=\operatorname{diag}(A_{ii})_{i\in\mathcal I}$ is the full pinching onto the diagonal.
--
--   The two objects are linked by the averaging identity
--   $$\mathcal P_{s\cup\{k\}}(A)=\tfrac12\,\mathcal P_s(A)+\tfrac12\,F_k\,\mathcal P_s(A)\,F_k^{*},$$
--   which writes each pinching step as an average of unitary conjugates; partial pinchings of positive definite matrices stay positive definite. Combined with the joint convexity and unitary invariance of the block log-determinant deficit $\operatorname{blockLogDet}(Z,D,E)=\log|\det(D+ZE^{-1}Z^*)|-\log|\det D|$, this shows that for a diagonal matrix $Z$ and positive definite $D,E$, replacing $D$ and $E$ by their diagonal parts can only decrease the deficit.
--
--   **Formalization Note** `flipSign k` is a term of `Matrix.unitaryGroup ι ℂ` (the matrix bundled with a proof of unitarity), and `partialPinch s A` takes `s : Finset ι`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/InformationTheory/AmplitudeDamping/Pinching.lean

-- Generated from openai/math@1581d4c lean/OAI/InformationTheory/AmplitudeDamping/Pinching.lean by skeleton subtraction
-- (upload_full_project.md Phase 3): Definitions bundle for the AmplitudeDamping mission closure.
-- Kept: reachable definitions/instances and the theorems their bodies or the node statements cite.
-- Project imports rewritten to platform modules; otherwise byte-identical to the source.
import Mathlib
import Definitions.Def_AmplitudeDamping
import Definitions.Def_OAI_InformationTheory_AmplitudeDamping_Channel
import Definitions.Def_OAI_InformationTheory_AmplitudeDamping_MatrixDifferentiation
import Definitions.Def_OAI_InformationTheory_AmplitudeDamping_LogDetConvexity
import Definitions.Def_OAI_InformationTheory_AmplitudeDamping_LogDetEntropy

namespace OAI

universe u_1

noncomputable section
open scoped BigOperators Matrix.Norms.Elementwise
open Matrix
open scoped BigOperators ComplexOrder MatrixOrder
open scoped Matrix.Norms.Elementwise ComplexOrder MatrixOrder
open Matrix Set
open scoped ComplexOrder MatrixOrder
open scoped BigOperators Topology
open Filter Set
open scoped BigOperators ComplexOrder MatrixOrder Topology

open scoped BigOperators ComplexOrder MatrixOrder
open Matrix Set
namespace GAD
variable {ι : Type u_1} [Fintype ι] [DecidableEq ι]

def flipSign (k : ι) : Matrix.unitaryGroup ι ℂ :=
  ⟨Matrix.diagonal (fun i ↦ if i = k then (-1 : ℂ) else 1), by
    rw [Matrix.mem_unitaryGroup_iff]
    simp only [Matrix.star_eq_conjTranspose, Matrix.diagonal_conjTranspose]
    rw [Matrix.diagonal_mul_diagonal]
    ext i j
    by_cases h : i = j
    · subst j
      simp only [Matrix.diagonal_apply_eq, Matrix.one_apply_eq]
      by_cases hi : i = k <;> simp [hi]
    · simp [Matrix.diagonal_apply_ne _ h, Matrix.one_apply_ne h]⟩

def partialPinch (s : Finset ι) (A : Matrix ι ι ℂ) : Matrix ι ι ℂ :=
  fun i j ↦ if i = j ∨ (i ∉ s ∧ j ∉ s) then A i j else 0

end GAD

end

end OAI


