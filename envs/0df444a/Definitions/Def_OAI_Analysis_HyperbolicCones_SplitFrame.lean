-- Prove2me | Definitions.Def_OAI_Analysis_HyperbolicCones_SplitFrame
-- name    : OAI_Analysis_HyperbolicCones_SplitFrame
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-15T18:38:33.150405+00:00
-- url     : https://prove2.me/theorems/670d5d45-e2b8-4f9a-8770-ce64910cb497
-- title:
--   Spectral splittings of a symmetric matrix and rectangular blocks of a pencil
-- statement:
--   Write $[k]=\{0,1,\dots,k-1\}$ and let $\mathrm{Sym}_m$ be the real symmetric $m\times m$ matrices, with rows and columns indexed by $[m]$. For $A\in\mathrm{Sym}_m$, let $\lambda_0,\dots,\lambda_{m-1}$ be its eigenvalues, listed with multiplicity. They are indexed by $[m]$ through a fixed orthonormal eigenbasis $U$, so that $U^{\mathsf T}AU=\operatorname{diag}(\lambda_0,\dots,\lambda_{m-1})$ and eigenvalue indices become row indices after this change of basis.
--
--   1. **Spectral split.** A spectral split of $A$ consists of integers $a,c\ge1$ and a bijection $e:[a]\sqcup[c]\to[m]$ from the disjoint union of the two index sets such that
--   $$
--   \lambda_{e(i)}>0\ \text{ for } i \text{ in the first part }[a],\qquad \lambda_{e(j)}\le0\ \text{ for } j \text{ in the second part }[c].
--   $$
--   In particular $a+c=m$, $a$ is the number of positive eigenvalues of $A$, and both numbers are nonzero.
--   2. **Rectangular blocks of a pencil.** For a real vector space $V$, a linear map $L:V\to\mathrm{Sym}_m$ and maps $f:[a]\to[m]$, $g:[c]\to[m]$, the linear map $L_{f,g}:V\to\mathbb{R}^{a\times c}$ with $L_{f,g}(x)_{ij}=L(x)_{f(i)\,g(j)}$.
--
--   Spectral splits are applied to a positive semidefinite, nonzero, singular matrix $A$, namely the value at the identity of the first component of a spectrahedral representation. For such $A$, a split separates the positive eigendirections ($a\ge1$) from the kernel ($c\ge1$). The representation is then rewritten in the eigenbasis $U$, and $f$ and $g$ are taken to be the two parts of $e$. Square restrictions along $f$ or $g$ and rectangular blocks $L_{f,g}$ of the rewritten representation give the diagonal and off-diagonal blocks of the resulting two-block representation.
--
--   **Formalization Note** The structure is `PencilSpectralSplit A`, whose eigenvalues are those of Mathlib's `IsHermitian.eigenvalues` and whose bijection `index` is an equivalence from `Fin a ⊕ Fin c` to `Fin m`. The nonpositivity condition is stated as the negation of positivity. The rectangular block map is `rectangularPencil L f g`, built with `Matrix.submatrix`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/HyperbolicCones/SplitFrame.lean

-- Generated from openai/math@1581d4c lean/OAI/Analysis/HyperbolicCones/SplitFrame.lean by skeleton subtraction
-- (upload_full_project.md Phase 3): Definitions bundle for the HyperbolicCones mission closure.
-- Kept: reachable definitions/instances and the theorems their bodies or the node statements cite.
-- Project imports rewritten to platform modules; otherwise byte-identical to the source.
import Mathlib
import Definitions.Def_HyperbolicCones
import Definitions.Def_OAI_Analysis_HyperbolicCones_Model
import Definitions.Def_OAI_Analysis_HyperbolicCones_MatrixBasic
import Definitions.Def_OAI_Analysis_HyperbolicCones_MatrixLinear
import Definitions.Def_OAI_Analysis_HyperbolicCones_PencilConjugation
import Definitions.Def_OAI_Analysis_HyperbolicCones_PencilBlocks
import Definitions.Def_OAI_Analysis_HyperbolicCones_RawBlocks
import Definitions.Def_OAI_Analysis_HyperbolicCones_KernelSpectrum
import Definitions.Def_OAI_Analysis_HyperbolicCones_PencilTopology
import Definitions.Def_OAI_Analysis_HyperbolicCones_SplitBasic

namespace OAI

noncomputable section

open Set Matrix
open scoped Matrix.Norms.L2Operator

universe u

namespace Paper256

structure PencilSpectralSplit {m : ℕ} (A : Sym m) where
  a : ℕ
  c : ℕ
  a_pos : 0 < a
  c_pos : 0 < c
  index : (Fin a ⊕ Fin c) ≃ Fin m
  positive : ∀ i, 0 < (sym_isHermitian A).eigenvalues (index (Sum.inl i))
  nonpositive : ∀ i, ¬ 0 < (sym_isHermitian A).eigenvalues (index (Sum.inr i))

def rectangularPencil {V : Type u} [AddCommGroup V] [Module ℝ V]
    {m a c : ℕ} (L : V →ₗ[ℝ] Sym m) (f : Fin a → Fin m) (g : Fin c → Fin m) :
    V →ₗ[ℝ] Matrix (Fin a) (Fin c) ℝ where
  toFun x := (L x : Mat m ℝ).submatrix f g
  map_add' x y := by ext i j; simp
  map_smul' s x := by ext i j; simp

end Paper256

end

end OAI


