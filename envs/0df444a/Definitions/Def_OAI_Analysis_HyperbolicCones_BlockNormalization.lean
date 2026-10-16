-- Prove2me | Definitions.Def_OAI_Analysis_HyperbolicCones_BlockNormalization
-- name    : OAI_Analysis_HyperbolicCones_BlockNormalization
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-15T18:41:52.837986+00:00
-- url     : https://prove2.me/theorems/d6144c5a-09b2-487e-b37d-e1d1051b976f
-- title:
--   Normalizing a raw two-block representation to unital diagonal blocks
-- statement:
--   Let $\mathrm{Sym}_n$ be the real symmetric $n\times n$ matrices. Write $M\succeq0$ when $M$ is positive semidefinite and $M\succ0$ when it is positive definite. Let $\mathcal V=\mathrm{Sym}_4\times\mathrm{Sym}_4\times\mathbb{R}^3$, with points $(X,Z,y)$, and fix a set $K\subseteq\mathcal V$. A linear map $\Phi:\mathrm{Sym}_4\to\mathrm{Sym}_k$ is positive if $X\succeq0$ implies $\Phi(X)\succeq0$. For integers $a,c\ge1$, a family of linear maps $D,F:\mathrm{Sym}_4\to\mathrm{Sym}_a$, $E:\mathrm{Sym}_4\to\mathrm{Sym}_c$, $C:\mathrm{Sym}_4\to\mathbb{R}^{a\times c}$, $A:\mathbb{R}^3\to\mathrm{Sym}_a$, $B:\mathbb{R}^3\to\mathbb{R}^{a\times c}$ and $G:\mathbb{R}^3\to\mathrm{Sym}_c$ *represents* $K$ if for all $(X,Z,y)\in\mathcal V$
--
--   $$
--   (X,Z,y)\in K\iff\begin{pmatrix}D(X)+F(Z)+A(y) & C(Z)+B(y)\\ \bigl(C(Z)+B(y)\bigr)^{\mathsf T} & E(Z)+G(y)\end{pmatrix}\succeq0 .
--   $$
--
--   A *raw block pencil* for $K$ is a representing family in which $D$ and $E$ are positive and $D(I_4)\succ0$, $E(I_4)\succ0$. A *block pencil* for $K$ is a representing family in which $D$ and $E$ are positive and unital, $D(I_4)=I_a$ and $E(I_4)=I_c$.
--
--   The file defines the **normalization** of a raw block pencil. Let $S=D(I_4)^{-1/2}$ and $T=E(I_4)^{-1/2}$ be the inverse square roots of the positive definite matrices $D(I_4)$ and $E(I_4)$, that is, the positive definite square roots of $D(I_4)^{-1}$ and $E(I_4)^{-1}$, computed from a spectral decomposition. The normalized pencil has the same sizes $a,c$ and the maps
--
--   $$
--   D'=S^{\mathsf T}D(\cdot)S,\quad F'=S^{\mathsf T}F(\cdot)S,\quad A'=S^{\mathsf T}A(\cdot)S,\quad E'=T^{\mathsf T}E(\cdot)T,\quad G'=T^{\mathsf T}G(\cdot)T,\quad C'=S^{\mathsf T}C(\cdot)T,\quad B'=S^{\mathsf T}B(\cdot)T .
--   $$
--
--   It is a block pencil for the same set $K$. The maps $D'$ and $E'$ are positive, $D'(I_4)=I_a$, $E'(I_4)=I_c$, and $(X,Z,y)\in K$ exactly when the block matrix built from the primed maps is positive semidefinite.
--
--   With this normalization, a two-block representation of a set may be assumed to have unital diagonal maps. This is the form required by the later rescaling and limiting argument, which extracts a normalized Schur-complement pencil from it.
--
--   **Formalization Note** The definition is `RawBlockPencil.normalize`, which produces a `BlockPencil K` from a `RawBlockPencil K`. It composes the blocks with `congruenceSym S`, `congruenceSym T` and `congruenceRect S T`, where `S` and `T` are `inverseSquareRoot` of the identity values. The structure fields carry the verification of positivity, unitality and the representation property.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/HyperbolicCones/BlockNormalization.lean

-- Generated from openai/math@1581d4c lean/OAI/Analysis/HyperbolicCones/BlockNormalization.lean by skeleton subtraction
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
import Definitions.Def_OAI_Analysis_HyperbolicCones_SplitFrame
import Definitions.Def_OAI_Analysis_HyperbolicCones_CongruenceMaps

namespace OAI

/-! Fixed positive-definite diagonal congruence makes both positive maps unital. -/

noncomputable section
open scoped Matrix.Norms.L2Operator MatrixOrder
open Matrix Set
namespace Paper256

noncomputable def RawBlockPencil.normalize {K : Set Ambient} (P : RawBlockPencil K) :
    BlockPencil K := by
  let S := inverseSquareRoot (P.D 1)
  let T := inverseSquareRoot (P.E 1)
  refine {
    a := P.a
    c := P.c
    a_pos := P.a_pos
    c_pos := P.c_pos
    D := (congruenceSym S).comp P.D
    E := (congruenceSym T).comp P.E
    F := (congruenceSym S).comp P.F
    C := (congruenceRect S T).comp P.C
    A := (congruenceSym S).comp P.A
    B := (congruenceRect S T).comp P.B
    G := (congruenceSym T).comp P.G
    D_positive := fun X hX => congruenceSym_positive S (P.D X) (P.D_positive X hX)
    E_positive := fun Z hZ => congruenceSym_positive T (P.E Z) (P.E_positive Z hZ)
    D_unital := congruenceSym_inverseSquareRoot_self (P.D 1) P.D_identity_posDef
    E_unital := congruenceSym_inverseSquareRoot_self (P.E 1) P.E_identity_posDef
    represents := ?_ }
  intro X Z y
  rw [P.represents]
  have h := block_congruence_posSemidef_iff S T
    (inverseSquareRoot_isUnit (P.D 1) P.D_identity_posDef)
    (inverseSquareRoot_isUnit (P.E 1) P.E_identity_posDef)
    ((P.D X : Mat P.a ℝ) + (P.F Z : Mat P.a ℝ) + (P.A y : Mat P.a ℝ))
    (P.C Z + P.B y) ((P.E Z : Mat P.c ℝ) + (P.G y : Mat P.c ℝ))
  simpa only [LinearMap.comp_apply, congruenceSym_val, congruenceRect_apply,
    Matrix.mul_add, Matrix.add_mul] using h.symm

end Paper256

end

end OAI


