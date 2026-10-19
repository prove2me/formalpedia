-- Prove2me | Definitions.Def_OAI_Combinatorics_SecondNeighborhood_MatrixMaps
-- name    : OAI_Combinatorics_SecondNeighborhood_MatrixMaps
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-19T11:51:39.799216+00:00
-- url     : https://prove2.me/theorems/5fe8a2dc-b3da-4471-9d24-abd15dd4b031
-- title:
--   Weighted incidence matrices $L$, $N$, $B$, $A$ of the pruning configuration
-- statement:
--   Let $r$ be a relation on a finite set $V$. Consider finite sets $R,C\subseteq V\times V$ of pairs. A pair $a\in R$ and a pair $b\in C$ conflict if $a_1\to b_1$ and $b_2\to a_2$. A pair $a\in R$ left-covers $z$ if $a_2=z_2$ and $a_1\to z_1$, and $b\in C$ right-covers $z$ if $b_1=z_1$ and $b_2\to z_2$. $Z(R,C)$ is the set of pairs $z$ that are both left-covered by some element of $R$ and right-covered by some element of $C$. $H(R,C)$ is the set of hub pairs. Let $a,b:V\times V\to\mathbb{R}$ be coefficient functions; $a$ is supported on $r$ if $a(x,y)=0$ whenever $x\not\to y$.
--
--   1. **$L$** ($Z\times R$): $L_{z,\rho}=a(\rho_1,z_1)$ if $z_2=\rho_2$, and $0$ otherwise.
--   2. **$N$** ($C\times Z$): $N_{\gamma,z}=b(\gamma_2,z_2)$ if $\gamma_1=z_1$, and $0$ otherwise.
--   3. **$B$** ($H\times R$): $B_{h,\rho}=b(h_2,\rho_2)$ if $h_1=\rho_1$, and $0$ otherwise.
--   4. **$A$** ($C\times H$): $A_{\gamma,h}=a(h_1,\gamma_1)$ if $\gamma_2=h_2$, and $0$ otherwise.
--
--   With coefficients supported on the arcs, the nonzero patterns of these matrices are exactly the cover and hub incidences. Rank inequalities among their products then yield the counting bounds of the pruning lemma.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/SecondNeighborhood/MatrixMaps.lean

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/SecondNeighborhood/MatrixMaps.lean by skeleton subtraction
-- (upload_full_project.md Phase 3): Definitions bundle for the SeymourSecondNeighborhood mission closure.
-- Kept: reachable definitions/instances and the theorems their bodies or the node statements cite.
-- Project imports rewritten to platform modules; otherwise byte-identical to the source.
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.MvPolynomial.Funext
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Combinatorics.Hall.Finite
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Max
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Finset.Sum
import Mathlib.Data.Finset.Union
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Fintype.Sum
import Mathlib.Data.Matrix.Mul
import Mathlib.Data.Nat.Find
import Mathlib.Data.Real.Basic
import Mathlib.LinearAlgebra.Dimension.Finite
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.Matrix.MvPolynomial
import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.Tactic.Tauto
import Definitions.Def_SeymourSecondNeighborhood
import Definitions.Def_OAI_Combinatorics_SecondNeighborhood_Basic
import Definitions.Def_OAI_Combinatorics_SecondNeighborhood_ReductionCore
import Definitions.Def_OAI_Combinatorics_SecondNeighborhood_Reindex
import Definitions.Def_OAI_Combinatorics_SecondNeighborhood_MinimalCounterexample
import Definitions.Def_OAI_Combinatorics_SecondNeighborhood_Deletion
import Definitions.Def_OAI_Combinatorics_SecondNeighborhood_TransitiveBlowup
import Definitions.Def_OAI_Combinatorics_SecondNeighborhood_PruningDefinitions
import Definitions.Def_OAI_Combinatorics_SecondNeighborhood_Matching
import Definitions.Def_OAI_Combinatorics_SecondNeighborhood_AugmentedGraph
import Definitions.Def_OAI_Combinatorics_SecondNeighborhood_MatchingAugmented
import Definitions.Def_OAI_Combinatorics_SecondNeighborhood_GenericRankMatching
import Definitions.Def_OAI_Combinatorics_SecondNeighborhood_GenericRank

namespace OAI

namespace SeymourSecondNeighborhood.Pruning

variable {V : Type*}

def SupportedCoefficients (r : V → V → Prop) (a : V → V → ℝ) : Prop :=
  ∀ x y, ¬ r x y → a x y = 0

variable [Fintype V] [DecidableEq V]

noncomputable section

def matrixL (r : V → V → Prop) (R C : Finset (V × V)) (a : V → V → ℝ) :
    Matrix ↥(Z r R C) ↥R ℝ :=
  Matrix.of fun z left => if z.val.2 = left.val.2 then a left.val.1 z.val.1 else 0

def matrixN (r : V → V → Prop) (R C : Finset (V × V)) (b : V → V → ℝ) :
    Matrix ↥C ↥(Z r R C) ℝ :=
  Matrix.of fun right z => if right.val.1 = z.val.1 then b right.val.2 z.val.2 else 0

def matrixB (r : V → V → Prop) (R C : Finset (V × V)) (b : V → V → ℝ) :
    Matrix ↥(H r R C) ↥R ℝ :=
  Matrix.of fun h left => if h.val.1 = left.val.1 then b h.val.2 left.val.2 else 0

def matrixA (r : V → V → Prop) (R C : Finset (V × V)) (a : V → V → ℝ) :
    Matrix ↥C ↥(H r R C) ℝ :=
  Matrix.of fun right h => if right.val.2 = h.val.2 then a h.val.1 right.val.1 else 0

@[simp] theorem matrixL_apply (r : V → V → Prop) (R C : Finset (V × V))
    (a : V → V → ℝ) (z : ↥(Z r R C)) (left : ↥R) :
    matrixL r R C a z left =
      if z.val.2 = left.val.2 then a left.val.1 z.val.1 else 0 := rfl

@[simp] theorem matrixN_apply (r : V → V → Prop) (R C : Finset (V × V))
    (b : V → V → ℝ) (right : ↥C) (z : ↥(Z r R C)) :
    matrixN r R C b right z =
      if right.val.1 = z.val.1 then b right.val.2 z.val.2 else 0 := rfl

@[simp] theorem matrixB_apply (r : V → V → Prop) (R C : Finset (V × V))
    (b : V → V → ℝ) (h : ↥(H r R C)) (left : ↥R) :
    matrixB r R C b h left =
      if h.val.1 = left.val.1 then b h.val.2 left.val.2 else 0 := rfl

@[simp] theorem matrixA_apply (r : V → V → Prop) (R C : Finset (V × V))
    (a : V → V → ℝ) (right : ↥C) (h : ↥(H r R C)) :
    matrixA r R C a right h =
      if right.val.2 = h.val.2 then a h.val.1 right.val.1 else 0 := rfl

end
end SeymourSecondNeighborhood.Pruning

end OAI


