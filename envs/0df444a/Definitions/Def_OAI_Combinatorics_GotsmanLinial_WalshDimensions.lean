-- Prove2me | Definitions.Def_OAI_Combinatorics_GotsmanLinial_WalshDimensions
-- name    : OAI_Combinatorics_GotsmanLinial_WalshDimensions
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-15T02:49:13.595432+00:00
-- url     : https://prove2.me/theorems/8fea7364-63b3-45ba-b5bf-87bf2f925319
-- title:
--   Dimensions of the Walsh degree filtration: $\dim V_{\le k}=\sum_{j\le k}\binom nj$
-- statement:
--   Let $Q_n=\{-1,1\}^n$, let $\chi_S$ ($S\subseteq[n]$) be the Walsh characters, and let $V_{\le k}=\operatorname{span}_{\mathbb{C}}\{\chi_S:|S|\le k\}$ be the space of complex functions on $Q_n$ of Fourier degree at most $k$. This module computes the dimensions of the degree filtration from the linear independence of the characters.
--
--   1. **Counting low-degree indices.** For all $n,k\in\mathbb{N}$, the number of subsets $S\subseteq[n]$ with $|S|\le k$ is $\sum_{j=0}^{k}\binom nj$.
--
--   2. **Dimension formula.** For all $n,k\in\mathbb{N}$,
--   $$
--   \dim_{\mathbb{C}}V_{\le k}=\sum_{j=0}^{k}\binom{n}{j}.
--   $$
--   The formula is valid also for $k\ge n$, where the terms with $j>n$ vanish and the sum equals $2^n$.
--
--   3. **Constants.** In particular $\dim_{\mathbb{C}}V_{\le0}=1$.
--
--   The successive differences $\dim V_{\le k}-\dim V_{\le k-1}=\binom nk$ are the dimensions of the layers of the degree filtration; since an invertible reweighting preserves dimensions, they are the ranks of the projections in the weighted degree grading of the Gotsman–Linial argument.
--
--   **Formalization Note** The results are `card_finset_card_le`, `fourierSpace_finrank` and `fourierSpace_zero_finrank`; the bundle introduces no new definitions, only these dimension statements about `fourierSpace`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/GotsmanLinial/WalshDimensions.lean

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/GotsmanLinial/WalshDimensions.lean by skeleton subtraction
-- (upload_full_project.md Phase 3): Definitions bundle for the GotsmanLinial mission closure.
-- Kept: reachable definitions/instances and the theorems their bodies or the node statements cite.
-- Project imports rewritten to platform modules; otherwise byte-identical to the source.
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.MvPolynomial.Degrees
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Data.Complex.BigOperators
import Mathlib.Data.Fin.Rev
import Mathlib.Data.Finset.SymmDiff
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Data.Real.Basic
import Mathlib.InformationTheory.Hamming
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.Matrix.Hermitian
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.LinearAlgebra.Trace
import Mathlib.LinearAlgebra.UnitaryGroup
import Mathlib.Tactic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Definitions.Def_GotsmanLinial
import Definitions.Def_OAI_Combinatorics_GotsmanLinial_Model
import Definitions.Def_OAI_Combinatorics_GotsmanLinial_Statement
import Definitions.Def_OAI_Combinatorics_GotsmanLinial_BinomialMoments
import Definitions.Def_OAI_Combinatorics_GotsmanLinial_ScalarIncrements
import Definitions.Def_OAI_Combinatorics_GotsmanLinial_HilbertSchmidt
import Definitions.Def_OAI_Combinatorics_GotsmanLinial_ProjectionBlocks
import Definitions.Def_OAI_Combinatorics_GotsmanLinial_BlockCoupling
import Definitions.Def_OAI_Combinatorics_GotsmanLinial_Commutator
import Definitions.Def_OAI_Combinatorics_GotsmanLinial_CoordinateMultipliers
import Definitions.Def_OAI_Combinatorics_GotsmanLinial_Walsh
import Definitions.Def_OAI_Combinatorics_GotsmanLinial_PolynomialDegree
import Definitions.Def_OAI_Combinatorics_GotsmanLinial_SignParity
import Definitions.Def_OAI_Combinatorics_GotsmanLinial_EdgeRecovery

namespace OAI

/-!
Dimensions of the Walsh degree filtration, derived from the
linear independence of the concrete characters.
-/

noncomputable section

open scoped BigOperators
open Module

namespace LeanBlast.GotsmanLinial

/-- Count low-degree character indices by partitioning them according to cardinality. -/
theorem card_finset_card_le (n k : ℕ) :
    Fintype.card {S : Finset (Fin n) // S.card ≤ k} =
      ∑ j ∈ Finset.range (k + 1), n.choose j := by
  classical
  let e : {S : Finset (Fin n) // S.card ≤ k} ≃
      (Σ j : Fin (k + 1), {S : Finset (Fin n) // S.card = j.val}) := {
    toFun := fun S => ⟨⟨S.val.card, Nat.lt_succ_of_le S.property⟩, ⟨S.val, rfl⟩⟩
    invFun := fun a => ⟨a.2.val, by
      rw [a.2.property]
      exact Nat.le_of_lt_succ a.1.isLt⟩
    left_inv := fun S => by rfl
    right_inv := fun a => by
      rcases a with ⟨⟨j, hj⟩, ⟨S, hS⟩⟩
      dsimp at hS
      subst j
      rfl
  }
  rw [Fintype.card_congr e, Fintype.card_sigma]
  simp only [Fintype.card_finset_len, Fintype.card_fin]
  exact Fin.sum_univ_eq_sum_range _ _

/-- The dimension of the degree-`k` Fourier subspace is the number of indices of
cardinality at most `k`. This formula remains valid beyond the saturated stage. -/
theorem fourierSpace_finrank (n k : ℕ) :
    finrank ℂ (fourierSpace n k) = ∑ j ∈ Finset.range (k + 1), n.choose j := by
  classical
  rw [fourierSpace, Set.image_eq_range]
  calc
    _ = Fintype.card {S : Finset (Fin n) // S.card ≤ k} := by
      exact finrank_span_eq_card ((walshChar_linearIndependent n).comp
        (Subtype.val : {S : Finset (Fin n) // S.card ≤ k} → Finset (Fin n))
        Subtype.val_injective)
    _ = _ := card_finset_card_le n k

@[simp] theorem fourierSpace_zero_finrank (n : ℕ) :
    finrank ℂ (fourierSpace n 0) = 1 := by
  simp [fourierSpace_finrank]

end LeanBlast.GotsmanLinial

end

end OAI


