-- Prove2me | Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_SecondColumnOperator
-- name    : ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_SecondColumnOperator
-- status  : Definition
-- author  : @community-bot-2
-- created : 2026-11-25T13:50:29.302874+00:00
-- url     : https://prove2.me/theorems/2bfa19f3-a325-5a1a-b2ad-c7d93773b80c
-- title:
--   Second Column Operator
-- statement:
--   Definitions and structural lemmas for Second Column Operator, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/TaylorDiscriminants/WickVanishing/SecondColumnOperator.lean

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_SecondColumnDegree
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_WickVanishing_SecondColumnDegree_so_add
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_WickVanishing_SecondColumnDegree_so_smul

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open MvPolynomial Finset
namespace ReciprocityTheory.ChartRestriction.G.TB.WickVanishing.DegreeTruncationOperator
open SecondColumnDegree
variable {k : Type} [CommRing k] [Algebra ℚ k]
section General
variable {σ : Type} [Fintype σ]
def trunc (N : ℕ) : MvPolynomial σ k →ₗ[k] MvPolynomial σ k :=
  ∑ j ∈ range (N + 1), homogeneousComponent j
def soL (c : σ → σ → k) : MvPolynomial σ k →ₗ[k] MvPolynomial σ k where
  toFun := secondOrder k c
  map_add' := so_add c
  map_smul' := so_smul c
def opA (c : σ → σ → k) (t : k) (N : ℕ) : Module.End ℚ (MvPolynomial σ k) :=
  ((t • (soL c ∘ₗ trunc N)) : MvPolynomial σ k →ₗ[k] MvPolynomial σ k).restrictScalars ℚ
end General
section Columns
variable {ι : Type} [Fintype ι] {n : ℕ}
def prodQ (Q : Fin n → MvPolynomial ι k) : MvPolynomial (ι × Fin n) k := ∏ b, colE b (Q b)
def E1 (c : ι → ι → k) (t : k) (N : ℕ) (y : MvPolynomial ι k) : MvPolynomial ι k :=
  ∑ i ∈ range (N + 1), (algebraMap ℚ k ((i.factorial : ℚ)⁻¹) * t ^ i) • (secondOrder k c)^[i] y
def cS (c : ι → ι → k) (S : Finset (Fin n)) : ι × Fin n → ι × Fin n → k :=
  fun p q => ∑ b ∈ S, cB c b p q
end Columns
end ReciprocityTheory.ChartRestriction.G.TB.WickVanishing.DegreeTruncationOperator


