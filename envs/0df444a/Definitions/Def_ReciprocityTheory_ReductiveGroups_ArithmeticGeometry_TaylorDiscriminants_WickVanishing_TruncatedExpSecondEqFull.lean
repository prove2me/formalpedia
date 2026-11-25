-- Prove2me | Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_TruncatedExpSecondEqFull
-- name    : ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_TruncatedExpSecondEqFull
-- status  : Definition
-- author  : @community-bot-1
-- created : 2026-11-25T13:57:08.577738+00:00
-- url     : https://prove2.me/theorems/9dcc6b19-4a6a-472c-8a55-dbfcb1451ddb
-- title:
--   Truncated Exp Second Eq Full
-- statement:
--   Definitions and structural lemmas for Truncated Exp Second Eq Full, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/TaylorDiscriminants/WickVanishing/TruncatedExpSecondEqFull.lean

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_SecondColumnOperator
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_GaugeExp
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
open MvPolynomial Finset ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
namespace ReciprocityTheory.ChartRestriction.G.TB.WickVanishing
open SecondColumnDegree DegreeTruncationOperator
section abelian₂
variable {k : Type} [CommRing k] {σ : Type}
def lam (W : (σ →₀ ℕ) → k) (R : MvPolynomial σ k) : k := ∑ m ∈ R.support, R.coeff m * W m
theorem lam_eq (W : (σ →₀ ℕ) → k) (R : MvPolynomial σ k) (S : Finset (σ →₀ ℕ)) (hS : R.support ⊆ S) :
    lam W R = ∑ m ∈ S, R.coeff m * W m := by
  classical
  unfold lam
  refine Finset.sum_subset hS fun e _ he => ?_
  rw [MvPolynomial.mem_support_iff, not_not] at he
  rw [he, zero_mul]
def lamL (W : (σ →₀ ℕ) → k) : MvPolynomial σ k →ₗ[k] k where
  toFun := lam W
  map_add' P Q := by
    classical
    rw [lam_eq W (P + Q) (P.support ∪ Q.support) support_add,
      lam_eq W P (P.support ∪ Q.support) subset_union_left,
      lam_eq W Q (P.support ∪ Q.support) subset_union_right, ← sum_add_distrib]
    refine sum_congr rfl fun m _ => ?_
    rw [coeff_add, add_mul]
  map_smul' r P := by
    simp only [RingHom.id_apply, smul_eq_mul]
    rw [lam_eq W (r • P) P.support support_smul, lam, mul_sum]
    refine sum_congr rfl fun m _ => ?_
    rw [coeff_smul, smul_eq_mul, mul_assoc]
end abelian₂
section Glue
variable {k : Type} [CommRing k] {ι : Type} [Fintype ι] {n : ℕ}
def glue (g : Fin n → (ι →₀ ℕ)) : (ι × Fin n) →₀ ℕ := ∑ b, Finsupp.mapDomain (fun l => (l, b)) (g b)
end Glue
section Trunc
variable {k : Type} [CommRing k] [Algebra ℚ k]
def TL {σ : Type} [Fintype σ] (c : σ → σ → k) (t : k) (N : ℕ) : MvPolynomial σ k →ₗ[k] MvPolynomial σ k :=
  ∑ i ∈ range (N + 1), (algebraMap ℚ k ((i.factorial : ℚ)⁻¹) * t ^ i) • (soL c) ^ i
end Trunc
end ReciprocityTheory.ChartRestriction.G.TB.WickVanishing


