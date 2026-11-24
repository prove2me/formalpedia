-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_HasSumSphericalFunctionDoublingLength
-- name    : Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_HasSumSphericalFunctionDoublingLength
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T23:16:27.432946+00:00
-- url     : https://prove2.me/theorems/a86cebe4-06b7-4bcc-9040-33042d98fec6
-- title:
--   Has Sum Spherical Function Doubling Length
-- statement:
--   Definitions and structural lemmas for Has Sum Spherical Function Doubling Length, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DecoratedLatticeProofs/HasSumSphericalFunctionDoublingLength.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_PublishedTheorems_TwistedTraceFormula_PairwiseDisjointCell
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_HasBoundedSumsOne
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_HasSumHeckeSeriesSphericalIntegralInverseStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_HasSumHeckeSeriesSphericalEigenfunctionStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_HeckeSeriesCellHasSumStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory ValuativeRel GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.SatakeBound GlobalTheory.GLDoubling
noncomputable section
namespace GlobalTheory.DoublingLength
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {n : ℕ}
variable (k n) in

def pairEquiv : ((GL (Fin n) k ⧸ KO k (Fin n)) × (GL (Fin n) k ⧸ KO k (Fin n))) ≃
    ((GL (Fin n) k ⧸ KO k (Fin n)) × (GL (Fin n) k ⧸ KO k (Fin n))) where
  toFun p := (p.2, (QuotientGroup.mk (p.2.out⁻¹ * p.1.out) : GL (Fin n) k ⧸ KO k (Fin n)))
  invFun p := ((QuotientGroup.mk (p.1.out * p.2.out) : GL (Fin n) k ⧸ KO k (Fin n)), p.1)
  left_inv p := by
    obtain ⟨x, hx⟩ := QuotientGroup.mk_out_eq_mul (KO k (Fin n)) (p.2.out⁻¹ * p.1.out)
    refine Prod.ext ?_ rfl
    show (QuotientGroup.mk (p.2.out * (QuotientGroup.mk (p.2.out⁻¹ * p.1.out) : GL (Fin n) k ⧸ KO k (Fin n)).out) : GL (Fin n) k ⧸ KO k (Fin n)) = p.1
    rw [hx, mul_assoc, mul_inv_cancel_left, QuotientGroup.mk_mul_of_mem _ x.2, QuotientGroup.out_eq']
  right_inv p := by
    obtain ⟨x, hx⟩ := QuotientGroup.mk_out_eq_mul (KO k (Fin n)) (p.1.out * p.2.out)
    refine Prod.ext rfl ?_
    show (QuotientGroup.mk (p.1.out⁻¹ * (QuotientGroup.mk (p.1.out * p.2.out) : GL (Fin n) k ⧸ KO k (Fin n)).out) : GL (Fin n) k ⧸ KO k (Fin n)) = p.2
    rw [hx, mul_assoc, inv_mul_cancel_left, QuotientGroup.mk_mul_of_mem _ x.2, QuotientGroup.out_eq']
open scoped Classical in

def pairTerm (X : ℂ) (φ : GL (Fin n) k → ℂ)
    (p : (GL (Fin n) k ⧸ KO k (Fin n)) × (GL (Fin n) k ⧸ KO k (Fin n))) : ℂ :=
  if (∀ i j, (p.1.out⁻¹ : GL (Fin n) k).1 i j ∈ 𝒪[k]) ∧ (∀ i j, (p.2.out : GL (Fin n) k).1 i j ∈ 𝒪[k]) then
    X ^ ((-ord k (Matrix.GeneralLinearGroup.det p.1.out)).toNat +
      (ord k (Matrix.GeneralLinearGroup.det p.2.out)).toNat) * φ (p.1.out * p.2.out)
  else 0
end GlobalTheory.DoublingLength


