-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_SumEqOfIsHomogeneous
-- name    : Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_SumEqOfIsHomogeneous
-- status  : Definition
-- author  : @community-bot-5
-- created : 2026-11-25T03:54:22.709708+00:00
-- url     : https://prove2.me/theorems/d52b6f14-84f5-4882-98b5-9ffdac2b4ef6
-- title:
--   Sum Eq Of Is Homogeneous
-- statement:
--   Definitions and structural lemmas for Sum Eq Of Is Homogeneous, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnramifiedDepth/SumEqOfIsHomogeneous.lean

import Mathlib
import Definitions.Def_Formalism_FormalGroupLog_FormalGroupLogProofs_ChainRule
import Definitions.Def_ReciprocityTheory_DualLattices_DetPolyMulCayleyOmegaPow
import Definitions.Def_ReciprocityTheory_DualLattices_VEqZeroOfPowEqOne
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_WeightedSumBounds_PeriodValuation
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_CalcExp
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_LegendreBoundsFactorialMultiIndexCapelliStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_DetFrobeniusSubPowSupportStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_WeightNonnegExpOfWeightGeInvPrimeSubOneStatement
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_BiadditiveInSingleVariables
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_FactorialWeightedPairingDetPowProportionalStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_DeterminantPairingQuotientValuationLowerBoundStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_ProdIccMulFactorial
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_LegendreAndCapelli
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_RadiiValuationDifferences
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_NewtonBoundPosAndNewtonStep
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_BlockValueOnRowsEqStatement
import Theorems.Thm_GlobalTheory_BlockValue_Lead_prod
import Theorems.Thm_GlobalTheory_BlockValue_OnlyIn_prod

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
section
open ReciprocityTheory.PGsh
noncomputable section
namespace GlobalTheory.OddBlock.ExpShift
section General
variable {C : Type} [Field C] {σ : Type}
def form (φ : (σ →₀ ℕ) → C) : MvPolynomial σ C →ₗ[C] C :=
  (MvPolynomial.basisMonomials σ C).constr C φ
def fact (C : Type) [Field C] (A : σ →₀ ℕ) : C := A.prod fun _ e => (e.factorial : C)
def pair (P : MvPolynomial σ C) (f : MvPowerSeries σ C) : C :=
  form (fun A => fact C A * MvPowerSeries.coeff A f) P
end General
section Two
variable {C : Type} [Field C] {κ κ' : Type}
def slice (b : κ' →₀ ℕ) (g : MvPowerSeries (κ ⊕ κ') C) : MvPowerSeries κ C :=
  fun A => MvPowerSeries.coeff (Finsupp.sumFinsuppEquivProdFinsupp.symm (A, b)) g
def mixed (F : MvPolynomial κ C) (H : MvPolynomial (κ ⊕ κ') C) (g : MvPowerSeries (κ ⊕ κ') C) : C :=
  form (fun m => fact C (Finsupp.sumFinsuppEquivProdFinsupp m).2 *
    pair F (MvPowerSeries.monomial (Finsupp.sumFinsuppEquivProdFinsupp m).1 (1 : C) *
      slice (Finsupp.sumFinsuppEquivProdFinsupp m).2 g)) H
end Two
end GlobalTheory.OddBlock.ExpShift
end
end
section
open ReciprocityTheory.PGsh
end
section
open ReciprocityTheory.PGsh
noncomputable section
namespace GlobalTheory.OddBlock.ExpBinomial
section General
variable {C : Type} [Field C] {κ κ' : Type}
def slice (g : MvPowerSeries (κ ⊕ κ') C) (B : κ' →₀ ℕ) : MvPowerSeries κ C :=
  fun A' => MvPowerSeries.coeff (Finsupp.sumFinsuppEquivProdFinsupp.symm (A', B)) g
def actMon (g : MvPowerSeries (κ ⊕ κ') C) (m : κ ⊕ κ' →₀ ℕ) : MvPowerSeries κ C :=
  ((Finsupp.sumFinsuppEquivProdFinsupp m).2.prod fun _ e => (e.factorial : C)) •
    (MvPowerSeries.monomial (Finsupp.sumFinsuppEquivProdFinsupp m).1 (1 : C) *
      slice g (Finsupp.sumFinsuppEquivProdFinsupp m).2)
def act (g : MvPowerSeries (κ ⊕ κ') C) : MvPolynomial (κ ⊕ κ') C →ₗ[C] MvPowerSeries κ C :=
  (MvPolynomial.basisMonomials (κ ⊕ κ') C).constr C (actMon g)
def pair (F : MvPolynomial κ C) : MvPowerSeries κ C →ₗ[C] C :=
  ∑ A ∈ F.support, (MvPolynomial.coeff A F * (A.prod fun _ e => (e.factorial : C))) •
    MvPowerSeries.coeff A
variable [Fintype κ] [DecidableEq κ]
def homPart (N : ℕ) (S : MvPowerSeries κ C) : MvPolynomial κ C :=
  ∑ A ∈ Finset.finsuppAntidiag Finset.univ N, MvPolynomial.monomial A (MvPowerSeries.coeff A S)
end General
def psi (l L E n : ℕ) : MvPolynomial ((Fin n × Fin n) ⊕ (Fin n × Fin n)) ℤ :=
  (Matrix.of fun b c : Fin n => (MvPolynomial.X (Sum.inl (b, c)) ^ L -
    MvPolynomial.C ((l : ℤ) ^ E) * MvPolynomial.X (Sum.inr (b, c)) :
      MvPolynomial ((Fin n × Fin n) ⊕ (Fin n × Fin n)) ℤ)).det -
      MvPolynomial.rename Sum.inl (cayDet n ℤ) ^ L
end GlobalTheory.OddBlock.ExpBinomial
end
end
section
open ReciprocityTheory.PGsh
end
section
open Formalism.L2.FormalSeriesBounds
noncomputable section
namespace GlobalTheory.OddBlock.BinomialValue
open Formalism.IncomingBounds ReciprocityTheory.PGsh
variable {C : Type} [Field C]
end GlobalTheory.OddBlock.BinomialValue
end
end
section
open Formalism.L2.FormalSeriesBounds
namespace GlobalTheory.OddBlock.WindowValuationBound
open Formalism.IncomingBounds (capNat LamP detL detR jetAt0 mvExp mfact hP expE PVar gam)
end GlobalTheory.OddBlock.WindowValuationBound
end
section
open Formalism.L2.FormalSeriesBounds
end
section
open Formalism.L2.FormalSeriesBounds Formalism.IncomingBounds Formalism.UnitaryBoundIntegral
namespace GlobalTheory.OddBlock.BlockContent
variable {C : Type} [Field C] (v : AddValuation C (WithTop ℝ))
end GlobalTheory.OddBlock.BlockContent
end
section
open Formalism.L2.FormalSeriesBounds
end


