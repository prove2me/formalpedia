-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_MonomialFrameSpan_BasisMonomialsApply
-- name    : Formalism_PeriodIntegrals_UnitaryGroupMassFormula_MonomialFrameSpan_BasisMonomialsApply
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T23:17:49.496158+00:00
-- url     : https://prove2.me/theorems/4760a3da-df23-49fb-b2a0-d8c8cbf6d519
-- title:
--   Basis Monomials Apply
-- statement:
--   Definitions and structural lemmas for Basis Monomials Apply, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/MonomialFrameSpan/BasisMonomialsApply.lean

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_MonomialFrameSpan_NablaSpanC
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_MonomialFrameSpan_DetSubmatrixFun
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Classical
namespace GenFrameSpan
open CutKW MvPolynomial
section Span
variable {Lt : Type} [Fintype Lt] [DecidableEq Lt] {N0 N1 l : ℕ} [Fact l.Prime]
def atMon (Th : MvPowerSeries (Lt × Fin N0 × Fin N1) ℂ_[l]) (μ : XZ Lt N0 N1 →₀ ℕ) :
    MvPolynomial (Lt × ℕ × Fin N0) ℂ_[l] :=
  monomial (Finsupp.sumFinsuppEquivProdFinsupp μ).1
    (((Finsupp.sumFinsuppEquivProdFinsupp μ).2.prod fun _ n => (n.factorial : ℂ_[l])) *
      MvPowerSeries.coeff (Finsupp.sumFinsuppEquivProdFinsupp μ).2 Th)
def Lj (Th : MvPowerSeries (Lt × Fin N0 × Fin N1) ℂ_[l]) :
    MvPolynomial (XZ Lt N0 N1) ℤ →ₗ[ℤ] MvPolynomial (Lt × ℕ × Fin N0) ℂ_[l] :=
  (basisMonomials (XZ Lt N0 N1) ℤ).constr ℤ (atMon Th)
def Sj (Th : MvPowerSeries (Lt × Fin N0 × Fin N1) ℂ_[l]) :
    MvPolynomial (Lt × Fin N0 × Fin N1) ℤ →ₗ[ℤ] ℂ_[l] :=
  (basisMonomials (Lt × Fin N0 × Fin N1) ℤ).constr ℤ fun β =>
    (β.prod fun _ n => (n.factorial : ℂ_[l])) * MvPowerSeries.coeff β Th
def Xm (s : Lt) (p : ℕ) : Matrix (Fin p) (Fin N0) (MvPolynomial (Lt × ℕ × Fin N0) ℤ) :=
  Matrix.of fun i a => X (s, (i : ℕ), a)
def Dm (s : Lt) (p : ℕ) (f : Fin p → Fin N0) : MvPolynomial (Lt × ℕ × Fin N0) ℤ :=
  ((Xm (N0 := N0) s p).submatrix id f).det
def Zm (s : Lt) (p : ℕ) (I : Fin p ↪o Fin N1) (f : Fin p → Fin N0) :
    MvPolynomial (Lt × Fin N0 × Fin N1) ℤ :=
  ∏ i, X (s, f i, I i)
end Span
end GenFrameSpan


