-- Prove2me | Definitions.Def_QEC_Coding_ExpanderCodes_LPSCuspHorocycle
-- name    : QEC_Coding_ExpanderCodes_LPSCuspHorocycle
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-06T09:14:58.197172+00:00
-- url     : https://prove2.me/theorems/562c39b9-5b9f-4337-a38c-48d0490877ba
-- title:
--   LPSCusp Horocycle
-- statement:
--   Definitions and structural lemmas for LPSCusp Horocycle, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSCuspHorocycle.lean

import Mathlib.Analysis.Fourier.AddCircle
import Mathlib.NumberTheory.ModularForms.Bounds
set_option autoImplicit false
namespace QEC.Coding.TannerLiftedProduct
open Complex Filter Topology MeasureTheory Asymptotics
open scoped MatrixGroups UpperHalfPlane ModularForm
noncomputable def lpsHorocyclePoint (y : ℝ) (hy : 0<y) (x : ℝ) : ℍ :=
  ⟨⟨x,y⟩,hy⟩
noncomputable def lpsCuspHorocycleTerm (N : ℕ)
    (f : CuspForm (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)) 2)
    (y : ℝ) (n : ℕ) (x : AddCircle (1:ℝ)) : ℂ :=
  PowerSeries.coeff n (UpperHalfPlane.qExpansion 1 f)*
    ((Real.exp (-2*Real.pi*y):ℂ)^n)*fourier (n:ℤ) x
noncomputable def lpsCuspHorocycleCircle (N : ℕ)
    (f : CuspForm (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)) 2)
    (y : ℝ) (x : AddCircle (1:ℝ)) : ℂ := ∑' n : ℕ,lpsCuspHorocycleTerm N f y n x
end QEC.Coding.TannerLiftedProduct


