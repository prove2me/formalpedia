-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_IsCoeffFieldOfCoeff
-- name    : Development_AbelianVarietyTheory_Proofs_ModuliProofs_IsCoeffFieldOfCoeff
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T15:42:54.029909+00:00
-- url     : https://prove2.me/theorems/c638f869-0222-4073-b2be-e2463bda873a
-- title:
--   Is Coeff Field Of Coeff
-- statement:
--   Definitions and structural lemmas for Is Coeff Field Of Coeff, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/IsCoeffFieldOfCoeff.lean

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_PushInvertible
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_CMModuli_CoefficientFieldBaseChange
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
namespace GlobalTheory.ModuliCompare
open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G.Geo
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Tor.Host E}
theorem dim_eq (D : Tor.Datum H) : D.dim = IndefiniteRowSideFullHecke.CoefficientFieldBaseChange.dimD D := by
  have h2 : Module.finrank (maximalRealSubfield E) E = 2 := Algebra.IsQuadraticExtension.finrank_eq_two _ _
  have h := Module.finrank_mul_finrank ℚ (maximalRealSubfield E) E
  rw [h2] at h
  unfold Tor.Datum.dim IndefiniteRowSideFullHecke.CoefficientFieldBaseChange.dimD
  rw [← h, Nat.mul_div_cancel _ two_pos]
variable {D : Tor.Datum H} {l : Tor.Level H}
theorem isModuli_of_moduli (Xo : Tor.Moduli D l) : IndefiniteRowSideFullHecke.CoefficientFieldBaseChange.IsModuli D l Xo.s Xo.univ where
  smooth := dim_eq D ▸ Xo.smooth
  qproj := Xo.qproj
  repr S hS s o := Xo.rep S s hS o
  rigid := Xo.unram
def moduliOfIsModuli {X : Scheme.{0}} {str : X ⟶ Tor.Sp (IndefiniteRowSideFullHecke.CoefficientFieldBaseChange.KA l)}
    {univ : Tor.Obj D l (IndefiniteRowSideFullHecke.CoefficientFieldBaseChange.baseKA l) str} (h : IndefiniteRowSideFullHecke.CoefficientFieldBaseChange.IsModuli D l str univ) : Tor.Moduli D l where
  X := X
  s := str
  qproj := h.qproj
  smooth := (dim_eq D).symm ▸ h.smooth
  univ := univ
  rep S s hS o := @IndefiniteRowSideFullHecke.CoefficientFieldBaseChange.IsModuli.repr _ _ _ _ _ _ _ _ _ _ h S hS s o
  unram := h.rigid
def moduliEquiv (D : Tor.Datum H) (l : Tor.Level H) :
    Tor.Moduli D l ≃
      {p : Σ (X : Scheme.{0}) (str : X ⟶ Tor.Sp (IndefiniteRowSideFullHecke.CoefficientFieldBaseChange.KA l)), Tor.Obj D l (IndefiniteRowSideFullHecke.CoefficientFieldBaseChange.baseKA l) str //
        IndefiniteRowSideFullHecke.CoefficientFieldBaseChange.IsModuli D l p.2.1 p.2.2} where
  toFun Xo := ⟨⟨Xo.X, Xo.s, Xo.univ⟩, isModuli_of_moduli Xo⟩
  invFun p := moduliOfIsModuli p.2
  left_inv _ := rfl
  right_inv _ := rfl
theorem isCoeffField_of_coeff (c : Tor.Coeff l) : IndefiniteRowSideFullHecke.CoefficientFieldBaseChange.IsCoeffField l c.F where
  fin := c.fin
  conj := c.conj
  root := c.zeta_mem
def coeffOfIsCoeffField {F₀ : IntermediateField ℚ ℂ} (h : IndefiniteRowSideFullHecke.CoefficientFieldBaseChange.IsCoeffField l F₀) : Tor.Coeff l where
  F := F₀
  fin := h.fin
  conj := h.conj
  zeta_mem := h.root
  le := h.KA_le
def coeffEquiv (l : Tor.Level H) : Tor.Coeff l ≃ {F₀ : IntermediateField ℚ ℂ // IndefiniteRowSideFullHecke.CoefficientFieldBaseChange.IsCoeffField l F₀} where
  toFun c := ⟨c.F, isCoeffField_of_coeff c⟩
  invFun F := coeffOfIsCoeffField F.2
  left_inv _ := rfl
  right_inv _ := rfl
end GlobalTheory.ModuliCompare


