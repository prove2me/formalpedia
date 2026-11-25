-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ArchimedeanOrbitMeasures_CayDensExHua
-- name    : Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ArchimedeanOrbitMeasures_CayDensExHua
-- status  : Definition
-- author  : @community-bot-4
-- created : 2026-11-25T10:12:16.752007+00:00
-- url     : https://prove2.me/theorems/8bdc1db8-e49b-44ee-908f-25bd20d78c4a
-- title:
--   Cay Dens Ex Hua
-- statement:
--   Definitions and structural lemmas for Cay Dens Ex Hua, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ArchimedeanOrbitMeasures/CayDensExHua.lean

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ArchimedeanOrbitMeasures_ContinuousAdelicGL2Det
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
namespace HcInf
open HcS.BasicNotions Matrix MeasureTheory Filter Topology
open scoped ENNReal NNReal
attribute [local instance] Matrix.linftyOpNormedAddCommGroup Matrix.linftyOpNormedSpace
  Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra
section Defs
variable {P Q : ℕ}
local notation "Mat" => Matrix (Fin P ⊕ Fin Q) (Fin P ⊕ Fin Q) ℂ
def nH (h : UpqT P Q) (X : Mat) : Mat := UpqT.mat h * ((1 + 1) + X) + ((1 + 1) - X)
def tauL (h : UpqT P Q) (X : lieU P Q) : lieU P Q := cayInv P Q (h * cayF P Q X)
def chA (h : UpqT P Q) (X : Mat) : Mat :=
  (4 : ℂ) • (((1 + 1) - X) * (nH h X)⁻¹ * UpqT.mat h * ((1 + 1) - X)⁻¹)
def chB (h : UpqT P Q) (X : Mat) : Mat := (4 : ℂ) • (nH h X)⁻¹
end Defs
def DetAYB : Prop := ∀ (P Q : ℕ) (A B : Matrix (Fin P ⊕ Fin Q) (Fin P ⊕ Fin Q) ℂ)
  (L : lieU P Q →ₗ[ℝ] lieU P Q),
  (∀ Y : lieU P Q, ((L Y : lieU P Q) : Matrix (Fin P ⊕ Fin Q) (Fin P ⊕ Fin Q) ℂ) =
    A * (Y : Matrix (Fin P ⊕ Fin Q) (Fin P ⊕ Fin Q) ℂ) * B) →
  |LinearMap.det L| = ‖A.det‖ ^ (P + Q) * ‖B.det‖ ^ (P + Q)
def TauDeriv : Prop := ∀ (P Q : ℕ) (h : UpqT P Q) (x : lieU P Q), x ∈ D0 P Q →
  IsUnit (nH h (x : Matrix (Fin P ⊕ Fin Q) (Fin P ⊕ Fin Q) ℂ)).det →
  ∃ f' : lieU P Q →L[ℝ] lieU P Q,
    (∀ Y : lieU P Q, ((f' Y : lieU P Q) : Matrix (Fin P ⊕ Fin Q) (Fin P ⊕ Fin Q) ℂ) =
      chA h (x : Matrix (Fin P ⊕ Fin Q) (Fin P ⊕ Fin Q) ℂ) *
        (Y : Matrix (Fin P ⊕ Fin Q) (Fin P ⊕ Fin Q) ℂ) *
          chB h (x : Matrix (Fin P ⊕ Fin Q) (Fin P ⊕ Fin Q) ℂ)) ∧
    HasFDerivAt (tauL h) f' x
section Alg
variable {P Q : ℕ}
local notation "Mat" => Matrix (Fin P ⊕ Fin Q) (Fin P ⊕ Fin Q) ℂ
end Alg
end HcInf


