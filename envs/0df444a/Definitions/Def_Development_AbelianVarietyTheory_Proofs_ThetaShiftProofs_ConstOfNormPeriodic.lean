-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_ConstOfNormPeriodic
-- name    : Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_ConstOfNormPeriodic
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T12:29:53.750797+00:00
-- url     : https://prove2.me/theorems/46c1e80f-ef83-4640-897e-ec5e455fb00a
-- title:
--   Const Of Norm Periodic
-- statement:
--   Definitions and structural lemmas for Const Of Norm Periodic, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaShiftProofs/ConstOfNormPeriodic.lean

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HasArcDataIff
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ThetaUnifAV
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ValCalc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_RosatiAdj
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_EntireApplyEqOfPeriodicOfSpanReal
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CubicalLineBundles_SemicharacterSqEqOneOfSymmetric
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CubicalLineBundles_EqZeroOfSumEmbeddingMul
import Theorems.Thm_GlobalTheory_SymmetricSemicharacter_exists_chart
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_exists_chart

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
noncomputable section
namespace GlobalTheory.FrameValue
open CubeValues SymmetricSemicharacter EigenNorm
section Calculus
def chartAt {X : Scheme.{0}} {L : LB X} (hL : L.IsLB) (x : Sp ℂ ⟶ X) : L.ι :=
  (ReciprocityTheory.ChartRestriction.G.Geo.Tor.exists_chart hL (x (default : PrimeSpectrum ℂ))).choose
variable {A : Over (Sp ℂ)} [GrpObj A] {L : LB A.left} {g : ℕ} (u : HolUnif A L g)
  {Y Y' : Scheme.{0}} {K K' : Type} [Fintype K] [Fintype K']
  {φ : K → (Y ⟶ A.left)} {ε : K → ℤ} {φ' : K' → (Y ⟶ A.left)} {ε' : K' → ℤ}
def IsLift (φ : K → (Y ⟶ A.left)) (y : Sp ℂ ⟶ Y) (z : K → Fin g → ℂ) : Prop :=
  ∀ k, y ≫ φ k = (u.ex (z k)).left
def frameProd (ε : K → ℤ) (z : K → Fin g → ℂ) (j : K → L.ι) : ℂ := ∏ k, u.fr (j k) (z k) ^ ε k
def secValIn (s : LB.Sec (LB.LinComb L φ ε)) (y : Sp ℂ ⟶ Y) (z : K → Fin g → ℂ) (j : K → L.ι) : ℂ :=
  valAt' y (L.wchart φ j) (s.f j) / frameProd u ε z j
def genValIn (t : LB.Gen (LB.LinComb L φ ε)) (y : Sp ℂ ⟶ Y) (z : K → Fin g → ℂ) (j : K → L.ι) : ℂ :=
  valAt' y (L.wchart φ j) (t.s j).val / frameProd u ε z j
def secVal (hL : L.IsLB) (s : LB.Sec (LB.LinComb L φ ε)) (y : Sp ℂ ⟶ Y) (z : K → Fin g → ℂ) : ℂ :=
  secValIn u s y z (fun k => chartAt hL (y ≫ φ k))
def genVal (hL : L.IsLB) (t : LB.Gen (LB.LinComb L φ ε)) (y : Sp ℂ ⟶ Y) (z : K → Fin g → ℂ) : ℂ :=
  genValIn u t y z (fun k => chartAt hL (y ≫ φ k))
variable {u}
def ahFactor (Hm : Matrix (Fin g) (Fin g) ℂ) (χ : u.Λ → ℂ) (l : u.Λ) (z : Fin g → ℂ) : ℂ :=
  χ l * Complex.exp (Real.pi * hermForm Hm z l + Real.pi / 2 * hermForm Hm l l)
variable {Hm : Matrix (Fin g) (Fin g) ℂ} {χ : u.Λ → ℂ}
end Calculus
section Main
variable {A : Over (Sp ℂ)} [GrpObj A] {L : LB A.left} {g : ℕ} {u : HolUnif A L g}
  {Hm : Matrix (Fin g) (Fin g) ℂ} {χ : u.Λ → ℂ}
def cubeLift (x : Fin 3 → Fin g → ℂ) : thK → Fin g → ℂ := fun I => ∑ a ∈ I.down, x a
variable [IsCommMonObj A] {f f' : A ⟶ A} {F G : (Fin g → ℂ) →ₗ[ℂ] (Fin g → ℂ)}
def rosatiLift (F G : (Fin g → ℂ) →ₗ[ℂ] (Fin g → ℂ)) (x z : Fin g → ℂ) : Fin 6 → Fin g → ℂ :=
  ![F x + z, F x, z, x + G z, x, G z]
end Main
end GlobalTheory.FrameValue


