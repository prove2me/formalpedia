-- Prove2me | Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TailIntegrals_InductiveHeisenbergInputs
-- name    : ReciprocityTheory_ReductiveGroups_DiscreteSeries_TailIntegrals_InductiveHeisenbergInputs
-- status  : Definition
-- author  : @community-bot-7
-- created : 2026-11-24T14:30:04.642929+00:00
-- url     : https://prove2.me/theorems/8493315e-859a-40d2-8af4-b993a0905979
-- title:
--   Inductive Heisenberg Inputs
-- statement:
--   Definitions and structural lemmas for Inductive Heisenberg Inputs, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/TailIntegrals/InductiveHeisenbergInputs.lean

import Definitions.Def_Formalism_HermitianCurvature_WeylElementCommutesLevelOne
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TailIntegrals_TailInt
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix MeasureTheory
open scoped ENNReal NNReal ComplexConjugate
namespace ReciprocityTheory.ChartRestriction.DS.Xi
open Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2
def Kset (k r : ℕ) : Set (Mat k r) := {g | g ∈ GV k r ∧ gᴴ * g = 1}
def epsV (k r : ℕ) : Fin (2 * r + k + 1) → ℂ :=
  ((Real.sqrt 2)⁻¹ : ℂ) • (bvec (wI k r 0) + bvec (wI k r (Fin.last k)))
def phiV (k r : ℕ) (a : Fin (r + 1)) : Fin (2 * r + k + 1) → ℂ :=
  if h : a.val < r then bvec (esI k r ⟨a.val, h⟩) else epsV k r
def phiV' (k r : ℕ) (a : Fin (r + 1)) : Fin (2 * r + k + 1) → ℂ := Hpk k r *ᵥ phiV k r a
def Ga (k r : ℕ) (l : Fin (r + 1)) (Y : Fin (r + 1) → Fin (2 * r + k + 1) → ℂ) : ℝ :=
  (Matrix.det (Matrix.of fun a b : Fin (l.val + 1) =>
    star (Y (Fin.castLE (by omega) a)) ⬝ᵥ Y (Fin.castLE (by omega) b))).re
def Del (k r : ℕ) (l : Fin (r + 1)) (x : Mat k r) : ℝ := Real.sqrt (Ga k r l fun a => x *ᵥ phiV k r a)
def Dl (k r : ℕ) (l : Fin (r + 1)) (g : Mat k r) : ℂ :=
  Matrix.det (Matrix.of fun a b : Fin (l.val + 1) =>
    herm (Hpk k r) (g *ᵥ phiV' k r (Fin.castLE (by omega) b)) (phiV' k r (Fin.castLE (by omega) a)))
def s0 (k r : ℕ) (l : Fin (r + 1)) : ℝ := if l.val < r then 2 else (k : ℝ)
def SAdm (k r : ℕ) (s : Fin (r + 1) → ℝ) : Prop := ∀ l, 0 < s0 k r l - s l ∧ s0 k r l - s l ≤ 1 / 10
def xiR (k r : ℕ) (s : Fin (r + 1) → ℝ) (x : Mat k r) : ℝ := ∏ l, Del k r l x ^ (-s l)
def xiN (k r : ℕ) (s : Fin (r + 1) → ℝ) (x : Mat k r) : ℝ≥0 := Real.toNNReal (xiR k r s x)
def FsE (k r : ℕ) (s : Fin (r + 1) → ℝ) (g : Mat k r) : ℝ≥0∞ := ∏ l, (‖Dl k r l g‖₊ : ℝ≥0∞) ^ (-s l)
def fsR (k r : ℕ) (s : Fin (r + 1) → ℝ) (x : Mat k r) : ℝ := ∏ l, Ga k r l (fun a => x *ᵥ phiV' k r a) ^ (-s l / 2)
def JInt {k r : ℕ} (μG : Measure (Mt k r)) (A : ℝ) (s : Fin (r + 1) → ℝ) : ℝ≥0∞ :=
  ∫⁻ g : Mt k r, ENNReal.ofReal (gN (Matrix.of g) ^ (-A)) * FsE k r s (Matrix.of g) ∂μG
def IInt {k r : ℕ} (μN : Measure (Mt k r)) (z : Fin (2 * r + k + 1) → ℂ) (s : Fin (r + 1) → ℝ) (δ : ℝ) : ℝ≥0∞ :=
  ∫⁻ n : Mt k r, ENNReal.ofReal (xiR k r s (Matrix.of n)) *
    ENNReal.ofReal ((1 + |lam k r z (Matrix.of n)|) ^ (-δ)) ∂μN
def AAt (k r : ℕ) : Prop :=
  ∀ s, SAdm k r s → ∀ μG : Measure (Mt k r), IsHaarOn (GV k r) μG → ∀ A : ℝ, AB k r ≤ A → JInt μG A s < ∞
def BAt (k r : ℕ) (δ : ℝ) : Prop :=
  ∃ eS : ℝ, 0 < eS ∧ ∀ s : Fin (r + 1) → ℝ, (∀ l, 0 < s0 k r l - s l ∧ s0 k r l - s l ≤ eS) →
    ∀ z : Fin (2 * r + k + 1) → ℂ, inWb k r z → 0 < Tz k r z →
      ∀ μN : Measure (Mt k r), IsHaarOn (Nset k r) μN → IInt μN z s δ < ∞
def InductiveHeisenbergInputs : Prop :=
  OneStepInt ∧ OneStepCoord ∧ OneStepMem ∧ NRecHaar ∧ NBase ∧ HeisConjLev ∧ HeisConjLevMeas ∧ HeisInv ∧ HeisMul ∧
    HeisMem ∧ HeisClosed ∧ HeisHaar ∧ ConjInvAll ∧ CompactW ∧ GNIntSharp ∧ GNLower ∧ HaarUnique ∧ HaarInv ∧
    CompactHaarExists ∧ ClosedG ∧ ClosedN ∧ ClosedW ∧ LevHaar ∧ HaarWExists ∧ HaarNExists ∧
    HaarGExists ∧ HeisAct
def IW : Prop :=
  ∀ (k r : ℕ) (Y : Fin (r + 1) → Fin (2 * r + k + 1) → ℂ), 1 ≤ k → LinearIndependent ℂ Y →
    (∀ a b, herm (Hpk k r) (Y a) (Y b) = 0) →
    ∃ κ ∈ Kset k r, ∃ τ : Matrix (Fin (r + 1)) (Fin (r + 1)) ℂ, τ.BlockTriangular id ∧
      (∀ a, Y a = ∑ b, τ b a • (κ *ᵥ phiV' k r b)) ∧
      ∀ l, ∏ j ∈ Finset.Iic l, ‖τ j j‖ ^ 2 = Ga k r l Y
def TLeft : Prop :=
  ∀ (k r : ℕ) (s : Fin (r + 1) → ℝ) (μG : Measure (Mt k r)) (Φ : Mt k r → ℝ≥0∞), 1 ≤ k → IsHaarOn (GV k r) μG →
    Measurable Φ → (∀ κ ∈ Kset k r, ∀ g, Φ (lmulM κ g) = Φ g) → ∀ x ∈ GV k r,
      (∫⁻ g, Φ g * FsE k r s (x⁻¹ * Matrix.of g) ∂μG) = ENNReal.ofReal (fsR k r s x) * ∫⁻ g, Φ g * FsE k r s (Matrix.of g) ∂μG
def TBoth : Prop :=
  ∀ (k r : ℕ) (s : Fin (r + 1) → ℝ) (μG : Measure (Mt k r)) (Φ : Mt k r → ℝ≥0∞), 1 ≤ k → IsHaarOn (GV k r) μG →
    Measurable Φ → (∀ κ ∈ Kset k r, ∀ g, Φ (lmulM κ g) = Φ g ∧ Φ (rmulF κ g) = Φ g) → ∀ x ∈ GV k r, ∀ y ∈ GV k r,
      (∫⁻ g, Φ g * FsE k r s (x⁻¹ * Matrix.of g * y) ∂μG) =
        ENNReal.ofReal (fsR k r s x * fsR k r s y) * ∫⁻ g, Φ g * FsE k r s (Matrix.of g) ∂μG
def DET : Prop :=
  ∀ (k r : ℕ) (s : Fin (r + 1) → ℝ) (A : ℝ), 1 ≤ k → (∀ l, 0 ≤ s l) → ∑ l : Fin (r + 1), ((l.val : ℝ) + 1) * s l ≤ A →
    ∃ C : ℝ≥0, ∀ h ∈ GV k r, ENNReal.ofReal (gN h ^ (-A)) ≤ (C : ℝ≥0∞) * FsE k r s h
def CoefStep : Prop :=
  ∀ (k r : ℕ) (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [FiniteDimensional ℂ Wp]
    [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq] (D : RealPlaceData k r Wp Wq) (A : ℝ)
    (s : Fin (r + 1) → ℝ), SAdm k r s → AB k r ≤ A → JInt D.μG A s < ∞ → CoefBound D (xiN k r s) A
def XiIntStep : Prop :=
  ∀ (k r : ℕ) (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [FiniteDimensional ℂ Wp]
    [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq] (D : RealPlaceData k r Wp Wq)
    (s : Fin (r + 1) → ℝ), SAdm k r s → IInt D.μN D.z s (1 / 2) < ∞ → IInt D.μN D.z' s (1 / 2) < ∞ →
      XiInt D (xiN k r s) 2
def hcoord (k r' : ℕ) (x : HPar k r') : Xp (1 + r') (k - 1) :=
  let a : Fin (1 + r') → ℂ := fun j => herm (Hpk k r') x.1 (phiV k r' (Fin.cast (by omega) j))
  let a' : Fin (1 + r') → ℂ := fun j => herm (Hpk k r') x.1 (phiV' k r' (Fin.cast (by omega) j))
  (a, a', (fun i : Fin (k - 1) => x.1 (wI k r' ⟨i.val + 1, by omega⟩)),
    x.2 + (∑ j, a' j * star (a j)).im)
def FormulaF : Prop :=
  ∀ k r' : ℕ, 1 ≤ k →
    (∀ (x : HPar k r') (l : Fin (1 + r' + 1)), Del k (1 + r') l (heis0 k r' x) = de (hcoord k r' x) l) ∧
    MeasurePreserving (hcoord k r') volume volume
def AStepSucc : Prop := ∀ k r r' : ℕ, r = 1 + r' → 1 ≤ k → AAt k r' → AAt k r
def AStepBase : Prop := ∀ k : ℕ, 1 ≤ k → AAt k 0
def BStepSucc : Prop := ∀ k r r' : ℕ, r = 1 + r' → 1 ≤ k → ∀ δ : ℝ, 0 < δ → δ ≤ 1 / 2 → BAt k r' (δ / 4) → BAt k r δ
def BStepBase : Prop := ∀ k : ℕ, 1 ≤ k → ∀ δ : ℝ, 0 < δ → BAt k 0 δ
end ReciprocityTheory.ChartRestriction.DS.Xi


