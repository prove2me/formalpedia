-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_DivisorBase_FramedLatticeZeroCycleHeight
-- name    : Development_AbelianVarietyTheory_BlockTheory_DivisorBase_FramedLatticeZeroCycleHeight
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T15:45:51.454834+00:00
-- url     : https://prove2.me/theorems/6129daab-9d7a-4dd3-aae6-42ffdf63bb8c
-- title:
--   Framed Lattice Zero Cycle Height
-- statement:
--   Definitions and structural lemmas for Framed Lattice Zero Cycle Height, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/BlockTheory/DivisorBase/FramedLatticeZeroCycleHeight.lean

import Mathlib
import Definitions.Def_ReciprocityTheory_SemistableReduction_SphereLogIntegrableStatement
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_PointHeight
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
open MvPolynomial NumberField GlobalTheory.ChowHt
namespace GlobalTheory.IndefiniteRowSideFullHecke.FramedLatticeZeroCycleHeight
structure IsFramedLattice {F : Type} [Field F] {N n : ℕ} (w : Matrix (Fin N) (Fin n) F)
    (A : (F →+* ℂ) → Matrix (Fin N) (Fin N) ℂ) : Prop where

  pos : 0 < N

  span : Function.Surjective w.mulVec

  frame : ∀ σ, IsUnit (A σ).det
def extGen {F : Type} [Field F] {N n : ℕ} (E : Type) [Field E] [Algebra F E]
    (w : Matrix (Fin N) (Fin n) F) : Matrix (Fin N) (Fin n) E :=
  w.map (algebraMap F E)
def extFrame {F : Type} [Field F] {N : ℕ} (E : Type) [Field E] [Algebra F E]
    (A : (F →+* ℂ) → Matrix (Fin N) (Fin N) ℂ) : (E →+* ℂ) → Matrix (Fin N) (Fin N) ℂ :=
  fun τ => A (τ.comp (algebraMap F E))
def pairingForm {K : Type} [CommRing K] {N : ℕ} (y : Fin N → K) : MvPolynomial (Fin 1 × Fin N) K :=
  ∑ j, X ((0 : Fin 1), j) * C (y j)
def PointHeightScaling : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] (N n : ℕ) (w : Matrix (Fin N) (Fin n) F)
    (A : (F →+* ℂ) → Matrix (Fin N) (Fin N) ℂ), IsFramedLattice w A →
    ∀ (K : Type) [Field K] [NumberField K] [Algebra F K] (y : Fin N → K) (c : K),
      y ≠ 0 → c ≠ 0 → pointHeight w A (c • y) = pointHeight w A y
def PointHeightExtension : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] (N n : ℕ) (w : Matrix (Fin N) (Fin n) F)
    (A : (F →+* ℂ) → Matrix (Fin N) (Fin N) ℂ), IsFramedLattice w A →
    ∀ (K K' : Type) [Field K] [NumberField K] [Field K'] [NumberField K'] [Algebra F K]
      [Algebra F K'] [Algebra K K'] [IsScalarTower F K K'] (y : Fin N → K),
      y ≠ 0 → pointHeight w A (fun j => algebraMap K K' (y j)) = pointHeight w A y
def FormHeightExtension : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] (N n : ℕ) (w : Matrix (Fin N) (Fin n) F)
    (A : (F →+* ℂ) → Matrix (Fin N) (Fin N) ℂ), IsFramedLattice w A →
    ∀ (E : Type) [Field E] [NumberField E] [Algebra F E] (B δ : ℕ)
      (f : MvPolynomial (Fin B × Fin N) F),
      f ≠ 0 → ReciprocityTheory.MultiplicativeHeights.IsMultiHomogeneous (fun _ => δ) f →
      formHeight δ (extGen E w) (extFrame E A) (MvPolynomial.map (algebraMap F E) f) =
        formHeight δ w A f
def ZeroCycleHeightFormula : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] (N n : ℕ) (w : Matrix (Fin N) (Fin n) F)
    (A : (F →+* ℂ) → Matrix (Fin N) (Fin N) ℂ), IsFramedLattice w A →
    ∀ (E K : Type) [Field E] [NumberField E] [Field K] [NumberField K] [Algebra F E] [Algebra F K]
      [Algebra E K] [IsScalarTower F E K] (m : ℕ) (y : Fin m → Fin N → K) (c : K)
      (g : MvPolynomial (Fin 1 × Fin N) E),
      (∀ q, y q ≠ 0) → c ≠ 0 →
      MvPolynomial.map (algebraMap E K) g = C c * ∏ q, pairingForm (y q) →
      ∑ q, pointHeight w A (y q) = formHeight m (extGen E w) (extFrame E A) g
def ZeroCycleHeight : Prop :=
  ZeroCycleHeightFormula ∧ PointHeightScaling ∧ PointHeightExtension ∧ FormHeightExtension
example : IsFramedLattice (!![2, 3] : Matrix (Fin 1) (Fin 2) ℚ) (fun _ => !![5]) where
  pos := Nat.one_pos
  span := fun x => ⟨![x 0 / 2, 0], by
    funext i
    fin_cases i
    simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two]
    ring⟩
  frame := fun _ => by simp
end GlobalTheory.IndefiniteRowSideFullHecke.FramedLatticeZeroCycleHeight


