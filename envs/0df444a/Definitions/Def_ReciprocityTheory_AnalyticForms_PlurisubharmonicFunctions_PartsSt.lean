-- Prove2me | Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_PartsSt
-- name    : ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_PartsSt
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T15:06:04.92105+00:00
-- url     : https://prove2.me/theorems/8107f9ef-5e2e-43e3-a1b8-2357c3627a17
-- title:
--   Parts St
-- statement:
--   Definitions and structural lemmas for Parts St, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/PlurisubharmonicFunctions/PartsSt.lean

import Mathlib
import Definitions.Def_ReciprocityTheory_AnalyticForms_MaIntEmpty
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace ReciprocityTheory.AnForm.A
open MeasureTheory ReciprocityTheory.AnForm
noncomputable section
section Partials
variable {D : ℕ}
def dz (j : Fin D) (f : (Fin D → ℂ) → ℂ) (z : Fin D → ℂ) : ℂ :=
  (fderiv ℝ f z (Pi.single j 1) - Complex.I * fderiv ℝ f z (Complex.I • Pi.single j 1)) / 2
def dzb (j : Fin D) (f : (Fin D → ℂ) → ℂ) (z : Fin D → ℂ) : ℂ :=
  (fderiv ℝ f z (Pi.single j 1) + Complex.I * fderiv ℝ f z (Complex.I • Pi.single j 1)) / 2
def cplx (v : (Fin D → ℂ) → ℝ) : (Fin D → ℂ) → ℂ := fun z => (v z : ℂ)
def gradMat (v w : (Fin D → ℂ) → ℝ) (z : Fin D → ℂ) : Matrix (Fin D) (Fin D) ℂ :=
  fun j k => dz j (cplx v) z * dzb k (cplx w) z
end Partials
section Densities
variable {n : ℕ}
def gradDens (φ : Fin n → (Fin (n + 1) → ℂ) → ℝ) (v w : (Fin (n + 1) → ℂ) → ℝ)
    (z : Fin (n + 1) → ℂ) : ℝ :=
  ((n + 1).factorial : ℝ) * (2 / Real.pi) ^ (n + 1) *
    (mdisc (Fin.cons (gradMat v w z) fun i => hessC (φ i) z)).re
def gradInt (φ : Fin n → (Fin (n + 1) → ℂ) → ℝ) (v w : (Fin (n + 1) → ℂ) → ℝ)
    (U : Set (Fin (n + 1) → ℂ)) : ℝ :=
  ∫ z in U, gradDens φ v w z
def mixedCof (B : Fin n → Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) :
    Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ :=
  fun j k => mdisc (Fin.cons (Matrix.single j k 1) B)
def hessCof (φ : Fin n → (Fin (n + 1) → ℂ) → ℝ) (z : Fin (n + 1) → ℂ) :
    Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ :=
  mixedCof fun i => hessC (φ i) z
end Densities
section MdiscLinear
def polCoef {D : ℕ} (r : Fin D → Fin D) : ℂ :=
  ∑ S : Finset (Fin D), (-1 : ℂ) ^ (D - S.card) * if (∀ i, r i ∈ S) then 1 else 0
end MdiscLinear
section Statements
variable {n : ℕ}
def IntegralDzStatement : Prop :=
  ∀ (D : ℕ) (j : Fin D) (g : (Fin D → ℂ) → ℂ), ContDiff ℝ 1 g → HasCompactSupport g →
    (∫ z, dz j g z) = 0 ∧ (∫ z, dzb j g z) = 0
def PiolaStatement : Prop :=
  ∀ (n : ℕ) (φ : Fin n → (Fin (n + 1) → ℂ) → ℝ) (U : Set (Fin (n + 1) → ℂ)),
    IsOpen U → (∀ i, ContDiffOn ℝ 3 (φ i) U) → ∀ z ∈ U,
      (∀ k, ∑ j, dz j (fun y => hessCof φ y j k) z = 0) ∧
      (∀ j, ∑ k, dzb k (fun y => hessCof φ y j k) z = 0)
def PartsHyp (φ : Fin n → (Fin (n + 1) → ℂ) → ℝ) (v w : (Fin (n + 1) → ℂ) → ℝ)
    (U : Set (Fin (n + 1) → ℂ)) : Prop :=
  IsOpen U ∧ ContDiffOn ℝ 3 v U ∧ HasCompactSupport v ∧ tsupport v ⊆ U ∧
    ContDiffOn ℝ 3 w U ∧ ∀ i, ContDiffOn ℝ 3 (φ i) U
def PartsStatement : Prop :=
  ∀ (n : ℕ) (φ : Fin n → (Fin (n + 1) → ℂ) → ℝ) (v w : (Fin (n + 1) → ℂ) → ℝ)
    (U : Set (Fin (n + 1) → ℂ)), PartsHyp φ v w U →
      IntegrableOn (fun z => v z * maDens (Fin.cons w φ) z) U ∧
      IntegrableOn (fun z => w z * maDens (Fin.cons v φ) z) U ∧
      IntegrableOn (gradDens φ v w) U ∧
      maInt (Fin.cons w φ) v U = - gradInt φ v w U ∧
      maInt (Fin.cons v φ) w U = maInt (Fin.cons w φ) v U
def MassZeroStatement : Prop :=
  ∀ (n : ℕ) (φ : Fin n → (Fin (n + 1) → ℂ) → ℝ) (v : (Fin (n + 1) → ℂ) → ℝ)
    (U : Set (Fin (n + 1) → ℂ)), PartsHyp φ v (fun _ => 1) U →
      (∫ z in U, maDens (Fin.cons v φ) z) = 0
def GradDensSymmStatement : Prop :=
  ∀ (n : ℕ) (φ : Fin n → (Fin (n + 1) → ℂ) → ℝ) (v w : (Fin (n + 1) → ℂ) → ℝ)
    (U : Set (Fin (n + 1) → ℂ)), IsOpen U → (∀ i, ContDiffOn ℝ 2 (φ i) U) →
      ∀ z ∈ U, gradDens φ v w z = gradDens φ w v z
def GradDensNonnegStatement : Prop :=
  ∀ (n : ℕ) (φ : Fin n → (Fin (n + 1) → ℂ) → ℝ) (v : (Fin (n + 1) → ℂ) → ℝ)
    (U : Set (Fin (n + 1) → ℂ)), IsOpen U → (∀ i, ContDiffOn ℝ 2 (φ i) U) →
      (∀ i, ∀ z ∈ U, ∀ ξ, 0 ≤ levi (φ i) z ξ) →
      ∀ z ∈ U, 0 ≤ gradDens φ v v z
def HessCDzStatement : Prop :=
  ∀ (D : ℕ) (v : (Fin D → ℂ) → ℝ) (U : Set (Fin D → ℂ)), IsOpen U → ContDiffOn ℝ 2 v U →
    ∀ z ∈ U, ∀ j k, hessC v z j k = dz j (dzb k (cplx v)) z
def DoubleDivStatement : Prop :=
  ∀ (n : ℕ) (φ : Fin n → (Fin (n + 1) → ℂ) → ℝ) (v : (Fin (n + 1) → ℂ) → ℝ)
    (U : Set (Fin (n + 1) → ℂ)), IsOpen U → ContDiffOn ℝ 2 v U →
      (∀ i, ContDiffOn ℝ 4 (φ i) U) → ∀ z ∈ U,
        ∑ j, ∑ k, dz j (dzb k (fun y => cplx v y * hessCof φ y j k)) z =
          ∑ j, ∑ k, hessCof φ z j k * dz j (dzb k (cplx v)) z
def GradDensCauchySchwarzStatement : Prop :=
  ∀ (n : ℕ) (φ : Fin n → (Fin (n + 1) → ℂ) → ℝ) (v w : (Fin (n + 1) → ℂ) → ℝ)
    (U : Set (Fin (n + 1) → ℂ)), IsOpen U → (∀ i, ContDiffOn ℝ 2 (φ i) U) →
      (∀ i, ∀ z ∈ U, ∀ ξ, 0 ≤ levi (φ i) z ξ) →
      ∀ z ∈ U, gradDens φ v w z ^ 2 ≤ gradDens φ v v z * gradDens φ w w z
def MaDensCofStatement : Prop :=
  ∀ (n : ℕ) (φ : Fin n → (Fin (n + 1) → ℂ) → ℝ) (v : (Fin (n + 1) → ℂ) → ℝ)
    (U : Set (Fin (n + 1) → ℂ)), IsOpen U → ContDiffOn ℝ 2 v U → ∀ z ∈ U,
      maDens (Fin.cons v φ) z = ((n + 1).factorial : ℝ) * (2 / Real.pi) ^ (n + 1) *
        (∑ j, ∑ k, hessCof φ z j k * dz j (dzb k (cplx v)) z).re
def HessCRestrictStatement : Prop :=
  ∀ (n : ℕ) (φ : (Fin (n + 1) → ℂ) → ℝ) (U : Set (Fin (n + 1) → ℂ)) (j : Fin (n + 1)),
    IsOpen U → ContDiffOn ℝ 2 φ U → ∀ y : Fin n → ℂ,
      (Fin.insertNth (α := fun _ => ℂ) j 0 y) ∈ U →
        hessC (fun y' => φ (Fin.insertNth (α := fun _ => ℂ) j 0 y')) y =
          (hessC φ (Fin.insertNth (α := fun _ => ℂ) j 0 y)).submatrix j.succAbove j.succAbove
def GradDensLeibnizStatement : Prop :=
  ∀ (n : ℕ) (φ : Fin n → (Fin (n + 1) → ℂ) → ℝ) (f g w : (Fin (n + 1) → ℂ) → ℝ)
    (z : Fin (n + 1) → ℂ), DifferentiableAt ℝ f z → DifferentiableAt ℝ g z →
      gradDens φ (fun y => f y * g y) w z = f z * gradDens φ g w z + g z * gradDens φ f w z ∧
      gradDens φ g (fun y => g y ^ 2 / 2) z = g z * gradDens φ g g z
def PartsHypInhabitStatement : Prop :=
  ∀ (n : ℕ) (U : Set (Fin (n + 1) → ℂ)), IsOpen U → ∀ z ∈ U,
    ∀ φ : Fin n → (Fin (n + 1) → ℂ) → ℝ, (∀ i, ContDiffOn ℝ 3 (φ i) U) →
      ∃ v : (Fin (n + 1) → ℂ) → ℝ, PartsHyp φ v v U ∧ v z = 1
def PartsInhabitStatement : Prop :=
  ∃ v : (Fin 1 → ℂ) → ℝ,
    PartsHyp (n := 0) Fin.elim0 v v Set.univ ∧ 0 < gradInt (n := 0) Fin.elim0 v v Set.univ
end Statements
end
end ReciprocityTheory.AnForm.A


