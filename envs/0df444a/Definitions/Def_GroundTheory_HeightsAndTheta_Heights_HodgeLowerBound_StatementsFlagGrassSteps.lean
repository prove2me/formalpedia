-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HodgeLowerBound_StatementsFlagGrassSteps
-- name    : GroundTheory_HeightsAndTheta_Heights_HodgeLowerBound_StatementsFlagGrassSteps
-- status  : Definition
-- author  : @community-bot-1
-- created : 2026-11-25T08:48:30.457521+00:00
-- url     : https://prove2.me/theorems/58c9ea99-9cda-4ff0-84d9-68c5d9538702
-- title:
--   Statements Flag Grass Steps
-- statement:
--   Definitions and structural lemmas for Statements Flag Grass Steps, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HodgeLowerBound/StatementsFlagGrassSteps.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HodgeLowerBound_StatementsFlagGrassPush
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_Statements
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArithmeticIntersection_MixedFieldContraction_ContractMixedFieldStatement
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_isArithVar_projLine_149b03129df9

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
namespace GroundTheory.Heights₂.Heights.LowerBoundFree
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I4
def plToIncr {j m N s : ℕ} (hs : s = j) (hN : j + m = N) (I : PlIdx j m) : PlueckerData.Incr s N :=
  ⟨fun a => Fin.cast hN (I.1.orderEmbOfFin I.2 (Fin.cast hs a)), fun a b hab => by
    rw [Fin.lt_def] at hab ⊢
    simp only [Fin.val_cast]
    exact (I.1.orderEmbOfFin I.2).strictMono (by rw [Fin.lt_def]; simpa using hab)⟩
section Block
variable (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N j : ℕ)
def grFlKappa (hj : 1 ≤ j) (hjN : j ≤ N - 1) : Fin (Fintype.card Ψ) → FlBlock Ψ N :=
  fun t => ((Fintype.equivFin Ψ).symm t, ⟨j - 1, by omega⟩)
def grFlV (hj : 1 ≤ j) (hjN : j ≤ N - 1) :
    (Σ _ : Fin (Fintype.card Ψ), PlIdx j (N - j)) → (Σ q : FlBlock Ψ N, FlIdx Ψ N q) :=
  fun p => ⟨grFlKappa Ψ N j hj hjN p.1, plToIncr (by simp only [grFlKappa]; omega) (by omega) p.2⟩
end Block
section Lines
variable (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N : ℕ)
def linForm (ℓ : Ψ × Fin N → ℤ) : RootPoly Ψ N := ∑ p, (ℓ p : ℚ) • X p
def linDeg (ℓ : Ψ × Fin N → ℤ) : FlBlock Ψ N → ℤ := fun q => ∑ p, ℓ p * xDeg Ψ N p q
def linLine (ℓ : Ψ × Fin N → ℤ) : HermLine (FlIdx Ψ N) := fsHerm (FlIdx Ψ N) (linDeg Ψ N ℓ)
variable (j : ℕ)
def muForm : Ψ × Fin N → ℤ := fun p => if (p.2 : ℕ) < j then 0 else 1
abbrev VandPair : Type :=
  {t : Ψ × Fin N × Fin N // t.2.1 < t.2.2 ∧ ((t.2.1 : ℕ) < j ↔ (t.2.2 : ℕ) < j)}
def vandForm (t : VandPair Ψ N j) : Ψ × Fin N → ℤ := fun p =>
  (if p = (t.1.1, t.1.2.1) then 1 else 0) - (if p = (t.1.1, t.1.2.2) then 1 else 0)
def vandCount : ℕ := Fintype.card (VandPair Ψ N j)
def vandLine (i : Fin (vandCount Ψ N j)) : HermLine (FlIdx Ψ N) :=
  linLine Ψ N (vandForm Ψ N j ((Fintype.equivFin (VandPair Ψ N j)).symm i))
end Lines
def FlagArithVar.Statement : Prop :=
  ∀ (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] [Nonempty Ψ] (N : ℕ), 2 ≤ N →
    IsArithVar (PFl Ψ N) (dimFl Ψ N + 1)
def FlagImageGrass.Statement : Prop :=
  ∀ (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N j : ℕ) (hj : 1 ≤ j) (hjN : j ≤ N - 1),
    imageZ (grFlV Ψ N j hj hjN) (PFl Ψ N) = grassIdeal (Fintype.card Ψ) j (N - j)
def VandCount.Statement : Prop :=
  ∀ (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N j : ℕ), j ≤ N → dimN Ψ N j + vandCount Ψ N j = dimFl Ψ N
def HFlProdLinear.Statement : Prop :=
  ∀ (II : IntersectionSystem) (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] [Nonempty Ψ] (N d : ℕ) (c : ℚ)
    (ℓ : Fin d → Ψ × Fin N → ℤ),
    IsIntersectionSystem II → 2 ≤ N → d = dimFl Ψ N + 1 →
    hFl Ψ N II (C c * ∏ i, linForm Ψ N (ℓ i)) =
      (c : ℝ) * II (FlBlock Ψ N) (FlIdx Ψ N) (PFl Ψ N) d (fun i => linLine Ψ N (ℓ i))
def FsInvPow.Statement : Prop :=
  ∀ (II : IntersectionSystem) (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (P : Ideal (MRing ι))
    (d : ℕ), IsIntersectionSystem II → IsArithVar P d →
    II K ι P d (fun _ => fsHerm ι (fun _ => -1)) = (-1) ^ d * II K ι P d (fun _ => GroundTheory.Heights₂.Heights.fsMulti ι)
def FlagGrassFibreDeg.Statement : Prop :=
  ∀ (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] [Nonempty Ψ] (N j : ℕ) (hj : 1 ≤ j) (hjN : j ≤ N - 1),
    ∃ (G : GenFibre (grFlV Ψ N j hj hjN) (PFl Ψ N))
      (J : IFamily G.Φ (fibreIdx (FlIdx Ψ N) (grFlKappa Ψ N j hj hjN))),
      IsFieldIntersection J ∧
        ((J (fibreIdeal (grFlKappa Ψ N j hj hjN) G) (vandCount Ψ N j)
          (fun i => fibreDeg (grFlKappa Ψ N j hj hjN) (vandLine Ψ N j i).a) : ℤ) : ℚ) = fdeg Ψ N j
def GrassDegFlagInt.Statement : Prop :=
  ∀ (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] [Nonempty Ψ] (N j : ℕ), 2 ≤ N → 1 ≤ j → j ≤ N - 1 →
    ((flagInt Ψ N (muPoly Ψ N j ^ dimN Ψ N j * vandBlocks Ψ N j) : ℚ) : ℝ) =
      (-1) ^ dimN Ψ N j * (fdeg Ψ N j : ℝ) *
        geomDeg (grassIdeal (Fintype.card Ψ) j (N - j))
          (GroundTheory.Heights₂.Heights.fsMulti (plBlocks (Fintype.card Ψ) j (N - j))) (dimN Ψ N j)
example : Nonempty Unit ∧ 2 ≤ 2 ∧ 1 ≤ 1 ∧ 1 ≤ 2 - 1 ∧ vandCount Unit 2 1 = 0 ∧ dimFl Unit 2 + 1 = 2 := by
  refine ⟨⟨()⟩, le_rfl, le_rfl, le_rfl, ?_, rfl⟩
  unfold vandCount
  rw [Fintype.card_eq_zero_iff]
  constructor
  rintro ⟨⟨u, a, b⟩, hab, hh⟩
  fin_cases a <;> fin_cases b <;> simp_all
example : IsArithVar (⊥ : Ideal (MRing (PBlk 2))) 2 := Inter.isArithVar_projLine
example : Nonempty Unit ∧ 2 ≤ 2 ∧ (2 = dimFl Unit 2 + 1) ∧
    linForm Unit 2 (fun p => if p = ((), 1) then 1 else 0) = X ((), 1) := by
  refine ⟨⟨()⟩, le_rfl, rfl, ?_⟩
  unfold linForm
  rw [Fintype.sum_eq_single ((), 1)]
  · simp
  · intro p hp
    simp [hp]
end GroundTheory.Heights₂.Heights.LowerBoundFree


