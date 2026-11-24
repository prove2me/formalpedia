-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_StatementsGrassHeight
-- name    : GroundTheory_HeightsAndTheta_Heights_HeightKernels_StatementsGrassHeight
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T23:45:34.454813+00:00
-- url     : https://prove2.me/theorems/03d32adc-d677-4ab7-a56a-99e966135d1f
-- title:
--   Statements Grass Height
-- statement:
--   Definitions and structural lemmas for Statements Grass Height, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/StatementsGrassHeight.lean

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ArithmeticHilbertSamuelLowerBound
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_StatementsGrass
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
namespace GroundTheory.Heights₂.Heights
open ReciprocityTheory.ChartRestriction.G.Geo MvPolynomial Matrix
noncomputable section
abbrev PlIdx (j m : ℕ) : Type := {I : Finset (Fin (j + m)) // I.card = j}
def plAnchor (j m : ℕ) : PlIdx j m :=
  ⟨Finset.univ.map (Fin.castAddEmb m), by simp⟩
abbrev plBlocks (f j m : ℕ) : Fin f → Type := fun _ => PlIdx j m
abbrev GrassField (f j m : ℕ) : Type := FractionRing (MvPolynomial (Fin f × Fin j × Fin m) ℚ)
def grassPolyCoord (f j m : ℕ) : (Σ _ : Fin f, PlIdx j m) → MvPolynomial (Fin f × Fin j × Fin m) ℚ :=
  fun p => (colsOf (onePipe (fun a b => (X (p.1, a, b) : MvPolynomial (Fin f × Fin j × Fin m) ℚ)))
    p.2).det
def grassCoord (f j m : ℕ) : (Σ _ : Fin f, PlIdx j m) → GrassField f j m :=
  fun p => algebraMap _ _ (grassPolyCoord f j m p)
def grassIdeal (f j m : ℕ) : Ideal (MRing (plBlocks f j m)) :=
  mCoordIdeal (grassCoord f j m)
def fsMulti {K : Type*} [Fintype K] (ι : K → Type*) [∀ k, Fintype (ι k)] : HermLine ι :=
  HermLine.ofMetrics (fun k => fsMetric (ι k)) (fun _ => 1)
def IsRootMatrix {f j m : ℕ} (ζ : Fin f → Matrix (Fin j) (Fin m) ℂ) : Prop :=
  ∀ τ a b, ∃ k : ℕ, 0 < k ∧ ζ τ a b ^ k = 1
def rootCoord {f j m : ℕ} (ζ : Fin f → Matrix (Fin j) (Fin m) ℂ) : (Σ _ : Fin f, PlIdx j m) → ℂ :=
  fun p => (colsOf (onePipe (ζ p.1)) p.2).det
def rootPointIdeal {f j m : ℕ} (ζ : Fin f → Matrix (Fin j) (Fin m) ℂ) :
    Ideal (MRing (plBlocks f j m)) :=
  mCoordIdeal (rootCoord ζ)
def rootFamily (f j m : ℕ) : Set (Ideal (MRing (plBlocks f j m))) :=
  {W | ∃ ζ : Fin f → Matrix (Fin j) (Fin m) ℂ, IsRootMatrix ζ ∧ W = rootPointIdeal ζ}
def grassConst (f j m : ℕ) : ℝ := ((f * j : ℕ) : ℝ) / 2 * Real.log (1 + m)
def rootAnchorSection (f j m : ℕ) : MRing (plBlocks f j m) :=
  ∏ τ : Fin f, X ⟨τ, plAnchor j m⟩
def coneRatios {K : Type*} {ι : K → Type*} {Ω : Type*} [Field Ω] (y : (Σ k, ι k) → Ω)
    (c : ∀ k, ι k) : Set Ω :=
  Set.range fun p : Σ k, ι k => y p / y ⟨p.1, c p.1⟩
def GrassHeightBound.Statement : Prop :=
  SuccessiveMinimaUpperBound → ∀ (f j m : ℕ), 1 ≤ f → ∀ II : IntersectionSystem, IsIntersectionSystem II →
    II (Fin f) (plBlocks f j m) (grassIdeal f j m) (f * j * m + 1) (fun _ => fsMulti (plBlocks f j m)) ≤
      ((f * j * m + 1 : ℕ) : ℝ) * grassConst f j m *
        geomDeg (grassIdeal f j m) (fsMulti (plBlocks f j m)) (f * j * m)
def CoordConeArithVar.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω] [CharZero Ω]
    (y : (Σ k, ι k) → Ω) (c : ∀ k, ι k) (d : ℕ) (t : Fin d → Ω),
    Nonempty K → (∀ k, y ⟨k, c k⟩ ≠ 0) → AlgebraicIndependent ℚ t →
    (∀ i, t i ∈ IntermediateField.adjoin ℚ (coneRatios y c)) →
    (∀ r ∈ coneRatios y c, IsAlgebraic (IntermediateField.adjoin ℚ (Set.range t)) r) →
    IsArithVar (mCoordIdeal y) (d + 1)
def GrassArithVar.Statement : Prop :=
  ∀ (f j m : ℕ), 1 ≤ f → IsArithVar (grassIdeal f j m) (f * j * m + 1)
def RootArithVar.Statement : Prop :=
  ∀ (f j m : ℕ) (ζ : Fin f → Matrix (Fin j) (Fin m) ℂ), 1 ≤ f → IsRootMatrix ζ →
    IsArithVar (rootPointIdeal ζ) 1
def FsLineSmooth.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)], IsSmoothHerm (fsMulti ι)
def FsLineLevi.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (z w : (Σ k, ι k) → ℂ),
    (∀ k, ∃ i, z ⟨k, i⟩ ≠ 0) → 0 ≤ leviForm (fun z => Real.log ((fsMulti ι).h z)) z w
def FsLineSemipositive.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (P : Ideal (MRing ι)),
    IsSemipositiveRel ⊥ P (fsMulti ι)
def NefOfNonneg.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (P : Ideal (MRing ι)) (a : K → ℤ),
    (∀ k, 0 ≤ a k) → NefOnFibres P a
def FsConjInvariant.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)], IsConjInvariantH (fsMulti ι)
def MultiHomogMemCoord.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω]
    (y : (Σ k, ι k) → Ω) (g : MRing ι) (a : K → ℕ),
    IsMultiHomog g a → (g ∈ mCoordIdeal y ↔ aeval y g = 0)
def GrassLeRoot.Statement : Prop :=
  ∀ (f j m : ℕ) (ζ : Fin f → Matrix (Fin j) (Fin m) ℂ), grassIdeal f j m ≤ rootPointIdeal ζ
def RootDense.Statement : Prop :=
  ∀ (f j m : ℕ), IsZariskiDense (grassIdeal f j m) (rootFamily f j m)
def RootAnchorNonzero.Statement : Prop :=
  ∀ (f j m : ℕ) (ζ : Fin f → Matrix (Fin j) (Fin m) ℂ), IsRootMatrix ζ →
    ∀ z ∈ mcPts (rootPointIdeal ζ), ∀ τ, z ⟨τ, plAnchor j m⟩ ≠ 0
def RootPointConj.Statement : Prop :=
  ∀ (f j m : ℕ) (ζ : Fin f → Matrix (Fin j) (Fin m) ℂ), IsRootMatrix ζ →
    ∀ z ∈ mcPts (rootPointIdeal ζ), ∀ τ, ∃ ζ' : Matrix (Fin j) (Fin m) ℂ,
      (∀ a b, ∃ k : ℕ, 0 < k ∧ ζ' a b ^ k = 1) ∧
        ∀ I : PlIdx j m, z ⟨τ, I⟩ = z ⟨τ, plAnchor j m⟩ * (colsOf (onePipe ζ') I).det
def RootLogNormBound.Statement : Prop :=
  ∀ (f j m : ℕ) (ζ : Fin f → Matrix (Fin j) (Fin m) ℂ), IsRootMatrix ζ →
    ∀ z ∈ mcPts (rootPointIdeal ζ),
      -grassConst f j m ≤ logNorm (fsMulti (plBlocks f j m)) (rootAnchorSection f j m) z
def RootDivSuppEmpty.Statement : Prop :=
  ∀ (f j m : ℕ) (ζ : Fin f → Matrix (Fin j) (Fin m) ℂ), IsRootMatrix ζ →
    divSupp (rootPointIdeal ζ) (rootAnchorSection f j m) = ∅
abbrev McClasses {K : Type*} [Fintype K] {ι : K → Type*} [∀ k, Fintype (ι k)]
    (W : Ideal (MRing ι)) : Type _ :=
  Quot fun z z' : mcPts W => ∃ c : K → ℂ, (∀ k, c k ≠ 0) ∧
    (z' : (Σ k, ι k) → ℂ) = fun p => c p.1 * (z : (Σ k, ι k) → ℂ) p
def RootPointsFinite.Statement : Prop :=
  ∀ (f j m : ℕ) (ζ : Fin f → Matrix (Fin j) (Fin m) ℂ), IsRootMatrix ζ →
    Finite (McClasses (rootPointIdeal ζ))
def PtsIntegralZeroLower.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (W : Ideal (MRing ι))
    (φ : Fin 0 → ((Σ k, ι k) → ℂ) → ℝ) (g : ((Σ k, ι k) → ℂ) → ℝ) (c : ℝ),
    IsMultiHomogIdeal W → Finite (McClasses W) →
    (∀ (u : K → ℂ) (z : (Σ k, ι k) → ℂ), (∀ k, u k ≠ 0) → z ∈ mcPts W →
      g (fun p => u p.1 * z p) = g z) →
    (∀ z ∈ mcPts W, c ≤ g z) →
    c * degC W ≤ ptsIntegral (e := 0) W φ g
def RootHeight.Statement : Prop :=
  ∀ (f j m : ℕ) (ζ : Fin f → Matrix (Fin j) (Fin m) ℂ), 1 ≤ f → IsRootMatrix ζ →
    ∀ II : IntersectionSystem, IsIntersectionSystem II →
      II (Fin f) (plBlocks f j m) (rootPointIdeal ζ) 1 ![fsMulti (plBlocks f j m)] ≤
        grassConst f j m * degC (rootPointIdeal ζ)
example : IsRootMatrix (fun _ : Fin 1 => (!![-1] : Matrix (Fin 1) (Fin 1) ℂ)) := by
  intro τ a b
  refine ⟨2, by norm_num, ?_⟩
  fin_cases a; fin_cases b; simp
example : 1 ≤ (1 : ℕ) := le_rfl
def lineExampleCoord : (Σ _ : Unit, Fin 2) → FractionRing (MvPolynomial (Fin 1) ℚ) :=
  fun p => if p.2 = 0 then 1 else algebraMap _ _ (X 0 : MvPolynomial (Fin 1) ℚ)
def lineExampleT : Fin 1 → FractionRing (MvPolynomial (Fin 1) ℚ) :=
  fun _ => algebraMap _ _ (X 0 : MvPolynomial (Fin 1) ℚ)
example : (∀ k : Unit, lineExampleCoord ⟨k, 0⟩ ≠ 0) ∧ AlgebraicIndependent ℚ lineExampleT ∧
    (∀ i, lineExampleT i ∈ IntermediateField.adjoin ℚ (coneRatios lineExampleCoord fun _ => 0)) ∧
    (∀ r ∈ coneRatios lineExampleCoord (fun _ => 0),
      IsAlgebraic (IntermediateField.adjoin ℚ (Set.range lineExampleT)) r) := by
  refine ⟨fun _ => by simp [lineExampleCoord], ?_, ?_, ?_⟩
  · have h := (MvPolynomial.algebraicIndependent_X (Fin 1) ℚ).map'
      (f := (IsScalarTower.toAlgHom ℚ (MvPolynomial (Fin 1) ℚ) (FractionRing (MvPolynomial (Fin 1) ℚ))))
      (IsFractionRing.injective _ _)
    have e : lineExampleT = (IsScalarTower.toAlgHom ℚ (MvPolynomial (Fin 1) ℚ)
        (FractionRing (MvPolynomial (Fin 1) ℚ))) ∘ X := by
      funext i; fin_cases i; rfl
    rw [e]; exact h
  · intro i
    apply IntermediateField.subset_adjoin
    refine ⟨⟨(), 1⟩, ?_⟩
    simp [lineExampleCoord, lineExampleT]
  · rintro r ⟨p, rfl⟩
    have hr : lineExampleCoord p / lineExampleCoord ⟨p.1, 0⟩ ∈
        IntermediateField.adjoin ℚ (Set.range lineExampleT) := by
      by_cases h : p.2 = 0
      · simp [lineExampleCoord, h]
      · have : lineExampleCoord p / lineExampleCoord ⟨p.1, 0⟩ = lineExampleT 0 := by
          simp [lineExampleCoord, h, lineExampleT]
        rw [this]
        exact IntermediateField.subset_adjoin _ _ ⟨0, rfl⟩
    exact isAlgebraic_algebraMap (R := IntermediateField.adjoin ℚ (Set.range lineExampleT))
      (A := FractionRing (MvPolynomial (Fin 1) ℚ)) ⟨_, hr⟩
example : IsMultiHomog (rootAnchorSection 2 1 1) (fun _ => 1) := by
  intro μ hμ k
  classical
  simp only [rootAnchorSection, Fin.prod_univ_two] at hμ
  rw [MvPolynomial.support_X_mul] at hμ
  · simp only [Finset.mem_map, MvPolynomial.support_X, Finset.mem_singleton] at hμ
    obtain ⟨ν, rfl, hν⟩ := hμ
    subst hν
    fin_cases k <;> simp [Finsupp.single_apply]
end
end GroundTheory.Heights₂.Heights


