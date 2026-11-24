-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_StatementsArith
-- name    : GroundTheory_HeightsAndTheta_Heights_Intersections_StatementsArith
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T23:45:17.092752+00:00
-- url     : https://prove2.me/theorems/f42f38f7-bce5-4bdf-b5c4-6f0ae55b4e39
-- title:
--   Statements Arith
-- statement:
--   Definitions and structural lemmas for Statements Arith, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/StatementsArith.lean

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArithmeticIntersection_RationalSections_ThmISt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArithmeticIntersection_MixedFieldContraction_ContractMixedFieldStatement
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArithmeticIntersection_MultihomogeneousIdeals_InhDivCycleOfSuppEmpty
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_Statements
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
namespace GroundTheory.Heights₂.Heights.Inter
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4
noncomputable section
section Objects
variable {K : Type*} [Fintype K] {ι : K → Type*} [∀ k, Fintype (ι k)]
open Classical in

def horCycle (P : Ideal (MRing ι)) (s : MRing ι) : Ideal (MRing ι) →₀ ℕ :=
  (divCycle P s).filter IsHorizontal
open Classical in

def vertCycle (P : Ideal (MRing ι)) (s : MRing ι) : Ideal (MRing ι) →₀ ℕ :=
  (divCycle P s).filter fun W => ¬ IsHorizontal W
def IsClosedPt (Q : Ideal (MRing ι)) : Prop :=
  IsMultiProjPrime Q ∧ ringKrullDim (MRing ι ⧸ Q) = ((Fintype.card K : ℕ) : WithBot ℕ∞)
def HasRAt (I : Ideal (MRing ι) → (n : ℕ) → (Fin n → HermLine ι) → ℝ) (n : ℕ) : Prop :=
  ∀ (P : Ideal (MRing ι)) (L : Fin n → HermLine ι) (A : HermLine ι) (s : MRing ι),
    IsArithVar P (n + 1) → (∀ j, IsSmoothHerm (L j)) → IsSmoothHerm A → IsSectionOn P A s →
    I P (n + 1) (Fin.snoc L A) = recR I P L A s
end Objects
section TheoremI
def ThmIExists.Statement : Prop := ExistsStatement
def ThmIUnique.Statement : Prop := UniqueStatement
def ThmISymm.Statement : Prop := SymmStatement
def ThmIMultilin.Statement : Prop := MultilinStatement
def SpecIntHeightFormula.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)]
    (I : Ideal (MRing ι) → (n : ℕ) → (Fin n → HermLine ι) → ℝ) (P : Ideal (MRing ι))
    (A : HermLine ι) (s : MRing ι),
    IsArithVar P 1 → IsSmoothHerm A → IsSectionOn P A s →
    recR I P (Fin.elim0 : Fin 0 → HermLine ι) A s =
      vertR P (Fin.elim0 : Fin 0 → HermLine ι) s - arInt P s A (Fin.elim0 : Fin 0 → HermLine ι)
def RegularityIndependence.Statement : Prop := DimensionOneRationalSectionIndependence
def RegularityAdditive.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)]
    (I : Ideal (MRing ι) → (n : ℕ) → (Fin n → HermLine ι) → ℝ) (P : Ideal (MRing ι))
    (A B : HermLine ι) (s t : MRing ι),
    IsArithVar P 1 → IsSmoothHerm A → IsSmoothHerm B → IsSectionOn P A s → IsSectionOn P B t →
    recR I P (Fin.elim0 : Fin 0 → HermLine ι) (A.tensor B) (s * t) =
      recR I P (Fin.elim0 : Fin 0 → HermLine ι) A s + recR I P (Fin.elim0 : Fin 0 → HermLine ι) B t
def Swap.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)]
    (I : Ideal (MRing ι) → (n : ℕ) → (Fin n → HermLine ι) → ℝ) (P : Ideal (MRing ι)) (n : ℕ)
    (L : Fin n → HermLine ι) (A A' : HermLine ι) (s s' : MRing ι),
    HasRAt I n → IsArithVar P (n + 2) → (∀ j, IsSmoothHerm (L j)) → IsSmoothHerm A → IsSmoothHerm A' →
    IsSectionOn P A s → IsSectionOn P A' s' → (∀ W, W ∈ divSupp P s → W ∉ divSupp P s') →
    recR I P (Fin.snoc L A') A s = recR I P (Fin.snoc L A) A' s'
def Choice.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (P : Ideal (MRing ι)) (d : ℕ)
    (a : K → ℤ) (m : ℕ) (Y x : Fin m → Ideal (MRing ι)),
    IsArithVar P d → (∀ i, IsMultiProjPrime (Y i) ∧ P ≤ Y i ∧ Y i ≤ x i ∧ IsClosedPt (x i)) →
    ∃ k₀ : ℕ, ∀ k : ℕ, k₀ ≤ k →
      (∃ (b : K → ℕ) (s : MRing ι), (∀ l, (b l : ℤ) = a l + k) ∧ IsMultiHomog s b ∧ ∀ i, s ∉ x i) ∧
      ∃ t : MRing ι, IsMultiHomog t (fun _ => k) ∧ ∀ i, t ∉ x i
end TheoremI
section Consequences
def ArithmeticIntersectionSecond.Statement : Prop := MetricChangeStatement
def InductiveIntersectionFormula.Statement : Prop := VerticalStatement
def ArithmeticIntersectionFifth.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)]
    (I : Ideal (MRing ι) → (n : ℕ) → (Fin n → HermLine ι) → ℝ), IsIntersectionFamily I →
    ∀ (P : Ideal (MRing ι)) (A : HermLine ι) (s : MRing ι),
      IsArithVar P 1 → IsSmoothHerm A → IsSectionOn P A s →
      I P 1 ![A] = vertR P (Fin.elim0 : Fin 0 → HermLine ι) s - arInt P s A (Fin.elim0 : Fin 0 → HermLine ι)
def Conservation.Statement : Prop := ConservationStatement
def RatR.Statement : Prop := RatRStatement
end Consequences
section PF
def PushforwardProjectivePoint.Statement : Prop := ContractStatement
def PushforwardArithIntersection.Statement : Prop := GenDegStatement
def PushforwardProjLineRankTwo.Statement : Prop :=
  ∀ (I : AllFam), I.IsFamily →
    ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)]
      (K' : Type) [Fintype K'] (ι' : K' → Type) [∀ k, Fintype (ι' k)]
      (κ : K → K') (v : (Σ k, ι k) → (Σ k', ι' k')) (P' : Ideal (MRing ι')) (d : ℕ)
      (G : GenFibre v P') (k₀ : FibreBlock κ)
      (L : Fin d → HermLine ι) (L' : Fin d → HermLine ι') (N : HermLine ι'),
      IsBlockMap κ v → IsArithVar P' (d + 1) → IsArithVar (imageZ v P') d → (∀ k, k = k₀) →
      (∃ S : Set (MRingOver G.Φ (fibreIdx ι' κ)),
        (∀ f ∈ S, IsMultiHomog f fun _ => 1) ∧ fibreIdeal κ G = Ideal.span S) →
      (∀ j, IsSmoothHerm (L j)) → (∀ j, IsPullHerm κ v (L j) (L' j)) → IsSmoothHerm N →
      I K' ι' P' (d + 1) (Fin.append L' ![N]) = (N.a k₀.1 : ℝ) * I K ι (imageZ v P') d L
def PushforwardProjLineFlag.Statement : Prop := PFStatement
end PF
section Inhabitants
def ptTwo : Ideal (MRing (PBlk 2)) := Ideal.span {C 2, Xc 2 1}
abbrev redTwo : MRing (PBlk 2) →+* MvPolynomial ((_ : Unit) × Fin 2) (ZMod 2) :=
  MvPolynomial.map (Int.castRingHom (ZMod 2))
end Inhabitants
end
end GroundTheory.Heights₂.Heights.Inter


