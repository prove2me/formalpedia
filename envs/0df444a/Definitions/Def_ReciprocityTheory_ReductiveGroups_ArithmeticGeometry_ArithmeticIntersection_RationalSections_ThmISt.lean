-- Prove2me | Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArithmeticIntersection_RationalSections_ThmISt
-- name    : ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArithmeticIntersection_RationalSections_ThmISt
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T23:32:42.225315+00:00
-- url     : https://prove2.me/theorems/6d8a8e2d-2477-4fe8-ad99-f9003e462538
-- title:
--   Thm ISt
-- statement:
--   Definitions and structural lemmas for Thm ISt, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ArithmeticIntersection/RationalSections/ThmISt.lean

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArithmeticIntersection_RationalSections_IsRatSectionOn
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArithmeticIntersection_MultihomogeneousIdeals_IsFieldIntersection
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArithmeticIntersection_IndexSt
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
namespace ReciprocityTheory.ChartRestriction.G.AI.I2
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo
abbrev SmoothFn {K : Type*} [Fintype K] {ι : K → Type*} [∀ k, Fintype (ι k)] (u : ((Σ k, ι k) → ℂ) → ℝ) : Prop :=
  ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) u {z | ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0}
section TheoremI
def ArithVarZeroStatement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (P : Ideal (MRing ι)), ¬ IsArithVar P 0
def ExistsStatement : Prop :=
  ∃ I : AllFam, I.IsFamily
def UniqueStatement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)]
    (I J : Ideal (MRing ι) → (n : ℕ) → (Fin n → HermLine ι) → ℝ), IsRFamily I → IsRFamily J →
    ∀ (P : Ideal (MRing ι)) (n : ℕ) (L : Fin n → HermLine ι), 1 ≤ n → IsArithVar P n →
      (∀ j, IsSmoothHerm (L j)) → I P n L = J P n L
def SymmStatement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)]
    (I : Ideal (MRing ι) → (n : ℕ) → (Fin n → HermLine ι) → ℝ), IsRFamily I →
    ∀ (P : Ideal (MRing ι)) (n : ℕ) (L : Fin n → HermLine ι) (σ : Equiv.Perm (Fin n)),
      IsArithVar P n → (∀ j, IsSmoothHerm (L j)) → I P n (L ∘ σ) = I P n L
def MultilinStatement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)]
    (I : Ideal (MRing ι) → (n : ℕ) → (Fin n → HermLine ι) → ℝ), IsRFamily I →
    ∀ (P : Ideal (MRing ι)) (n : ℕ) (L : Fin n → HermLine ι) (j : Fin n) (A B : HermLine ι),
      IsArithVar P n → (∀ j, IsSmoothHerm (L j)) → IsSmoothHerm A → IsSmoothHerm B →
      I P n (Function.update L j (A.tensor B)) =
        I P n (Function.update L j A) + I P n (Function.update L j B)
def TheoremIStatement : Prop :=
  ExistsStatement ∧ UniqueStatement ∧ SymmStatement ∧ MultilinStatement
def AvoidStatement : Prop :=
  ∀ (R : Type) [CommRing R] (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)]
    (Ws : Finset (Ideal (MRingOver R ι))), (∀ W ∈ Ws, IsMultiProjPrime W) →
    ∃ d₀ : K → ℕ, ∀ d : K → ℕ, d₀ ≤ d →
      ∃ s : MRingOver R ι, IsMultiHomog s d ∧ ∀ W ∈ Ws, s ∉ W
def RMulStatement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)]
    (I : Ideal (MRing ι) → (n : ℕ) → (Fin n → HermLine ι) → ℝ) (P : Ideal (MRing ι)) (n : ℕ)
    (L : Fin n → HermLine ι) (A B : HermLine ι) (s t : MRing ι),
    IsArithVar P (n + 1) → (∀ j, IsSmoothHerm (L j)) → IsSmoothHerm A → IsSmoothHerm B →
    IsSectionOn P A s → IsSectionOn P B t →
    recR I P L (A.tensor B) (s * t) = recR I P L A s + recR I P L B t
def DimensionOneRationalSectionIndependence : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)]
    (I : Ideal (MRing ι) → (n : ℕ) → (Fin n → HermLine ι) → ℝ) (P : Ideal (MRing ι))
    (A : HermLine ι) (s t : MRing ι),
    IsArithVar P 1 → IsSectionOn P A s → IsSectionOn P A t →
    recR I P (Fin.elim0 : Fin 0 → HermLine ι) A s = recR I P (Fin.elim0 : Fin 0 → HermLine ι) A t
def DimensionOneRationalSectionsFromIndex : Prop :=
  IndexStatement → DimensionOneRationalSectionIndependence
end TheoremI
section Consequences
def RatRStatement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)]
    (I : Ideal (MRing ι) → (n : ℕ) → (Fin n → HermLine ι) → ℝ), IsIntersectionFamily I →
    ∀ (P : Ideal (MRing ι)) (n : ℕ) (L : Fin n → HermLine ι) (A : HermLine ι) (f g : MRing ι),
      IsArithVar P (n + 1) → (∀ j, IsSmoothHerm (L j)) → IsSmoothHerm A → IsRatSectionOn P A f g →
      I P (n + 1) (Fin.snoc L A) = recRRat I P L A f g
def MetricChangeStatement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)]
    (I : Ideal (MRing ι) → (n : ℕ) → (Fin n → HermLine ι) → ℝ), IsIntersectionFamily I →
    ∀ (P : Ideal (MRing ι)) (n : ℕ) (L : Fin n → HermLine ι) (A : HermLine ι)
      (u : ((Σ k, ι k) → ℂ) → ℝ)
      (hu : ∀ (c : K → ℂ) z, (∀ k, c k ≠ 0) → u (fun p => c p.1 * z p) = u z),
      IsArithVar P (n + 1) → (∀ j, IsSmoothHerm (L j)) → IsSmoothHerm A → SmoothFn u →
      I P (n + 1) (Fin.snoc L (A.tensor (HermLine.ofWeight u hu))) =
        I P (n + 1) (Fin.snoc L A) - ptsIntegral P (pot L) u
def MetricLocalStatement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)]
    (I : Ideal (MRing ι) → (n : ℕ) → (Fin n → HermLine ι) → ℝ), IsIntersectionFamily I →
    ∀ (P : Ideal (MRing ι)) (n : ℕ) (L L' : Fin n → HermLine ι),
      IsArithVar P n → (∀ j, IsSmoothHerm (L j)) → (∀ j, IsSmoothHerm (L' j)) →
      (∀ j, (L j).a = (L' j).a) → (∀ j, ∀ z ∈ mcPts P, (L j).h z = (L' j).h z) →
      I P n L = I P n L'
def VerticalStatement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)]
    (I : Ideal (MRing ι) → (n : ℕ) → (Fin n → HermLine ι) → ℝ), IsIntersectionFamily I →
    ∀ (P : Ideal (MRing ι)) (n : ℕ) (L : Fin n → HermLine ι) (A : HermLine ι) (f g : MRing ι),
      IsArithVar P (n + 1) → (∀ j, IsSmoothHerm (L j)) → IsSmoothHerm A → IsRatSectionOn P A f g →
      (∀ W, IsHorizontal W → (W ∈ divSupp P f ↔ W ∈ divSupp P g)) →
      (∀ W, IsHorizontal W → W ∈ divSupp P f →
        multAt (P ⊔ Ideal.span {f}) W = multAt (P ⊔ Ideal.span {g}) W) →
      (∀ z ∈ mcPts P, ‖eval z (map (Int.castRingHom ℂ) f)‖ =
        ‖eval z (map (Int.castRingHom ℂ) g)‖ * A.h z) →
      I P (n + 1) (Fin.snoc L A) = vertR P L f - vertR P L g
def TelescopeStatement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)]
    (I : Ideal (MRing ι) → (n : ℕ) → (Fin n → HermLine ι) → ℝ), IsIntersectionFamily I →
    ∀ (P : Ideal (MRing ι)) (D : ℕ) (A : HermLine ι) (u : ((Σ k, ι k) → ℂ) → ℝ)
      (hu : ∀ (c : K → ℂ) z, (∀ k, c k ≠ 0) → u (fun p => c p.1 * z p) = u z),
      IsArithVar P (D + 1) → IsSmoothHerm A → SmoothFn u →
      I P (D + 1) (fun _ => A.tensor (HermLine.ofWeight u hu)) - I P (D + 1) (fun _ => A) =
        -∑ i ∈ Finset.range (D + 1),
          ptsIntegral P (pot fun j : Fin D => if (j : ℕ) < i then A.tensor (HermLine.ofWeight u hu) else A) u
def ConservationStatement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)]
    (I : Ideal (MRing ι) → (n : ℕ) → (Fin n → HermLine ι) → ℝ), IsIntersectionFamily I →
    ∀ (P : Ideal (MRing ι)) (n : ℕ) (L : Fin n → HermLine ι) (p : ℕ),
      IsArithVar P (n + 1) → (∀ j, IsSmoothHerm (L j)) → p.Prime →
      I P (n + 1) (Fin.snoc L (constLine (-Real.log p))) = vertR P L (C (p : ℤ)) ∧
        I P (n + 1) (Fin.snoc L (constLine (-Real.log p))) =
          Real.log p * ptsIntegral P (pot L) (fun _ => 1)
def FibreCompStatement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (P : Ideal (MRing ι)) (n : ℕ)
    (A : HermLine ι) (s : MRing ι) (W : Ideal (MRing ι)),
    IsArithVar P (n + 1) → IsSectionOn P A s → W ∈ divSupp P s → ¬ IsHorizontal W →
    ∃ hp : (charOf W).Prime, ((charOf W : ℕ) : MRing ι) ∈ W ∧ IsMultiProjPrime W ∧
      (haveI : Fact (charOf W).Prime := ⟨hp⟩
       I1.IsProjVarF (W.map (MvPolynomial.map (Int.castRingHom (ZMod (charOf W))))) n)
end Consequences
section Inhabit
def DimensionOneRationalSectionExample : Prop :=
  IsArithVar (⊥ : Ideal (MRing (PBlk 1))) 1 ∧
    ∀ I : Ideal (MRing (PBlk 1)) → (n : ℕ) → (Fin n → HermLine (PBlk 1)) → ℝ,
      IsIntersectionFamily I → ∀ A : HermLine (PBlk 1), IsSmoothHerm A →
        I ⊥ 1 ![A] = Real.log (A.h 1)
def ProjectiveLineRationalSectionExample : Prop :=
  ∀ I : Ideal (MRing (PBlk 2)) → (n : ℕ) → (Fin n → HermLine (PBlk 2)) → ℝ,
    IsIntersectionFamily I → I ⊥ 2 ![fsLine 2, fsLine 2] = 1 / 2
def InhabitVertStatement : Prop :=
  ∀ p : ℕ, p.Prime →
    IsRatSectionOn (⊥ : Ideal (MRing (PBlk 2))) (constLine (-Real.log p)) (C (p : ℤ)) 1 ∧
    (∀ W ∈ divSupp (⊥ : Ideal (MRing (PBlk 2))) (C (p : ℤ)), ¬ IsHorizontal W) ∧
    (∀ z ∈ mcPts (⊥ : Ideal (MRing (PBlk 2))),
      ‖eval z (map (Int.castRingHom ℂ) (C (p : ℤ)))‖ =
        ‖eval z (map (Int.castRingHom ℂ) (1 : MRing (PBlk 2)))‖ *
          (constLine (-Real.log p) : HermLine (PBlk 2)).h z)
end Inhabit
end ReciprocityTheory.ChartRestriction.G.AI.I2


