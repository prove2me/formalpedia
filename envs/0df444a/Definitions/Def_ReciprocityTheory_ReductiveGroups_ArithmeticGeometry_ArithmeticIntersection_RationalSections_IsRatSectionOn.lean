-- Prove2me | Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArithmeticIntersection_RationalSections_IsRatSectionOn
-- name    : ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArithmeticIntersection_RationalSections_IsRatSectionOn
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T23:29:40.601432+00:00
-- url     : https://prove2.me/theorems/e3daf431-bfd0-481b-b088-f14a56572165
-- title:
--   Is Rat Section On
-- statement:
--   Definitions and structural lemmas for Is Rat Section On, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ArithmeticIntersection/RationalSections/IsRatSectionOn.lean

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterSt
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
abbrev AllFam : Type 1 :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)],
    Ideal (MRing ι) → (n : ℕ) → (Fin n → HermLine ι) → ℝ
def AllFam.IsFamily (I : AllFam) : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)], IsIntersectionFamily (I K ι)
variable {K : Type*} [Fintype K] {ι : K → Type*} [∀ k, Fintype (ι k)]
def IsRFamily (I : Ideal (MRing ι) → (n : ℕ) → (Fin n → HermLine ι) → ℝ) : Prop :=
  (∀ P n (L : Fin n → HermLine ι) (A B : HermLine ι), IsArithVar P (n + 1) →
      (∀ j, IsSmoothHerm (L j)) → IsSmoothHerm A → IsSmoothHerm B →
      I P (n + 1) (Fin.snoc L (A.tensor B)) =
        I P (n + 1) (Fin.snoc L A) + I P (n + 1) (Fin.snoc L B)) ∧
  (∀ P n (L : Fin n → HermLine ι) (A : HermLine ι) (s : MRing ι) (a : K → ℕ),
      IsArithVar P (n + 1) → (∀ j, IsSmoothHerm (L j)) → IsSmoothHerm A →
      (∀ k, A.a k = a k) → IsMultiHomog s a → s ∉ P →
      I P (n + 1) (Fin.snoc L A) = recR I P L A s)
open Classical in

def cycR (I : Ideal (MRing ι) → (n : ℕ) → (Fin n → HermLine ι) → ℝ) (P : Ideal (MRing ι)) {n : ℕ}
    (L : Fin n → HermLine ι) (s : MRing ι) : ℝ :=
  ∑ᶠ W ∈ divSupp P s, (multAt (P ⊔ Ideal.span {s}) W : ℝ) *
    (if IsHorizontal W then I W n L else (geoNum n W (fun j => (L j).a) : ℝ) * Real.log (charOf W))
open Classical in

def vertR (P : Ideal (MRing ι)) {n : ℕ} (L : Fin n → HermLine ι) (s : MRing ι) : ℝ :=
  ∑ᶠ W ∈ divSupp P s, (multAt (P ⊔ Ideal.span {s}) W : ℝ) *
    (if IsHorizontal W then 0 else (geoNum n W (fun j => (L j).a) : ℝ) * Real.log (charOf W))
def IsRatSectionOn (P : Ideal (MRing ι)) (A : HermLine ι) (f g : MRing ι) : Prop :=
  ∃ α β : K → ℕ, IsMultiHomog f α ∧ IsMultiHomog g β ∧ f ∉ P ∧ g ∉ P ∧
    ∀ k, (α k : ℤ) - β k = A.a k
def logNormRat (A : HermLine ι) (f g : MRing ι) (z : (Σ k, ι k) → ℂ) : ℝ :=
  Real.log (‖eval z (map (Int.castRingHom ℂ) f)‖ / ‖eval z (map (Int.castRingHom ℂ) g)‖ / A.h z)
def recRRat (I : Ideal (MRing ι) → (n : ℕ) → (Fin n → HermLine ι) → ℝ) (P : Ideal (MRing ι))
    {n : ℕ} (L : Fin n → HermLine ι) (A : HermLine ι) (f g : MRing ι) : ℝ :=
  cycR I P L f - cycR I P L g - ptsIntegral P (pot L) (logNormRat A f g)
def constLine (c : ℝ) : HermLine ι :=
  HermLine.ofWeight (fun _ => c) (fun _ _ _ => rfl)
end ReciprocityTheory.ChartRestriction.G.AI.I2


