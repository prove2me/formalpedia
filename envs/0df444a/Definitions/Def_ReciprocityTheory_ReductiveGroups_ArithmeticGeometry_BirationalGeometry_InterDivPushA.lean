-- Prove2me | Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterDivPushA
-- name    : ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterDivPushA
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T00:20:19.095487+00:00
-- url     : https://prove2.me/theorems/c7902168-0fe3-499b-80e3-cea9391f1405
-- title:
--   Inter Div Push A
-- statement:
--   Definitions and structural lemmas for Inter Div Push A, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/BirationalGeometry/InterDivPushA.lean

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterRed
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterDivSupp
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
namespace ReciprocityTheory.ChartRestriction.G.Geo
open MvPolynomial MeasureTheory ReciprocityTheory.AnForm.M
def DivPushCommonProjStatement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (P : Ideal (MRing ι)) (n : ℕ)
    (A : HermLine ι) (s : MRing ι), IsArithVar P (n + 2) → IsSectionOn P A s →
    ∃ Ψ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (n + 1) → ℂ),
      ∀ W ∈ divSupp P s, IsHorizontal W → IsGoodProj W Ψ
def DivPushFibreStatement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (P J : Ideal (MRing ι)) (n : ℕ)
    (R : AnLogRes P J (n + 1)) (L : Fin n → HermLine ι) (A B : HermLine ι) (s : MRing ι)
    (r : ℕ) (m : Fin r → ℕ) (W : Fin r → Set R.X) (BW : ∀ k, FinHolAtlas n (W k))
    (Ψ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (n + 1) → ℂ)),
    IsArithVar P (n + 2) → (∀ j, IsSmoothHerm (L j)) → IsSmoothHerm A → IsSmoothHerm B →
    B.a = 0 → IsSectionOn P A s →
    IsSNC R.A (potOf R A) (fun x y => eval (R.lift x y) (map (Int.castRingHom ℂ) s)) m W →
    (∀ k, HoloMap (BW k) R.A Subtype.val) →
    (∀ W' ∈ divSupp P s, IsHorizontal W' → IsGoodProj W' Ψ) →
    ∑ k, (m k : ℝ) * mInt (BW k)
        (fun i => (potOf R (L i)).pullback Subtype.val continuous_subtype_val)
        ((fun x => Real.log (B.h (R.lift x x))) ∘ Subtype.val) =
      ∫ y, ∑ᶠ (W') (_ : W' ∈ divSupp P s ∧ IsHorizontal W'),
        (multAt (P ⊔ Ideal.span {s}) W' : ℝ) *
          ∑ᶠ w ∈ fibre W' Ψ y, sheetDensity W' Ψ (pot L) (fun z => Real.log (B.h z)) y w
def projCoord {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {P J : Ideal (MRing ι)}
    {e n : ℕ} (R : AnLogRes P J e) (Ψ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (n + 1) → ℂ)) (x : R.X) :
    Fin n → ℂ :=
  fun i => Ψ (segre (R.lift x x)) i.succ / Ψ (segre (R.lift x x)) 0
def divFib {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {P J : Ideal (MRing ι)}
    {n : ℕ} (R : AnLogRes P J (n + 1)) (L : Fin n → HermLine ι) (B : HermLine ι)
    (Ψ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (n + 1) → ℂ)) {V : Set R.X} (BV : FinHolAtlas n V)
    (y : Fin n → ℂ) : ℝ :=
  ∑ᶠ x ∈ (projCoord R Ψ ∘ Subtype.val : V → Fin n → ℂ) ⁻¹' {y},
    Real.log (B.h (R.lift x x)) *
      pushDens BV (fun i => (potOf R (L i)).pullback Subtype.val continuous_subtype_val)
        (projCoord R Ψ ∘ Subtype.val) x
def DivPushResSideStatement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (P J : Ideal (MRing ι)) (n : ℕ)
    (R : AnLogRes P J (n + 1)) (L : Fin n → HermLine ι) (B : HermLine ι)
    (Ψ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (n + 1) → ℂ)) (V : Set R.X) (BV : FinHolAtlas n V),
    IsArithVar P (n + 2) → (∀ j, IsSmoothHerm (L j)) → IsSmoothHerm B → B.a = 0 → IsClosed V →
    HoloMap BV R.A Subtype.val → (∀ x ∈ V, Ψ (segre (R.lift x x)) ≠ 0) →
    Integrable (divFib R L B Ψ BV) ∧
      mInt BV (fun i => (potOf R (L i)).pullback Subtype.val continuous_subtype_val)
        ((fun x => Real.log (B.h (R.lift x x))) ∘ Subtype.val) = ∫ y, divFib R L B Ψ BV y
def DivPushPointStatement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (P J : Ideal (MRing ι)) (n : ℕ)
    (R : AnLogRes P J (n + 1)) (L : Fin n → HermLine ι) (A B : HermLine ι) (s : MRing ι)
    (r : ℕ) (m : Fin r → ℕ) (W : Fin r → Set R.X) (BW : ∀ k, FinHolAtlas n (W k))
    (Ψ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (n + 1) → ℂ)),
    IsArithVar P (n + 2) → (∀ j, IsSmoothHerm (L j)) → IsSmoothHerm A → IsSmoothHerm B →
    B.a = 0 → IsSectionOn P A s →
    IsSNC R.A (potOf R A) (fun x y => eval (R.lift x y) (map (Int.castRingHom ℂ) s)) m W →
    (∀ k, HoloMap (BW k) R.A Subtype.val) →
    (∀ W' ∈ divSupp P s, IsHorizontal W' → IsGoodProj W' Ψ) →
    ∀ᵐ y, ∑ k, (m k : ℝ) * divFib R L B Ψ (BW k) y =
      ∑ᶠ (W') (_ : W' ∈ divSupp P s ∧ IsHorizontal W'),
        (multAt (P ⊔ Ideal.span {s}) W' : ℝ) *
          ∑ᶠ w ∈ fibre W' Ψ y, sheetDensity W' Ψ (pot L) (fun z => Real.log (B.h z)) y w
end ReciprocityTheory.ChartRestriction.G.Geo


