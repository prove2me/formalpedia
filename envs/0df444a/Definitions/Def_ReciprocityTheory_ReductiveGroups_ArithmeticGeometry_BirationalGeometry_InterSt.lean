-- Prove2me | Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterSt
-- name    : ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterSt
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T23:25:44.898682+00:00
-- url     : https://prove2.me/theorems/23f7693a-098a-44b7-8b24-9fff47ce86e4
-- title:
--   Inter St
-- statement:
--   Definitions and structural lemmas for Inter St, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/BirationalGeometry/InterSt.lean

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_IsIntersectionFamily
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
open MvPolynomial MeasureTheory
def pot {K : Type*} [Fintype K] {ι : K → Type*} [∀ k, Fintype (ι k)] {e : ℕ} (L : Fin e → HermLine ι) :
    Fin e → ((Σ k, ι k) → ℂ) → ℝ :=
  fun j z => Real.log ((L j).h z)
def IsSectionOn {K : Type*} [Fintype K] {ι : K → Type*} [∀ k, Fintype (ι k)] (P : Ideal (MRing ι)) (A : HermLine ι) (s : MRing ι) :
    Prop :=
  ∃ a : K → ℕ, (∀ k, A.a k = a k) ∧ IsMultiHomog s a ∧ s ∉ P
def GoodProjExistsStatement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (P : Ideal (MRing ι)) (e : ℕ),
    IsArithVar P (e + 1) → ∃ Ψ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (e + 1) → ℂ), IsGoodProj P Ψ
def FibreFiniteStatement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (P : Ideal (MRing ι)) (e : ℕ)
    (Ψ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (e + 1) → ℂ)),
    IsArithVar P (e + 1) → IsGoodProj P Ψ → ∀ y, (fibre P Ψ y).Finite
def PtsIntegrableStatement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (P : Ideal (MRing ι)) (e : ℕ)
    (Ψ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (e + 1) → ℂ)) (L : Fin e → HermLine ι) (A : HermLine ι)
    (s : MRing ι),
    IsArithVar P (e + 1) → IsGoodProj P Ψ → (∀ j, IsSmoothHerm (L j)) → IsSmoothHerm A →
    IsSectionOn P A s →
    Integrable (fun y => ∑ᶠ w ∈ fibre P Ψ y, sheetDensity P Ψ (pot L) (logNorm A s) y w)
def PtsIndepStatement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (P : Ideal (MRing ι)) (e : ℕ)
    (Ψ Ψ' : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (e + 1) → ℂ)) (L : Fin e → HermLine ι)
    (A : HermLine ι) (s : MRing ι),
    IsArithVar P (e + 1) → IsGoodProj P Ψ → IsGoodProj P Ψ' → (∀ j, IsSmoothHerm (L j)) →
    IsSmoothHerm A → IsSectionOn P A s →
    ptsIntegralAt P Ψ (pot L) (logNorm A s) = ptsIntegralAt P Ψ' (pot L) (logNorm A s)
def DivSuppArithStatement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (P : Ideal (MRing ι)) (n : ℕ)
    (A : HermLine ι) (s : MRing ι) (W : Ideal (MRing ι)),
    IsArithVar P (n + 1) → IsSectionOn P A s → W ∈ divSupp P s →
    (IsHorizontal W → IsArithVar W n) ∧
    (¬ IsHorizontal W → IsMultiProjPrime W ∧ (charOf W).Prime ∧
      ringKrullDim (MRing ι ⧸ W) = ((n + Fintype.card K : ℕ) : WithBot ℕ∞))
def SheetIndepStatement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (P : Ideal (MRing ι)) (e : ℕ)
    (Ψ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (e + 1) → ℂ)) (L : Fin e → HermLine ι) (A : HermLine ι)
    (s : MRing ι),
    IsArithVar P (e + 1) → IsGoodProj P Ψ → (∀ j, IsSmoothHerm (L j)) → IsSmoothHerm A →
    IsSectionOn P A s →
    ∀ᵐ y, ∀ w γ γ', IsSheet P Ψ y w γ → IsSheet P Ψ y w γ' →
      logNorm A s (γ y) * maDensity (fun j y' => pot L j (γ y')) y =
        logNorm A s (γ' y) * maDensity (fun j y' => pot L j (γ' y')) y
def DegreeStatement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (P : Ideal (MRing ι)) (e : ℕ)
    (L : Fin e → HermLine ι) (p : ℕ),
    IsArithVar P (e + 1) → (∀ j, IsSmoothHerm (L j)) → p.Prime →
    ptsIntegral P (pot L) (fun _ => 1) =
      ∑ᶠ V ∈ divSupp P (C (p : ℤ)),
        (multAt (P ⊔ Ideal.span {C (p : ℤ)}) V : ℝ) * (geoNum e V (fun j => (L j).a) : ℝ)
def StokesStatement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (P : Ideal (MRing ι)) (n : ℕ)
    (L : Fin n → HermLine ι) (B B' : HermLine ι),
    IsArithVar P (n + 2) → (∀ j, IsSmoothHerm (L j)) → IsSmoothHerm B → IsSmoothHerm B' →
    B.a = 0 → B'.a = 0 →
    ptsIntegral P (Fin.cons (fun z => Real.log (B'.h z)) (pot L)) (fun z => Real.log (B.h z)) =
      ptsIntegral P (Fin.cons (fun z => Real.log (B.h z)) (pot L)) (fun z => Real.log (B'.h z))
def ArithmeticPoincareLelongFormula : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (P : Ideal (MRing ι)) (n : ℕ)
    (L : Fin n → HermLine ι) (A B : HermLine ι) (s : MRing ι),
    IsArithVar P (n + 2) → (∀ j, IsSmoothHerm (L j)) → IsSmoothHerm A → IsSmoothHerm B →
    B.a = 0 → IsSectionOn P A s →
    ptsIntegral P (Fin.cons (fun z => Real.log (B.h z)) (pot L)) (logNorm A s) =
      (∑ᶠ (W) (_ : W ∈ divSupp P s ∧ IsHorizontal W),
          (multAt (P ⊔ Ideal.span {s}) W : ℝ) * ptsIntegral W (pot L) (fun z => Real.log (B.h z))) -
        ptsIntegral P (Fin.cons (fun z => Real.log (A.h z)) (pot L)) (fun z => Real.log (B.h z))
def SectionSpaceSymmetry : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (P : Ideal (MRing ι)) (n : ℕ)
    (L : Fin n → HermLine ι) (A A' : HermLine ι) (s s' : MRing ι),
    IsArithVar P (n + 2) → (∀ j, IsSmoothHerm (L j)) → IsSmoothHerm A → IsSmoothHerm A' →
    IsSectionOn P A s → IsSectionOn P A' s' →
    (∀ W, W ∈ divSupp P s → W ∈ divSupp P s' → ¬ IsHorizontal W) →
    (∑ᶠ (W) (_ : W ∈ divSupp P s ∧ IsHorizontal W),
        (multAt (P ⊔ Ideal.span {s}) W : ℝ) * ptsIntegral W (pot L) (logNorm A' s')) +
      ptsIntegral P (Fin.cons (fun z => Real.log (A'.h z)) (pot L)) (logNorm A s) =
    (∑ᶠ (W) (_ : W ∈ divSupp P s' ∧ IsHorizontal W),
        (multAt (P ⊔ Ideal.span {s'}) W : ℝ) * ptsIntegral W (pot L) (logNorm A s)) +
      ptsIntegral P (Fin.cons (fun z => Real.log (A.h z)) (pot L)) (logNorm A' s')
section Tests
abbrev PBlk (n : ℕ) : Unit → Type := fun _ => Fin n
def fsLine (n : ℕ) : HermLine (PBlk n) :=
  HermLine.ofMetrics (fun _ => fsMetric (Fin n)) 1
abbrev Xc (n : ℕ) (i : Fin n) : MRing (PBlk n) := X ⟨(), i⟩
def ArithVarTestStatement : Prop :=
  IsArithVar (⊥ : Ideal (MRing (PBlk 2))) 2 ∧
    IsArithVar (Ideal.span {Xc 2 1 - 2 * Xc 2 0}) 1 ∧
    IsArithVar (Ideal.span {Xc 3 2}) 2
def ProjectiveLineHeightIntegral : Prop :=
  arInt (⊥ : Ideal (MRing (PBlk 2))) (Xc 2 0) (fsLine 2) ![fsLine 2] = -1 / 2
def PointTestStatement : Prop :=
  arInt (Ideal.span {Xc 2 1 - 2 * Xc 2 0}) (Xc 2 0) (fsLine 2) ![] = -Real.log 5 / 2
def LineTestStatement : Prop :=
  ptsIntegral (Ideal.span {Xc 3 2}) (pot ![fsLine 3]) (fun _ => 1) = 1
end Tests
end ReciprocityTheory.ChartRestriction.G.Geo


