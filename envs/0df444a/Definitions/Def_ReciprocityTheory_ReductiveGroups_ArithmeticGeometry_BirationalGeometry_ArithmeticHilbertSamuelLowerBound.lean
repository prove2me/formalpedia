-- Prove2me | Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ArithmeticHilbertSamuelLowerBound
-- name    : ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ArithmeticHilbertSamuelLowerBound
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T23:26:56.210265+00:00
-- url     : https://prove2.me/theorems/0ec1bf0c-ed2b-4945-8622-f80fdfc93b83
-- title:
--   Arithmetic Hilbert Samuel Lower Bound
-- statement:
--   Definitions and structural lemmas for Arithmetic Hilbert Samuel Lower Bound, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/BirationalGeometry/ArithmeticHilbertSamuelLowerBound.lean

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_IsIntersectionFamily
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_PenVol
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
open MvPolynomial Filter
section Defs
variable {K : Type*} [Fintype K] {ι : K → Type*} [∀ k, Fintype (ι k)] {Ω : Type*} [Field Ω]
def mConeMap (y : (Σ k, ι k) → Ω) : MRing ι →ₐ[ℤ] MvPolynomial K Ω :=
  aeval fun p => MvPolynomial.C (y p) * MvPolynomial.X p.1
def mCoordIdeal (y : (Σ k, ι k) → Ω) : Ideal (MRing ι) :=
  RingHom.ker (mConeMap y)
def IsSmallH (P : Ideal (MRing ι)) (y : (Σ k, ι k) → Ω) (A : HermLine ι) (τ : ℕ) (s : Ω) : Prop :=
  ∀ (dg dh : K → ℕ) (g h : MRing ι) (z : (Σ k, ι k) → ℂ),
    IsMultiHomog g dg → IsMultiHomog h dh → (∀ k, (dg k : ℤ) = dh k + τ * A.a k) →
    aeval y g = s * aeval y h → z ∈ mcPts P →
    ‖eval z (map (Int.castRingHom ℂ) g)‖ ≤ ‖eval z (map (Int.castRingHom ℂ) h)‖ * A.h z ^ τ
def Birational (y : (Σ k, ι k) → Ω) : Prop :=
  ∀ s : Ω, ∃ (d : K → ℕ) (g h : MRing ι), IsMultiHomog g d ∧ IsMultiHomog h d ∧
    aeval y h ≠ 0 ∧ aeval y g = s * aeval y h
def chartRingZ (y : (Σ k, ι k) → Ω) (c : ∀ k, ι k) : Subalgebra ℤ Ω :=
  Algebra.adjoin ℤ (Set.range fun p : Σ k, ι k => y p / y ⟨p.1, c p.1⟩)
def SmoothGenericFibreM [Algebra ℚ Ω] (y : (Σ k, ι k) → Ω) : Prop :=
  ∀ c : ∀ k, ι k, (∀ k, y ⟨k, c k⟩ ≠ 0) →
    Algebra.Smooth ℚ (Algebra.adjoin ℚ (Set.range fun p : Σ k, ι k => y p / y ⟨p.1, c p.1⟩))
def IsSemipositiveRel (P0 P : Ideal (MRing ι)) (A : HermLine ι) : Prop :=
  IsSmoothHerm A ∧ ∀ z ∈ mcPts P, ∀ w, IsConeTangent (Int.castRingHom ℂ) P0 z w →
    0 ≤ leviForm (fun z => Real.log (A.h z)) z w
def IsSemipositiveH (P : Ideal (MRing ι)) (A : HermLine ι) : Prop :=
  IsSemipositiveRel P P A
def IsConjInvariantH (A : HermLine ι) : Prop :=
  ∀ z : (Σ k, ι k) → ℂ, A.h (fun p => (starRingEnd ℂ) (z p)) = A.h z
def NefOnFibres (P : Ideal (MRing ι)) (a : K → ℤ) : Prop :=
  ∀ W : Ideal (MRing ι), IsMultiProjPrime W → P ≤ W → charOf W ≠ 0 →
    ringKrullDim (MRing ι ⧸ W) = ((1 + Fintype.card K : ℕ) : WithBot ℕ∞) →
    0 ≤ geoNum 1 W (fun _ => a)
def secM (y : (Σ k, ι k) → Ω) (d : K → ℕ) : AddSubgroup Ω :=
  (Submodule.span ℤ {s | ∃ g : MRing ι, IsMultiHomog g d ∧ aeval y g = s}).toAddSubgroup
def chartLat (y : (Σ k, ι k) → Ω) (a : K → ℤ) (τ : ℕ) : AddSubgroup Ω where
  carrier := {s | ∀ c : ∀ k, ι k, (∀ k, y ⟨k, c k⟩ ≠ 0) →
    s * ∏ k, y ⟨k, c k⟩ ^ (-((τ : ℤ) * a k)) ∈ chartRingZ y c}
  zero_mem' := fun c _ => by simp
  add_mem' := fun {s t} hs ht c hc => by rw [add_mul]; exact add_mem (hs c hc) (ht c hc)
  neg_mem' := fun {s} hs c hc => by rw [neg_mul]; exact neg_mem (hs c hc)
def chartLatNm (y : (Σ k, ι k) → Ω) (a : K → ℤ) (τ : ℕ) : AddSubgroup Ω where
  carrier := {s | ∀ c : ∀ k, ι k, (∀ k, y ⟨k, c k⟩ ≠ 0) →
    s * ∏ k, y ⟨k, c k⟩ ^ (-((τ : ℤ) * a k)) ∈ integralClosure (chartRingZ y c) Ω}
  zero_mem' := fun c _ => by simp
  add_mem' := fun {s t} hs ht c hc => by rw [add_mul]; exact add_mem (hs c hc) (ht c hc)
  neg_mem' := fun {s} hs c hc => by rw [neg_mul]; exact neg_mem (hs c hc)
def degC (W : Ideal (MRing ι)) : ℕ :=
  Nat.card (Quot fun z z' : mcPts W =>
    ∃ c : K → ℂ, (∀ k, c k ≠ 0) ∧ (z' : (Σ k, ι k) → ℂ) = fun p => c p.1 * (z : (Σ k, ι k) → ℂ) p)
def geomDeg (P : Ideal (MRing ι)) (A : HermLine ι) (D : ℕ) : ℝ :=
  ptsIntegral (e := D) P (fun _ z => Real.log (A.h z)) (fun _ => 1)
def MonomialsBounded (P : Ideal (MRing ι)) (A : HermLine ι) (a : K → ℕ) : Prop :=
  ∀ z ∈ mcPts P, ∀ μ : (Σ k, ι k) →₀ ℕ, (∀ k, ∑ i, μ ⟨k, i⟩ = a k) → ‖∏ p, z p ^ μ p‖ ≤ A.h z
def IsZariskiDense (P : Ideal (MRing ι)) (F : Set (Ideal (MRing ι))) : Prop :=
  ∀ f : MRing ι, (∃ a, IsMultiHomog f a) → f ∉ P → ∃ W ∈ F, f ∉ W
end Defs
section Statements
def IntersectionSystem : Type 1 :=
  ∀ (K' : Type) [Fintype K'] (ι' : K' → Type) [∀ k, Fintype (ι' k)],
    Ideal (MRing ι') → (n : ℕ) → (Fin n → HermLine ι') → ℝ
def IsIntersectionSystem (II : IntersectionSystem) : Prop :=
  ∀ (K' : Type) [Fintype K'] (ι' : K' → Type) [∀ k, Fintype (ι' k)], IsIntersectionFamily (II K' ι')
def PackingStatement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω]
    (y : (Σ k, ι k) → Ω) (D : ℕ) (A : HermLine ι) (La : ℕ → AddSubgroup Ω),
    IsArithVar (mCoordIdeal y) (D + 1) → Birational y → IsSmoothHerm A →
    (∀ τ, La τ ≤ chartLatNm y A.a τ) →
    (∀ τ, {s : La τ | IsSmallH (mCoordIdeal y) y A τ (s : Ω)}.Finite) ∧
      ∃ C : ℝ, ∀ τ, smallSectionCount (IsSmallH (mCoordIdeal y) y A) La τ ≤ C * ((τ : ℝ) + 1) ^ (D + 1)
def ArithmeticHilbertSamuelLowerBound : Prop :=
  ∀ (ι0 : Type) [Fintype ι0] (Ω : Type) [Field Ω] [Algebra ℚ Ω] (x : ι0 → Ω) (D : ℕ)
    (A : HermLine (fun _ : Unit => ι0))
    (II : IntersectionSystem),
    1 ≤ D → IsIntersectionSystem II → A.a = 1 →
    IsArithVar (mCoordIdeal (fun p : Σ _ : Unit, ι0 => x p.2)) (D + 1) →
    Birational (fun p : Σ _ : Unit, ι0 => x p.2) →
    SmoothGenericFibreM (fun p : Σ _ : Unit, ι0 => x p.2) →
    IsSemipositiveH (mCoordIdeal (fun p : Σ _ : Unit, ι0 => x p.2)) A → IsConjInvariantH A →
    II Unit (fun _ => ι0) (mCoordIdeal (fun p : Σ _ : Unit, ι0 => x p.2)) (D + 1) (fun _ => A) ≤
      liminf (fun τ : ℕ =>
        smallSectionCount (IsSmallH (mCoordIdeal (fun p : Σ _ : Unit, ι0 => x p.2)) (fun p => x p.2) A)
          (fun τ => secM (fun p : Σ _ : Unit, ι0 => x p.2) (fun _ => τ)) τ /
          ((τ : ℝ) ^ (D + 1) / ((D + 1).factorial : ℝ))) atTop
def ArithmeticVolumeLowerBound : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω] [Algebra ℚ Ω]
    (y : (Σ k, ι k) → Ω) (D : ℕ) (A : HermLine ι)
    (II : IntersectionSystem),
    1 ≤ D → IsIntersectionSystem II → IsArithVar (mCoordIdeal y) (D + 1) → Birational y →
    SmoothGenericFibreM y → IsSemipositiveH (mCoordIdeal y) A → NefOnFibres (mCoordIdeal y) A.a →
    IsConjInvariantH A →
    II K ι (mCoordIdeal y) (D + 1) (fun _ => A) ≤
      arVolP (IsSmallH (mCoordIdeal y) y A) (chartLat y A.a) 1 D
def BirationalPullbackPushforwardFormula : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω]
    (y : (Σ k, ι k) → Ω) (D : ℕ) (A : HermLine ι) (P0 : Ideal (MRing ι)) (II : IntersectionSystem),
    1 ≤ D → IsIntersectionSystem II → IsArithVar (mCoordIdeal y) (D + 1) → Birational y →
    P0 ≤ mCoordIdeal y → IsSemipositiveRel P0 (mCoordIdeal y) A → NefOnFibres (mCoordIdeal y) A.a →
    IsConjInvariantH A →
    II K ι (mCoordIdeal y) (D + 1) (fun _ => A) ≤
      arVolP (IsSmallH (mCoordIdeal y) y A) (chartLatNm y A.a) 1 D
def ArithmeticHilbertSamuelUpperBound : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω]
    (y : (Σ k, ι k) → Ω) (D : ℕ) (a : K → ℕ) (A : HermLine ι) (P0 : Ideal (MRing ι))
    (II : IntersectionSystem),
    1 ≤ D → IsIntersectionSystem II → IsArithVar (mCoordIdeal y) (D + 1) → Birational y →
    (A.a = fun k => (a k : ℤ)) → P0 ≤ mCoordIdeal y → IsSemipositiveRel P0 (mCoordIdeal y) A →
    MonomialsBounded (mCoordIdeal y) A a → IsConjInvariantH A →
    limsup (fun τ : ℕ =>
        smallSectionCount (IsSmallH (mCoordIdeal y) y A) (chartLatNm y A.a) τ /
          ((τ : ℝ) ^ (D + 1) / ((D + 1).factorial : ℝ))) atTop ≤
      II K ι (mCoordIdeal y) (D + 1) (fun _ => A)
def ArithmeticIntersectionNonneg : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω]
    (y : (Σ k, ι k) → Ω) (D : ℕ) (a : K → ℕ) (A : HermLine ι) (P0 : Ideal (MRing ι))
    (II : IntersectionSystem),
    1 ≤ D → IsIntersectionSystem II → IsArithVar (mCoordIdeal y) (D + 1) → Birational y →
    (A.a = fun k => (a k : ℤ)) → P0 ≤ mCoordIdeal y → IsSemipositiveRel P0 (mCoordIdeal y) A →
    MonomialsBounded (mCoordIdeal y) A a → IsConjInvariantH A →
    0 ≤ II K ι (mCoordIdeal y) (D + 1) (fun _ => A)
def SuccessiveMinimaLowerBound : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (P P0 : Ideal (MRing ι)) (D : ℕ)
    (A : HermLine ι) (e : ℝ) (II : IntersectionSystem),
    IsIntersectionSystem II → IsArithVar P (D + 1) → P0 ≤ P → IsSemipositiveRel P0 P A →
    NefOnFibres P A.a → IsConjInvariantH A →
    (∀ W, IsArithVar W 1 → P ≤ W → e * degC W ≤ II K ι W 1 ![A]) →
    ((D + 1 : ℕ) : ℝ) * e * geomDeg P A D ≤ II K ι P (D + 1) (fun _ => A)
def SuccessiveMinimaUpperBound : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (P P0 : Ideal (MRing ι)) (D : ℕ)
    (A : HermLine ι) (e' : ℝ) (F : Set (Ideal (MRing ι)))
    (II : IntersectionSystem),
    IsIntersectionSystem II → IsArithVar P (D + 1) → P0 ≤ P → IsSemipositiveRel P0 P A →
    NefOnFibres P A.a → IsConjInvariantH A →
    (∀ W ∈ F, IsArithVar W 1 ∧ P ≤ W ∧ II K ι W 1 ![A] ≤ e' * degC W) → IsZariskiDense P F →
    II K ι P (D + 1) (fun _ => A) ≤ ((D + 1 : ℕ) : ℝ) * e' * geomDeg P A D
end Statements
end ReciprocityTheory.ChartRestriction.G.Geo


