-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_BundleObjects
-- name    : GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_BundleObjects
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T23:52:18.327134+00:00
-- url     : https://prove2.me/theorems/4d42114c-06f3-4179-a739-6324c6da8456
-- title:
--   Bundle Objects
-- statement:
--   Definitions and structural lemmas for Bundle Objects, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/BundleObjects.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_Objects
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_Bundle
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
namespace GroundTheory.Heights₂.Heights.NumbersDVR
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo
noncomputable section
section Point
variable {K : Type*} {ι : K → Type*} {Ω : Type*} [Field Ω]
def pointConeMap (R : Type*) [CommRing R] [Algebra R Ω] (y : (Σ k, ι k) → Ω) :
    MRing ι R →ₐ[R] MvPolynomial K Ω :=
  aeval fun p => C (y p) * X p.1
def pointIdeal (R : Type*) [CommRing R] [Algebra R Ω] (y : (Σ k, ι k) → Ω) : Ideal (MRing ι R) :=
  RingHom.ker (pointConeMap R y)
end Point
section Generic
variable {K : Type*} (R : Type*) [CommRing R] [IsDomain R] (ι : K → Type*)
def genericPt : (Σ k, ι k) → FractionRing (MRing ι R) :=
  fun p => algebraMap (MRing ι R) (FractionRing (MRing ι R)) (X p)
end Generic
section Charts
variable {K : Type*} [Fintype K] {ι : K → Type*} {Ω : Type*} [Field Ω]
def segreVec (y : (Σ k, ι k) → Ω) : (∀ k, ι k) → Ω :=
  fun c => ∏ k, y ⟨k, c k⟩
variable (R : Type*) [CommRing R] [Algebra R Ω]
def degLat (y : (Σ k, ι k) → Ω) (b : K → ℤ) (c : ∀ k, ι k) : Set Ω :=
  {s | ∃ a ∈ chartRing R (segreVec y) c, s = a * ∏ k, y ⟨k, c k⟩ ^ b k}
variable {R} {N : ℕ} {E : Type*} [AddCommGroup E] [Module Ω E]
structure IsFlagFrame (y : (Σ k, ι k) → Ω) (B : ChartBundle R (segreVec y) N E)
    (w : Module.Basis (Fin N) Ω E) (b : Fin N → K → ℤ) : Prop where
  graded : ∀ c, segreVec y c ≠ 0 → ∀ i : Fin N,
    {s | ∃ v ∈ B.lat c, (∀ j, i < j → w.repr v j = 0) ∧ w.repr v i = s} = degLat R y (b i) c
structure IsTwistedDualGens (y : (Σ k, ι k) → Ω) (B : ChartBundle R (segreVec y) N E) (a : K → ℤ)
    {M : ℕ} (φ : Fin M → Module.Dual Ω E) : Prop where
  sections : ∀ c, segreVec y c ≠ 0 → ∀ l, ∀ v ∈ B.lat c, φ l v ∈ degLat R y a c
  generate : ∀ c, segreVec y c ≠ 0 → ∀ ψ : Module.Dual Ω E,
    (∀ v ∈ B.lat c, ψ v ∈ chartRing R (segreVec y) c) →
    ∃ u : Fin M → Ω, (∀ l, u l ∈ chartRing R (segreVec y) c) ∧
      ψ = ∑ l, (u l * ∏ k, y ⟨k, c k⟩ ^ (-a k)) • φ l
def SameGenericFibre {τ : Type*} {x : τ → Ω} (ϖ : R) (B B' : ChartBundle R x N E) : Prop :=
  ∀ c, x c ≠ 0 → (∀ v ∈ B.lat c, ∃ n : ℕ, algebraMap R Ω ϖ ^ n • v ∈ B'.lat c) ∧
    (∀ v ∈ B'.lat c, ∃ n : ℕ, algebraMap R Ω ϖ ^ n • v ∈ B.lat c)
end Charts
section ProjBundle
variable {K : Type*} {ι : K → Type} {Ω : Type*} [Field Ω]
def bundleIdx (ι : K → Type) (M : ℕ) : Option K → Type :=
  fun o => Option.elim o (Fin M) ι
instance bundleIdx.fintype [∀ k, Fintype (ι k)] (M : ℕ) : ∀ o, Fintype (bundleIdx ι M o)
  | none => inferInstanceAs (Fintype (Fin M))
  | some k => inferInstanceAs (Fintype (ι k))
variable {N M : ℕ} {E : Type*} [AddCommGroup E] [Module Ω E] {Φ : Type*} [Field Φ] [Algebra Ω Φ]
def projCoord (y : (Σ k, ι k) → Ω) (w : Module.Basis (Fin N) Ω E) (φ : Fin M → Module.Dual Ω E)
    (t : Fin N → Φ) : (Σ o, bundleIdx ι M o) → Φ
  | ⟨none, l⟩ => ∑ i, t i * algebraMap Ω Φ (φ l (w i))
  | ⟨some k, i⟩ => algebraMap Ω Φ (y ⟨k, i⟩)
def projIdeal (F : Type*) [Field F] [Algebra F Ω] (y : (Σ k, ι k) → Ω)
    (w : Module.Basis (Fin N) Ω E) (φ : Fin M → Module.Dual Ω E) (t : Fin N → Φ) :
    Ideal (MRing (bundleIdx ι M) F) :=
  RingHom.ker (eval₂Hom (C.comp ((algebraMap Ω Φ).comp (algebraMap F Ω)))
    (fun p => C (projCoord y w φ t p) * X p.1))
def zetaDeg : Option K → ℤ := fun o => Option.elim o 1 (fun _ => 0)
def liftDeg (L : K → ℤ) : Option K → ℤ := fun o => Option.elim o 0 L
end ProjBundle
section Numbers
variable {K : Type*} [DecidableEq K] {ι : K → Type*}
def intNumL (F : Type*) [Field F] (P : Ideal (MRing ι F)) (l : List (K → ℤ)) : ℤ :=
  intNum F P l.get
def rootList {N : ℕ} (x : Fin N → K → ℤ) (α : Fin N → ℕ) : List (K → ℤ) :=
  (List.finRange N).flatMap fun i => List.replicate (α i) (x i)
def classList {σ : Type*} (cls : σ → K → ℤ) (μ : σ →₀ ℕ) : List (K → ℤ) :=
  (μ.toMultiset.map cls).toList
variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
def vNumL (W : Ideal (MRing ι O)) (l : List (K → ℤ)) : ℤ :=
  vNum W l.get
def classNum {σ : Type*} (cls : σ → K → ℤ) (H : MvPolynomial σ ℤ) (Q : List (K → ℤ))
    (W : Ideal (MRing ι O)) : ℤ :=
  ∑ μ ∈ H.support, H.coeff μ * vNumL W (classList cls μ ++ Q)
structure IsPairExpansion {N : ℕ} (m : ℕ) (G : MvPolynomial (Fin N) ℤ)
    (Gs : Fin N → MvPolynomial (Fin N ⊕ Fin N) ℤ) : Prop where
  expansion : rename Sum.inl G - rename Sum.inr G = ∑ i, (X (Sum.inl i) - X (Sum.inr i)) * Gs i
  homogeneous : ∀ i, (Gs i).IsHomogeneous (m - 1)
def pairNum {N : ℕ} (P : Ideal (MRing ι O)) (x x' : Fin N → K → ℤ) (f g : Fin N → MRing ι O)
    (Gs : Fin N → MvPolynomial (Fin N ⊕ Fin N) ℤ) (Q : List (K → ℤ)) : ℤ :=
  ∑ i, cycEval (fun W => classNum (Sum.elim x x') (Gs i) Q W) (ratDiv P (f i) (g i))
end Numbers
section Pairs
variable {K : Type*} [Fintype K] [DecidableEq K] {ι : K → Type*} {Ω : Type*} [Field Ω]
variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Algebra O Ω]
variable {N : ℕ} {E : Type*} [AddCommGroup E] [Module Ω E]
structure IsFlagPair (ϖ : O) (y : (Σ k, ι k) → Ω) (B B' : ChartBundle O (segreVec y) N E)
    (w w' : Module.Basis (Fin N) Ω E) (x x' : Fin N → K → ℤ) (f g : Fin N → MRing ι O) : Prop where
  flag : IsFlagFrame y B w x
  flag' : IsFlagFrame y B' w' x'
  sameFlag : ∀ i j : Fin N, i < j → w.repr (w' i) j = 0
  vertical : ∀ i, IsVerticalDivisor (pointIdeal O y) ϖ (x i - x' i) (f i) (g i)
  generic : ∀ i, aeval y (f i) = w.repr (w' i) i * aeval y (g i)
end Pairs
section Joins
variable {K K' : Type*} {ι : K → Type} {ι' : K' → Type} {Ω : Type*} [Field Ω]
def joinCoords (y : (Σ k, ι k) → Ω) (y' : (Σ k, ι' k) → Ω) :
    (Σ s : K ⊕ K', Sum.elim ι ι' s) → Ω
  | ⟨Sum.inl k, i⟩ => y ⟨k, i⟩
  | ⟨Sum.inr k, i⟩ => y' ⟨k, i⟩
def joinForm {R : Type*} [CommRing R] (f : MRing ι R) : MRing (Sum.elim ι ι') R :=
  rename (fun p : (Σ k, ι k) => (⟨Sum.inl p.1, p.2⟩ : Σ s : K ⊕ K', Sum.elim ι ι' s)) f
def joinDeg (b : K → ℤ) : K ⊕ K' → ℤ := Sum.elim b 0
def IsBirationalJoin [Fintype K] [Fintype K'] (R : Type*) [CommRing R] [Algebra R Ω]
    (y : (Σ k, ι k) → Ω) (y' : (Σ k, ι' k) → Ω) : Prop :=
  ∀ c, segreVec y c ≠ 0 → ∀ c₁ c₂, segreVec y' c₂ ≠ 0 →
    ∃ a ∈ chartRing R (segreVec y) c, ∃ b ∈ chartRing R (segreVec y) c,
      b ≠ 0 ∧ segreVec y' c₁ * b = a * segreVec y' c₂
end Joins
section GenericJoin
variable {K K' : Type*} (R : Type*) [CommRing R] [IsDomain R] (ι : K → Type) (ι' : K' → Type)
def genericLeft : (Σ k, ι k) → FractionRing (MRing (Sum.elim ι ι') R) :=
  fun p => genericPt R (Sum.elim ι ι') ⟨Sum.inl p.1, p.2⟩
def genericRight : (Σ k, ι' k) → FractionRing (MRing (Sum.elim ι ι') R) :=
  fun p => genericPt R (Sum.elim ι ι') ⟨Sum.inr p.1, p.2⟩
end GenericJoin
section Examples
variable {Ω : Type*} [Field Ω] (R : Type*) [CommRing R] [Algebra R Ω] {τ : Type*}
def scaledTrivLat (x : τ → Ω) (r : ℕ) (s : Ω) (c : τ) : AddSubgroup (Fin r → Ω) where
  carrier := {v | ∀ q, ∃ a ∈ chartRing R x c, v q = s * a}
  add_mem' := by
    intro u v hu hv q
    obtain ⟨a, ha, hua⟩ := hu q
    obtain ⟨b, hb, hvb⟩ := hv q
    exact ⟨a + b, add_mem ha hb, by simp [hua, hvb, mul_add]⟩
  zero_mem' := fun q => ⟨0, zero_mem _, by simp⟩
  neg_mem' := by
    intro v hv q
    obtain ⟨a, ha, hva⟩ := hv q
    exact ⟨-a, neg_mem ha, by simp [hva]⟩
variable {R}
theorem mem_scaledTrivLat {x : τ → Ω} {r : ℕ} {s : Ω} {c : τ} {v : Fin r → Ω} :
    v ∈ scaledTrivLat R x r s c ↔ ∀ q, ∃ a ∈ chartRing R x c, v q = s * a := Iff.rfl
def scaledBasis (r : ℕ) {s : Ω} (hs : s ≠ 0) : Module.Basis (Fin r) Ω (Fin r → Ω) :=
  (Pi.basisFun Ω (Fin r)).unitsSMul fun _ => Units.mk0 s hs
theorem scaledBasis_repr (r : ℕ) {s : Ω} (hs : s ≠ 0) (v : Fin r → Ω) (q : Fin r) :
    (scaledBasis r hs).repr v q = s⁻¹ * v q := by
  simp [scaledBasis, Units.smul_def]
theorem scaledBasis_apply (r : ℕ) {s : Ω} (hs : s ≠ 0) (q : Fin r) :
    scaledBasis r hs q = s • Pi.single q 1 := by
  simp [scaledBasis, Module.Basis.unitsSMul_apply]
variable (R)
def scaledTrivBundle (x : τ → Ω) (r : ℕ) {s : Ω} (hs : s ≠ 0) : ChartBundle R x r (Fin r → Ω) where
  lat := scaledTrivLat R x r s
  stable c a ha v hv q := by
    obtain ⟨b, hb, hvb⟩ := (mem_scaledTrivLat).1 hv q
    exact ⟨a * b, mul_mem ha hb, by simp [hvb]; ring⟩
  frame c hc := by
    refine ⟨1, fun _ => 1, fun _ => 1, fun _ => one_mem _, fun _ => one_mem _, by simp, fun _ => ?_⟩
    refine ⟨scaledBasis r hs, (scaledBasis r hs).linearIndependent, (scaledBasis r hs).span_eq,
      fun e => ?_⟩
    simp only [one_pow, one_smul, one_mul, exists_const]
    constructor
    · intro he
      refine ⟨fun q => s⁻¹ * e q, fun q => ?_, ?_⟩
      · obtain ⟨a, ha, hea⟩ := (mem_scaledTrivLat).1 he q
        show s⁻¹ * e q ∈ _
        rw [hea, ← mul_assoc, inv_mul_cancel₀ hs, one_mul]
        exact ha
      · conv_lhs => rw [← (scaledBasis r hs).sum_repr e]
        simp only [scaledBasis_repr]
    · rintro ⟨a, ha, rfl⟩
      refine (mem_scaledTrivLat).2 fun q => ⟨a q, ha q, ?_⟩
      simp [scaledBasis_apply, Finset.sum_apply, Pi.single_apply, mul_comm]
  overlap c c' hc hc' v hv := by
    choose a ha hva using (mem_scaledTrivLat).1 hv
    have hex : ∀ q, ∃ m : ℕ, (x c / x c') ^ m * a q ∈ chartRing R x c' :=
      fun q => exists_pow_mul_mem_chartRing x c c' hc (ha q)
    choose m hm using hex
    refine ⟨∑ q, m q, (mem_scaledTrivLat).2 fun q => ⟨(x c / x c') ^ (∑ q, m q) * a q, ?_, ?_⟩⟩
    · have hle : m q ≤ ∑ q, m q :=
        Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ q)
      rw [← Nat.sub_add_cancel hle, pow_add, mul_assoc]
      exact mul_mem (pow_mem (div_mem_chartRing x c' c) _) (hm q)
    · simp only [Pi.smul_apply, smul_eq_mul, hva]
      ring
variable {K : Type*} [Fintype K] {ι : K → Type*}
end Examples
end
end GroundTheory.Heights₂.Heights.NumbersDVR


