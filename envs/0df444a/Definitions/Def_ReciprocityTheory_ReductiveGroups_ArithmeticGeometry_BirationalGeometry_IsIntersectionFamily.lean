-- Prove2me | Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_IsIntersectionFamily
-- name    : ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_IsIntersectionFamily
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T23:19:07.345182+00:00
-- url     : https://prove2.me/theorems/da77b855-f078-453d-9bd1-4aeb0ab86bcb
-- title:
--   Is Intersection Family
-- statement:
--   Definitions and structural lemmas for Is Intersection Family, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/BirationalGeometry/IsIntersectionFamily.lean

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_IsSemipositiveOn
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
open MvPolynomial MeasureTheory Filter Topology
variable {K : Type*} [Fintype K] {ι : K → Type*} [∀ k, Fintype (ι k)]
section Algebra
abbrev MRingOver (R : Type*) [CommRing R] (ι : K → Type*) := MvPolynomial (Σ k, ι k) R
abbrev MRing (ι : K → Type*) := MRingOver ℤ ι
variable {R : Type*} [CommRing R]
def IsMultiHomog (s : MRingOver R ι) (a : K → ℕ) : Prop :=
  ∀ m ∈ s.support, ∀ k, ∑ i, m ⟨k, i⟩ = a k
def IsMultiHomogIdeal (P : Ideal (MRingOver R ι)) : Prop :=
  ∃ S : Set (MRingOver R ι), (∀ f ∈ S, ∃ a, IsMultiHomog f a) ∧ P = Ideal.span S
def IsRelevant (W : Ideal (MRingOver R ι)) : Prop :=
  ∀ k, ∃ i, (X ⟨k, i⟩ : MRingOver R ι) ∉ W
def IsMultiProjPrime (P : Ideal (MRingOver R ι)) : Prop :=
  P.IsPrime ∧ IsMultiHomogIdeal P ∧ IsRelevant P
def IsHorizontal (P : Ideal (MRing ι)) : Prop :=
  P.comap (C : ℤ →+* MRing ι) = ⊥
def IsArithVar (P : Ideal (MRing ι)) (d : ℕ) : Prop :=
  Nonempty K ∧ IsMultiProjPrime P ∧ IsHorizontal P ∧
    ringKrullDim (MRing ι ⧸ P) = ((d + Fintype.card K : ℕ) : WithBot ℕ∞)
def divSupp (P : Ideal (MRingOver R ι)) (s : MRingOver R ι) : Set (Ideal (MRingOver R ι)) :=
  {W | W ∈ (P ⊔ Ideal.span {s}).minimalPrimes ∧ IsRelevant W}
open Classical in

def multAt (J W : Ideal (MRingOver R ι)) : ℕ :=
  if h : W.IsPrime then
    haveI := h
    (Module.length (Localization.AtPrime W) (LocalizedModule W.primeCompl (MRingOver R ι ⧸ J))).toNat
  else 0
theorem divSupp_finite [IsNoetherianRing R] (P : Ideal (MRingOver R ι)) (s : MRingOver R ι) : (divSupp P s).Finite :=
  (Ideal.finite_minimalPrimes_of_isNoetherianRing _ (P ⊔ Ideal.span {s})).subset fun _ hW => hW.1
def divCycle [IsNoetherianRing R] (P : Ideal (MRingOver R ι)) (s : MRingOver R ι) :
    Ideal (MRingOver R ι) →₀ ℕ := by
  classical
  exact Finsupp.ofSupportFinite
    (fun W => if W ∈ divSupp P s then multAt (P ⊔ Ideal.span {s}) W else 0)
    ((divSupp_finite P s).subset fun W hW => by
      by_contra h
      exact hW (if_neg h))
def charOf (W : Ideal (MRing ι)) : ℕ :=
  (Submodule.IsPrincipal.generator (W.comap (C : ℤ →+* MRing ι))).natAbs
open Classical in

def geoNum : (n : ℕ) → Ideal (MRing ι) → (Fin n → K → ℤ) → ℤ
  | 0, V, _ =>
    if h : IsRelevant V then
      ((Module.length ℤ
        (MRing ι ⧸ (V ⊔ Ideal.span (Set.range fun k => (X ⟨k, (h k).choose⟩ : MRing ι) - 1)))).toNat : ℤ)
    else 0
  | n + 1, V, a =>
    if h : IsRelevant V then
      ∑ k, a (Fin.last n) k *
        ∑ᶠ W ∈ divSupp V (X ⟨k, (h k).choose⟩),
          (multAt (V ⊔ Ideal.span {(X ⟨k, (h k).choose⟩ : MRing ι)}) W : ℤ) * geoNum n W (Fin.init a)
    else 0
end Algebra
section Complex
def mcPts (P : Ideal (MRing ι)) : Set ((Σ k, ι k) → ℂ) :=
  {z | (∀ k, ∃ i, z ⟨k, i⟩ ≠ 0) ∧ ∀ f ∈ P, eval z (map (Int.castRingHom ℂ) f) = 0}
variable (ι) in

structure HermLine where

  a : K → ℤ

  h : ((Σ k, ι k) → ℂ) → ℝ
  pos : ∀ z : (Σ k, ι k) → ℂ, (∀ k, ∃ i, z ⟨k, i⟩ ≠ 0) → 0 < h z
  smul : ∀ (c : K → ℂ) (z : (Σ k, ι k) → ℂ), (∀ k, c k ≠ 0) →
    h (fun p => c p.1 * z p) = (∏ k, ‖c k‖ ^ a k) * h z
def IsSmoothHerm (A : HermLine ι) : Prop :=
  ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) A.h {z | ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0}
def HermLine.tensor (A B : HermLine ι) : HermLine ι where
  a := A.a + B.a
  h z := A.h z * B.h z
  pos z hz := mul_pos (A.pos z hz) (B.pos z hz)
  smul c z hc := by
    rw [A.smul c z hc, B.smul c z hc]
    have : ∀ k, ‖c k‖ ^ (A.a + B.a) k = ‖c k‖ ^ A.a k * ‖c k‖ ^ B.a k := fun k =>
      zpow_add₀ (norm_ne_zero_iff.mpr (hc k)) _ _
    simp only [this, Finset.prod_mul_distrib]
    ring
def segre (z : (Σ k, ι k) → ℂ) : ((k : K) → ι k) → ℂ :=
  fun i => ∏ k, z ⟨k, i k⟩
variable {e : ℕ}
def fibre (P : Ideal (MRing ι)) (Ψ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (e + 1) → ℂ))
    (y : Fin e → ℂ) : Set (((k : K) → ι k) → ℂ) :=
  {w | ∃ z ∈ mcPts P, segre z = w ∧ Ψ w = Fin.cons 1 y}
def IsSheet (P : Ideal (MRing ι)) (Ψ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (e + 1) → ℂ))
    (y : Fin e → ℂ) (w : ((k : K) → ι k) → ℂ) (γ : (Fin e → ℂ) → (Σ k, ι k) → ℂ) : Prop :=
  segre (γ y) = w ∧ ∀ᶠ y' in 𝓝 y,
    DifferentiableAt ℂ γ y' ∧ γ y' ∈ mcPts P ∧ Ψ (segre (γ y')) = Fin.cons 1 y'
def sheetDensity (P : Ideal (MRing ι)) (Ψ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (e + 1) → ℂ))
    (φ : Fin e → ((Σ k, ι k) → ℂ) → ℝ) (g : ((Σ k, ι k) → ℂ) → ℝ) (y : Fin e → ℂ)
    (w : ((k : K) → ι k) → ℂ) : ℝ := by
  classical
  exact if hγ : ∃ γ, IsSheet P Ψ y w γ then
    g (hγ.choose y) * maDensity (fun j y' => φ j (hγ.choose y')) y
  else 0
def ptsIntegralAt (P : Ideal (MRing ι)) (Ψ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (e + 1) → ℂ))
    (φ : Fin e → ((Σ k, ι k) → ℂ) → ℝ) (g : ((Σ k, ι k) → ℂ) → ℝ) : ℝ :=
  ∫ y, ∑ᶠ w ∈ fibre P Ψ y, sheetDensity P Ψ φ g y w
def IsGoodProj (P : Ideal (MRing ι)) (Ψ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (e + 1) → ℂ)) : Prop :=
  ∀ z ∈ mcPts P, Ψ (segre z) ≠ 0
def ptsIntegral (P : Ideal (MRing ι)) (φ : Fin e → ((Σ k, ι k) → ℂ) → ℝ)
    (g : ((Σ k, ι k) → ℂ) → ℝ) : ℝ := by
  classical
  exact if hΨ : ∃ Ψ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (e + 1) → ℂ), IsGoodProj P Ψ then
    ptsIntegralAt P hΨ.choose φ g
  else 0
def logNorm (A : HermLine ι) (s : MRing ι) (z : (Σ k, ι k) → ℂ) : ℝ :=
  Real.log (‖eval z (map (Int.castRingHom ℂ) s)‖ / A.h z)
def arInt (P : Ideal (MRing ι)) (s : MRing ι) (A : HermLine ι) (L : Fin e → HermLine ι) : ℝ :=
  ptsIntegral P (fun j z => Real.log ((L j).h z)) (logNorm A s)
end Complex
section Constructors
def HermLine.ofMetrics (m : ∀ k, ConeMetric ℂ (ι k)) (a : K → ℤ) : HermLine ι where
  a := a
  h z := ∏ k, (m k).ρ (fun i => z ⟨k, i⟩) ^ a k
  pos z hz := Finset.prod_pos fun k _ => by
    obtain ⟨i, hi⟩ := hz k
    exact zpow_pos ((m k).pos _ fun h0 => hi (congrFun h0 i)) _
  smul c z hc := by
    rw [← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun k _ => ?_
    have : (fun i => c k * z ⟨k, i⟩) = c k • fun i => z ⟨k, i⟩ := rfl
    simp only [this, (m k).smul, mul_zpow]
def HermLine.ofWeight (u : ((Σ k, ι k) → ℂ) → ℝ)
    (hu : ∀ (c : K → ℂ) z, (∀ k, c k ≠ 0) → u (fun p => c p.1 * z p) = u z) : HermLine ι where
  a := 0
  h z := Real.exp (-u z)
  pos _ _ := Real.exp_pos _
  smul c z hc := by simp [hu c z hc]
end Constructors
section Family
def recR (I : Ideal (MRing ι) → (n : ℕ) → (Fin n → HermLine ι) → ℝ) (P : Ideal (MRing ι)) {n : ℕ}
    (L : Fin n → HermLine ι) (A : HermLine ι) (s : MRing ι) : ℝ := by
  classical
  exact (∑ᶠ W ∈ divSupp P s, (multAt (P ⊔ Ideal.span {s}) W : ℝ) *
      (if IsHorizontal W then I W n L
        else (geoNum n W (fun j => (L j).a) : ℝ) * Real.log (charOf W))) -
    arInt P s A L
def IsIntersectionFamily (I : Ideal (MRing ι) → (n : ℕ) → (Fin n → HermLine ι) → ℝ) : Prop :=
  (∀ P n (L : Fin n → HermLine ι) (σ : Equiv.Perm (Fin n)), IsArithVar P n →
      (∀ j, IsSmoothHerm (L j)) → I P n (L ∘ σ) = I P n L) ∧
  (∀ P n (L : Fin n → HermLine ι) (A B : HermLine ι), IsArithVar P (n + 1) →
      (∀ j, IsSmoothHerm (L j)) → IsSmoothHerm A → IsSmoothHerm B →
      I P (n + 1) (Fin.snoc L (A.tensor B)) =
        I P (n + 1) (Fin.snoc L A) + I P (n + 1) (Fin.snoc L B)) ∧
  (∀ P n (L : Fin n → HermLine ι) (A : HermLine ι) (s : MRing ι) (a : K → ℕ),
      IsArithVar P (n + 1) → (∀ j, IsSmoothHerm (L j)) → IsSmoothHerm A →
      (∀ k, A.a k = a k) → IsMultiHomog s a → s ∉ P →
      I P (n + 1) (Fin.snoc L A) = recR I P L A s)
end Family
end ReciprocityTheory.ChartRestriction.G.Geo


