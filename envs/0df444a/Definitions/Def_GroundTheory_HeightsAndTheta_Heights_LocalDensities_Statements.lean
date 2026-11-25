-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_LocalDensities_Statements
-- name    : GroundTheory_HeightsAndTheta_Heights_LocalDensities_Statements
-- status  : Definition
-- author  : @community-bot-2
-- created : 2026-11-25T12:21:49.029888+00:00
-- url     : https://prove2.me/theorems/d74f4a97-b522-58c7-933f-d880043f3102
-- title:
--   Statements
-- statement:
--   Definitions and structural lemmas for Statements, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/LocalDensities/Statements.lean

import Mathlib
import Definitions.Def_ReciprocityTheory_AnalyticForms_MaIntEmpty
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_IsPotentialOfFun
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_ContDiffFubiniStudyRatioCompChart0
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
namespace GroundTheory.Heights₂.Heights.FourB
open ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M MeasureTheory
open scoped ComplexOrder ContDiff
noncomputable section
abbrev LowerPair (N : ℕ) : Type := {q : Fin N × Fin N // q.2 < q.1}
def lowerMatrix {N : ℕ} (z : LowerPair N → ℂ) : Matrix (Fin N) (Fin N) ℂ :=
  Matrix.of fun a b => if h : b < a then z ⟨(a, b), h⟩ else 0
def signatureForm (N p : ℕ) : Matrix (Fin N) (Fin N) ℂ :=
  Matrix.diagonal fun a => if a.val < p then 1 else -1
def flagPs (N p i : ℕ) (hi : i ≤ N) (z : LowerPair N → ℂ) : ℝ :=
  Real.log ‖((((1 : Matrix (Fin N) (Fin N) ℂ) + lowerMatrix z).submatrix id (Fin.castLE hi)).conjTranspose *
    signatureForm N p * ((1 + lowerMatrix z).submatrix id (Fin.castLE hi))).det‖
def flagWeight (N p : ℕ) (lam : Fin N → ℝ) (z : LowerPair N → ℂ) : ℝ :=
  ∑ k : Fin N, if h : k.val + 1 < N then
    (lam k - lam ⟨k.val + 1, h⟩) * flagPs N p (k.val + 1) h.le z else 0
def flagWeightProd (f N p : ℕ) (lam : Fin f → Fin N → ℝ) (z : (Σ _ : Fin f, LowerPair N) → ℂ) : ℝ :=
  ∑ τ : Fin f, flagWeight N p (lam τ) fun q => z ⟨τ, q⟩
def rootPairing (N p : ℕ) (lam : Fin N → ℝ) (q : LowerPair N) : ℝ :=
  if q.1.2.val < p ∧ p ≤ q.1.1.val then lam q.1.1 - lam q.1.2 else lam q.1.2 - lam q.1.1
def splitRank (N p : ℕ) (a : Fin N) : ℕ :=
  if p ≤ a.val then a.val - p else a.val + (N - p)
def IsSplitDominant (N p : ℕ) (lam : Fin N → ℝ) : Prop :=
  ∀ a b : Fin N, splitRank N p a ≤ splitRank N p b → lam b ≤ lam a
def FlagWeightLevi.Statement : Prop :=
  ∀ (f N p : ℕ) (lam : Fin f → Fin N → ℝ) (w : (Σ _ : Fin f, LowerPair N) → ℂ),
    levi (flagWeightProd f N p lam) 0 w = ∑ x, rootPairing N p (lam x.1) x.2 * ‖w x‖ ^ 2
def FlagRootProduct.Statement : Prop :=
  ∀ (N p : ℕ) (lam : Fin N → ℝ), IsSplitDominant N p lam →
    (∀ q, rootPairing N p lam q = |lam q.1.1 - lam q.1.2|) ∧
      ∏ q, rootPairing N p lam q = ∏ q : LowerPair N, |lam q.1.1 - lam q.1.2|
def weightDegree {f N : ℕ} (x : Fin f → Fin N → ℝ) : ℝ :=
  ∏ τ, ∏ i : Fin N, ∏ l : Fin N, if i < l then x τ i - x τ l else 1
def raiseSmall {f : ℕ} (N j' : ℕ) (δ : ℝ) (x : Fin f → Fin N → ℝ) : Fin f → Fin N → ℝ :=
  fun τ l => if N - j' ≤ l.val then x τ l + δ else x τ l
def Across (N j' : ℕ) (i l : Fin N) : Prop := i.val < N - j' ∧ N - j' ≤ l.val
instance (N j' : ℕ) (i l : Fin N) : Decidable (Across N j' i l) := by
  unfold Across; infer_instance
def DegreeRatio.Hyp {f : ℕ} (N j' : ℕ) (x : Fin f → Fin N → ℝ) (δ : ℝ) : Prop :=
  0 ≤ δ ∧ (∀ τ (i l : Fin N), i < l → x τ l < x τ i) ∧
    ∀ τ (i l : Fin N), Across N j' i l → δ < x τ i - x τ l
def DegreeRatio.Statement : Prop :=
  ∀ (f N j' : ℕ) (x : Fin f → Fin N → ℝ) (δ : ℝ), DegreeRatio.Hyp N j' x δ →
    weightDegree (raiseSmall N j' δ x) / weightDegree x =
        ∏ τ, ∏ i : Fin N, ∏ l : Fin N, (if Across N j' i l then 1 - δ / (x τ i - x τ l) else 1) ∧
      0 < weightDegree (raiseSmall N j' δ x) / weightDegree x ∧
      weightDegree (raiseSmall N j' δ x) / weightDegree x ≤ 1 ∧
      1 - weightDegree (raiseSmall N j' δ x) / weightDegree x ≤
        ∑ τ, ∑ i : Fin N, ∑ l : Fin N, (if Across N j' i l then δ / (x τ i - x τ l) else 0)
def RhoBound.Hyp {f : ℕ} (k j j' : ℕ) (x : Fin f → Fin (k + j + j' - 1) → ℝ) (g₁ T : ℝ)
    (w : Fin f → ℝ) : Prop :=
  1 ≤ k ∧ 3 * ((k + j + j' - 1 : ℕ) : ℝ) < g₁ ∧ 0 < T ∧ (∀ τ, 0 < w τ) ∧
    (∀ τ (i l : Fin (k + j + j' - 1)), i < l → x τ l < x τ i) ∧
    (∀ τ (i l : Fin (k + j + j' - 1)), Across (k + j + j' - 1) j' i l → g₁ ≤ x τ i - x τ l) ∧
    (∀ τ (i l : Fin (k + j + j' - 1)), i.val < k - 1 → Across (k + j + j' - 1) j' i l →
      w τ / (2 * T) ≤ x τ i - x τ l)
def RhoBound.Statement : Prop :=
  ∀ (f k j j' : ℕ) (x : Fin f → Fin (k + j + j' - 1) → ℝ) (g₁ T : ℝ) (w : Fin f → ℝ),
    RhoBound.Hyp k j j' x g₁ T w →
    let N : ℝ := ((k + j + j' - 1 : ℕ) : ℝ)
    let ρ := 1 - weightDegree (raiseSmall (k + j + j' - 1) j' (3 * N) x) / weightDegree x
    0 ≤ ρ ∧
      ρ ≤ 3 * N * ∑ τ, ((j : ℝ) * j' / g₁ + 2 * ((k : ℝ) - 1) * j' * T / w τ) ∧
      3 * N * ∑ τ, ((j : ℝ) * j' / g₁ + 2 * ((k : ℝ) - 1) * j' * T / w τ) ≤
        6 * N * ∑ τ, (((j : ℝ) + j') ^ 2 / g₁ + ((j : ℝ) + j') * k * T / w τ)
def MongeAmpereCompactChange.Hyp {e : ℕ} {X : Type} [TopologicalSpace X] (A : FinHolAtlas e X)
    (P : LocPot X) (v : X → ℝ) (K : Set X) : Prop :=
  IsPotential A P ∧ A.Smooth v ∧ HasCompactSupport v ∧ IsCompact K ∧ tsupport v ⊆ K
def MongeAmpereCompactChange.Statement : Prop :=
  ∀ {e : ℕ} {X : Type} [TopologicalSpace X] [T2Space X] (A : FinHolAtlas e X) (P : LocPot X)
    (v : X → ℝ) (K : Set X), MongeAmpereCompactChange.Hyp A P v K →
      mInt A (fun _ => P + LocPot.ofFun v) (K.indicator 1) = mInt A (fun _ => P) (K.indicator 1)
def MongeAmpereComparison.Hyp {e : ℕ} {X : Type} [TopologicalSpace X] (A : FinHolAtlas e X)
    (P : LocPot X) (a b : X → ℝ) : Prop :=
  IsPotential A P ∧ A.Smooth a ∧ A.Smooth b ∧ IsPsh A (P + LocPot.ofFun a) ∧
    IsPsh A (P + LocPot.ofFun b) ∧ ∀ k : ℝ, IsCompact {x | -k ≤ b x - a x}
def MongeAmpereComparison.Statement : Prop :=
  ∀ {e : ℕ} {X : Type} [TopologicalSpace X] [T2Space X] [MeasurableSpace X] [BorelSpace X]
    (A : FinHolAtlas e X) (P : LocPot X) (a b : X → ℝ), MongeAmpereComparison.Hyp A P a b →
      maMeasure A (fun _ => P + LocPot.ofFun b) Set.univ ≤
        maMeasure A (fun _ => P + LocPot.ofFun a) Set.univ
def FubiniStudyCoverMass.Hyp {e : ℕ} {X : Type} [TopologicalSpace X] (A : FinHolAtlas e X)
    (P : LocPot X) (q : X → Fin e → ℂ) (M₀ : Set X) (Δ : Set (Fin e → ℂ)) (d : ℕ) : Prop :=
  IsPotential A P ∧ IsOpen M₀ ∧ A.IsAnalyticSubset M₀ᶜ ∧ interior M₀ᶜ = ∅ ∧
    (∀ i, A.HoloOn M₀ fun x => q x i) ∧ IsClosed Δ ∧ volume Δ = 0 ∧
    (∃ h : Set.MapsTo q M₀ Δᶜ, IsCoveringMap h.restrict) ∧
    (∀ z ∉ Δ, (M₀ ∩ q ⁻¹' {z}).encard = d) ∧
    ∀ x, ∀ y ∈ P.U x ∩ M₀, ∃ W : Set X, IsOpen W ∧ y ∈ W ∧ ∃ G : X → ℂ, A.HoloOn W G ∧
      ∀ z ∈ W ∩ P.U x ∩ M₀, P.φ x z = (1 / 2) * Real.log (1 + ∑ i, ‖q z i‖ ^ 2) + (G z).re
def FubiniStudyCoverMass.Statement : Prop :=
  ∀ {e : ℕ} {X : Type} [TopologicalSpace X] [T2Space X] [MeasurableSpace X] [BorelSpace X]
    (A : FinHolAtlas e X) (P : LocPot X) (q : X → Fin e → ℂ) (M₀ : Set X) (Δ : Set (Fin e → ℂ))
    (d : ℕ), FubiniStudyCoverMass.Hyp A P q M₀ Δ d →
      IsPsh A P ∧ maMeasure A (fun _ => P) Set.univ = d
def HermitianDetMono.Statement : Prop :=
  ∀ (n : ℕ) (A B : Matrix (Fin n) (Fin n) ℂ), B.PosSemidef → (A - B).PosSemidef →
    B.det.re ≤ A.det.re
def RiemannExtension.Hyp {e : ℕ} {X : Type} [TopologicalSpace X] (A : FinHolAtlas e X) (S : Set X)
    (g : X → ℂ) : Prop :=
  A.IsAnalyticSubset S ∧ interior S = ∅ ∧ A.HoloOn Sᶜ g ∧
    ∀ x, ∃ W : Set X, IsOpen W ∧ x ∈ W ∧ BddAbove ((fun y => ‖g y‖) '' (W \ S))
def RiemannExtension.Statement : Prop :=
  ∀ {e : ℕ} {X : Type} [TopologicalSpace X] [T2Space X] (A : FinHolAtlas e X) (S : Set X)
    (g : X → ℂ), RiemannExtension.Hyp A S g →
      ∃ G : X → ℂ, A.HoloOn Set.univ G ∧ ∀ x ∉ S, G x = g x
def IntegralOnModel.Hyp (F : Type) [Field F] [NumberField F] (R : Type) [CommRing R]
    [Algebra (NumberField.RingOfIntegers F) R] (r g : R) (s : NumberField.RingOfIntegers F) : Prop :=
  s ≠ 0 ∧ g ≠ 0 ∧
    ∀ (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers F)) (L : Type) [Field L]
      [Algebra (v.adicCompletion F) L] [FiniteDimensional (v.adicCompletion F) L] (y : R →+* L),
      y.comp (algebraMap (NumberField.RingOfIntegers F) R) =
          (algebraMap (v.adicCompletion F) L).comp
            ((algebraMap F (v.adicCompletion F)).comp (algebraMap (NumberField.RingOfIntegers F) F)) →
      (∀ a : R, ((algebraMap (v.adicCompletion F) L).comp
          (v.adicCompletionIntegers F).subtype).IsIntegralElem (y a)) →
      y g ≠ 0 →
      ((algebraMap (v.adicCompletion F) L).comp
          (v.adicCompletionIntegers F).subtype).IsIntegralElem
        (y r / y (algebraMap (NumberField.RingOfIntegers F) R s))
def IntegralOnModel.Statement : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] (R : Type) [CommRing R] [IsDomain R]
    [Algebra (NumberField.RingOfIntegers F) R] [Module.Flat (NumberField.RingOfIntegers F) R]
    [Algebra.FiniteType (NumberField.RingOfIntegers F) R] [IsIntegrallyClosed R] (r g : R)
    (s : NumberField.RingOfIntegers F),
    IntegralOnModel.Hyp F R r g s → ∃ r' : R, r = algebraMap (NumberField.RingOfIntegers F) R s * r'
section Examples
def lineAtlas : FinHolAtlas 1 (Fin 1 → ℂ) where
  n := 1
  chart _ := OpenPartialHomeomorph.refl _
  cover _ := ⟨0, Set.mem_univ _⟩
  holo _ _ := analyticOnNhd_id
def lineFS (z : Fin 1 → ℂ) : ℝ := (1 / 2) * Real.log (1 + ∑ i, ‖z i‖ ^ 2)
end Examples
end
end GroundTheory.Heights₂.Heights.FourB


