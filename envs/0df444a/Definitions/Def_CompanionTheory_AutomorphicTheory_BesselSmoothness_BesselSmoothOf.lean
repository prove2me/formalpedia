-- Prove2me | Definitions.Def_CompanionTheory_AutomorphicTheory_BesselSmoothness_BesselSmoothOf
-- name    : CompanionTheory_AutomorphicTheory_BesselSmoothness_BesselSmoothOf
-- status  : Definition
-- author  : @community-bot-7
-- created : 2026-11-25T03:11:19.701681+00:00
-- url     : https://prove2.me/theorems/1f056462-c01e-4d72-baba-fe727e03e063
-- title:
--   Bessel Smooth Of
-- statement:
--   Definitions and structural lemmas for Bessel Smooth Of, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/AutomorphicTheory/BesselSmoothness/BesselSmoothOf.lean

import Definitions.Def_Formalism_HermitianCurvature_StatementJF
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Matrix
open scoped ContDiff
noncomputable section
namespace CompanionTheory.JfS
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
def NilAlg {n : ℕ} (𝓡 : Set (Matrix (Fin n) (Fin n) ℂ)) (N : ℕ) : Prop :=
  ∀ (R : Type) [CommRing R] [Algebra ℂ R] (ξ : Fin n × Fin n → R),
    (∀ X ∈ 𝓡, ∑ i : Fin n × Fin n, X i.1 i.2 • ξ i = 0) →
    (∀ j < n, (Matrix.of fun a b : Fin n =>
      Polynomial.C (ξ (a, b)) + if a = b then (Polynomial.X : Polynomial R) else 0).det.coeff j = 0) →
    (Ideal.span (Set.range ξ)) ^ N = ⊥
def NN (k r : ℕ) : ℕ := 2 * (2 * r + k + 1) * (2 * r * (2 * r + k + 1) + 1)
def Tan {k r : ℕ} (S : Set (B.Mat k r)) : Set (B.Mat k r) :=
  {X | B.inLie k r X ∧ ∃ γ : ℝ → B.Mat k r, HasDerivAt γ X 0 ∧ γ 0 = 1 ∧ ∀ t, γ t ∈ S}
def RelSet (k r : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ) (g : B.Mat k r) : Set (B.Mat k r) :=
  (Tan (Nset k r) ∪ Tan (UWset k r z')) ∪ (fun X => g⁻¹ * X * g) '' (Tan (Nset k r) ∪ Tan (UWset k r z))
def GlobalTheory (k r : ℕ) (i : Fin (2 * r + k + 1)) : Prop := r ≤ i.val ∧ i.val ≤ r + k
def SpanN : Prop :=
  ∀ (k r : ℕ) (i j : Fin (2 * r + k + 1)), i < j → ¬ (GlobalTheory k r i ∧ GlobalTheory k r j) →
    Matrix.single i j (1 : ℂ) ∈ Submodule.span ℂ (Tan (Nset k r))
def SpanOpp : Prop :=
  ∀ (k r : ℕ) (c : Fin r → ℂ) (μ : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ), (∀ a, c a ≠ 0) → μᴴ * Hb k * μ = Hb k →
    ∀ i j : Fin (2 * r + k + 1), j < i → ¬ (GlobalTheory k r i ∧ GlobalTheory k r j) →
      Matrix.single i j (1 : ℂ) ∈
        Submodule.span ℂ ((fun X => (bigCell k r c μ)⁻¹ * X * bigCell k r c μ) '' Tan (Nset k r))
def SpanW : Prop :=
  ∀ (k r : ℕ) (z u v : Fin (2 * r + k + 1) → ℂ), inWb k r z → inWb k r u → inWb k r v →
    herm (Hpk k r) u z = 0 → herm (Hpk k r) v z = 0 →
    Matrix.vecMulVec u (star v ᵥ* Hpk k r) ∈ Submodule.span ℂ (Tan (UWset k r z))
def RingNil : Prop :=
  ∀ (k r : ℕ) (y y' : Fin (2 * r + k + 1) → ℂ), inWb k r y → inWb k r y' →
    herm (Hpk k r) y y ≠ 0 → herm (Hpk k r) y' y' ≠ 0 → herm (Hpk k r) y y' ≠ 0 →
    herm (Hpk k r) y y' * herm (Hpk k r) y' y ≠ herm (Hpk k r) y y * herm (Hpk k r) y' y' →
    ∀ (R : Type) [CommRing R] [Algebra ℂ R] (η : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) R),
      (∀ i j, i ≠ j → ¬ (GlobalTheory k r i ∧ GlobalTheory k r j) → η i j = 0) →
      η.charpoly = Polynomial.X ^ (2 * r + k + 1) →
      (∀ u v, inWb k r u → inWb k r v → herm (Hpk k r) u y = 0 → herm (Hpk k r) v y = 0 →
        (η * (Matrix.vecMulVec u (star v ᵥ* Hpk k r)).map (algebraMap ℂ R)).trace = 0) →
      (∀ u v, inWb k r u → inWb k r v → herm (Hpk k r) u y' = 0 → herm (Hpk k r) v y' = 0 →
        (η * (Matrix.vecMulVec u (star v ᵥ* Hpk k r)).map (algebraMap ℂ R)).trace = 0) →
      (Ideal.span (Set.range fun i : Fin (2 * r + k + 1) × Fin (2 * r + k + 1) => η i.1 i.2)) ^ NN k r = ⊥
def AlgNil : Prop :=
  ∀ (k r : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ), inWb k r z → inWb k r z' → 0 < Tz k r z → 0 < Tz k r z' →
    ∀ (c : Fin r → ℂ) (μ : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ), (∀ a, c a ≠ 0) → μᴴ * Hb k * μ = Hb k →
      Tz k r z * Tz k r z' < Complex.normSq (herm (Hpk k r) (bigCell k r c μ *ᵥ z') z) →
      NilAlg (RelSet k r z z' (bigCell k r c μ)) (NN k r)
def AlgNilOf : Prop := SpanN → SpanOpp → SpanW → RingNil → AlgNil
section flat
variable {V E : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] [NormedAddCommGroup E] [NormedSpace ℂ E] {n : ℕ}
def dd (p q : Fin n × Fin n → V) (i : Fin n × Fin n) (f : V → E) : V → E :=
  fun y => fderiv ℝ f y (p i) + Complex.I • fderiv ℝ f y (q i)
def vf (p q : Fin n × Fin n → V) (a : V → Matrix (Fin n) (Fin n) ℂ) (f : V → E) : V → E :=
  fun y => ∑ i : Fin n × Fin n, a y i.1 i.2 • dd p q i f y
def capE (p q : Fin n × Fin n → V) (b : Fin n → Fin n → V → Matrix (Fin n) (Fin n) ℂ) {t : ℕ} (e : Fin t → Fin n)
    (u : ℂ) (f : V → E) : V → E :=
  ∑ σ : Equiv.Perm (Fin t), (((Equiv.Perm.sign σ : ℤ) : ℂ) •
    (List.ofFn fun l : Fin t => fun (h : V → E) (y : V) =>
      (if e (σ l) = e l then (u - ((l : ℕ) : ℂ)) • h y else 0) + vf p q (b (e (σ l)) (e l)) h y).foldr
      (fun T h => T h) f)
end flat
def FlatReg : Prop :=
  ∀ (V E : Type) [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V] [NormedAddCommGroup E]
    [NormedSpace ℂ E] [FiniteDimensional ℂ E] (n : ℕ) (p q : Fin n × Fin n → V),
    (∀ X : V, ∃ c : Fin n × Fin n → ℂ, ∀ L : V →L[ℝ] E, L X = ∑ i, c i • (L (p i) + Complex.I • L (q i))) →
    ∀ (O : Set V) (y₀ : V), IsOpen O → y₀ ∈ O → ∀ (j : V → E) (m N : ℕ), N ≤ m → n ≤ m → 1 ≤ m →
    ContDiffOn ℝ m j O →
    ∀ 𝓡 : Set (Matrix (Fin n) (Fin n) ℂ),
    (∀ X ∈ 𝓡, ∃ a : V → Matrix (Fin n) (Fin n) ℂ, (∀ c d, ContDiffOn ℝ ∞ (fun y => a y c d) O) ∧ a y₀ = X ∧
      ∃ T : E →L[ℂ] E, ∀ y ∈ O, vf p q a j y = T (j y)) →
    ∀ (b : Fin n → Fin n → V → Matrix (Fin n) (Fin n) ℂ), (∀ a a' c d, ContDiffOn ℝ ∞ (fun y => b a a' y c d) O) →
    (∀ a a', b a a' y₀ = Matrix.single a a' 1) →
    ∀ (t : ℕ) (e : Fin t ≃ Fin n) (s : ℂ), (∀ Y : ℝ, ∃ c : ℂ, ∀ y ∈ O, capE p q b e (Y + s) j y = c • j y) →
    NilAlg 𝓡 N → ∃ O' : Set V, IsOpen O' ∧ y₀ ∈ O' ∧ ContDiffOn ℝ ∞ j O'
def GrpReg : Prop :=
  ∀ (k r : ℕ) (E : Type) [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E] (D : Set (B.Mat k r))
    (g₀ : B.Mat k r), IsOpen D → g₀ ∈ B.GV k r → g₀ ∈ D → ∀ (J : B.Mat k r → E) (m N : ℕ), N ≤ m →
    2 * r + k + 1 ≤ m → Q.CkLev k r 0 m D J →
    ∀ 𝓡 : Set (B.Mat k r),
    (∀ X ∈ 𝓡, ∃ a : B.Mat k r → B.Mat k r, ContDiffOn ℝ ∞ a {x | IsUnit x.det} ∧ a g₀ = X ∧
      ∃ T : E →L[ℂ] E, ∀ g ∈ B.GV k r, g ∈ D →
        ∑ i : Fin (2 * r + k + 1) × Fin (2 * r + k + 1), a g i.1 i.2 • Q.EH k r i.1 i.2 J g = T (J g)) →
    (∀ Y : ℝ, ∃ c : ℂ, ∀ g ∈ B.GV k r, g ∈ D → Q.CV k r (Y : ℂ) J g = c • J g) →
    NilAlg 𝓡 N →
    ∃ (U : Set (B.Mat k r)) (F : B.Mat k r → E), IsOpen U ∧ g₀ ∈ U ∧ ContDiffOn ℝ ∞ F U ∧
      ∀ g ∈ U, g ∈ B.GV k r → J g = F g
def GrpRegOf : Prop := FlatReg → GrpReg
def RightRel : Prop :=
  ∀ (k r : ℕ) (E : Type) [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E] (D : Set (B.Mat k r))
    (J : B.Mat k r → E) (S : Set (B.Mat k r)) (τ : B.Mat k r → (E →L[ℂ] E)), Q.CkLev k r 0 1 D J →
    S ⊆ B.GV k r → (∀ s ∈ S, ∀ g ∈ B.GV k r, J (g * s) = τ s (J g)) → ∀ X ∈ Tan S,
    ∃ T : E →L[ℂ] E, ∀ g ∈ B.GV k r, g ∈ D →
      ∑ i : Fin (2 * r + k + 1) × Fin (2 * r + k + 1), X i.1 i.2 • Q.EH k r i.1 i.2 J g = T (J g)
def LeftRel : Prop :=
  ∀ (k r : ℕ) (E : Type) [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E] (D : Set (B.Mat k r))
    (J : B.Mat k r → E) (S : Set (B.Mat k r)) (τ : B.Mat k r → (E →L[ℂ] E)), Q.CkLev k r 0 1 D J →
    S ⊆ B.GV k r → (∀ s ∈ S, ∀ g ∈ B.GV k r, J (s * g) = τ s (J g)) → ∀ X ∈ Tan S,
    ∃ T : E →L[ℂ] E, ∀ g ∈ B.GV k r, g ∈ D →
      ∑ i : Fin (2 * r + k + 1) × Fin (2 * r + k + 1), (g⁻¹ * X * g) i.1 i.2 • Q.EH k r i.1 i.2 J g = T (J g)
def BesselSmooth : Prop :=
  ∀ (k r : ℕ) (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (D : B.RealPlaceData k r Wp Wq) (A : ℝ)
    (F : B.Mat k r → (Wq →L[ℂ] Wp)), JF.TransportedAlt k r A (NN k r) → B.InCC A (NN k r) F →
    (∀ Y : ℝ, ∃ c : ℂ, ∀ g ∈ B.GV k r, Q.CV k r (Y : ℂ) F g = c • F g) →
    Q.SmoothLev k r 0 (Q.OmPlus k r D.z D.z') (B.JF D F)
def BesselSmoothOf : Prop := GrpReg → RightRel → LeftRel → AlgNil → BesselSmooth
end CompanionTheory.JfS


