-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_JetGauges_PerfectPairings
-- name    : Development_AbelianVarietyTheory_BlockTheory_JetGauges_PerfectPairings
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T15:44:31.246684+00:00
-- url     : https://prove2.me/theorems/849839a4-7f85-4b08-a36b-06fd7609f3b9
-- title:
--   Perfect Pairings
-- statement:
--   Definitions and structural lemmas for Perfect Pairings, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/BlockTheory/JetGauges/PerfectPairings.lean

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_CocycleRightZeroThd
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
namespace GlobalTheory.IndefiniteRowSideFullHecke.PerfectPairings
structure IsPerfectPairing {A B K : Type} [AddCommGroup A] [AddCommGroup B] [Field K]
    (e : A → B → Kˣ) : Prop where
  add_left : ∀ a a' t, e (a + a') t = e a t * e a' t
  add_right : ∀ a t t', e a (t + t') = e a t * e a t'
  nondeg_left : ∀ a, (∀ t, e a t = 1) → a = 0
  nondeg_right : ∀ t, (∀ a, e a t = 1) → t = 0
def fourierCoeff {A B K : Type} [Fintype A] [Fintype B] [Field K]
    (e : A → B → Kˣ) (φ : A → K) (t : B) : K :=
  ((Fintype.card B : ℕ) : K)⁻¹ * ∑ a : A, φ a * (((e a t)⁻¹ : Kˣ) : K)
def onDatum {A B K V : Type} [Fintype A] [Fintype B] [Field K] [AddCommGroup V] [Module K V]
    (e : A → B → Kˣ) (θ : B → V) (φ : A → K) : V :=
  ∑ t : B, fourierCoeff e φ t • θ t
def FourierInversion : Prop :=
  ∀ (A B K : Type) [AddCommGroup A] [AddCommGroup B] [Fintype A] [Fintype B] [Field K]
    (e : A → B → Kˣ), IsPerfectPairing e →
      Fintype.card A = Fintype.card B ∧ ((Fintype.card B : ℕ) : K) ≠ 0 ∧
      (∀ (φ : A → K) (a : A), φ a = ∑ t : B, fourierCoeff e φ t * ((e a t : Kˣ) : K)) ∧
      (∀ t₀ : B, fourierCoeff e (fun a => ((e a t₀ : Kˣ) : K)) t₀ = 1 ∧
        ∀ t : B, t ≠ t₀ → fourierCoeff e (fun a => ((e a t₀ : Kˣ) : K)) t = 0) ∧
      (∀ (V : Type) [AddCommGroup V] [Module K V] (θ : B → V) (t₀ : B),
        onDatum e θ (fun a => ((e a t₀ : Kˣ) : K)) = θ t₀)
def EnoughCharacters : Prop :=
  ∀ (A K : Type) [AddCommGroup A] [Fintype A] [Field K]
    [HasEnoughRootsOfUnity K (AddMonoid.exponent A)],
      Finite (Additive (Multiplicative A →* Kˣ)) ∧
      IsPerfectPairing (fun (a : A) (χ : Additive (Multiplicative A →* Kˣ)) =>
        (Additive.toMul χ) (Multiplicative.ofAdd a))
def FourierDenominators : Prop :=
  ∀ (A B K : Type) [AddCommGroup A] [AddCommGroup B] [Fintype A] [Fintype B] [Field K]
    (e : A → B → Kˣ), IsPerfectPairing e → ∀ φ : A → K,
      (∀ O : Subring K, (∀ a, φ a ∈ O) → (∀ a t, ((e a t : Kˣ) : K) ∈ O) →
        ∀ t, ((Fintype.card B : ℕ) : K) * fourierCoeff e φ t ∈ O) ∧
      (∀ O : ValuationSubring K, (∀ a, φ a ∈ O) →
        (∀ t, ((Fintype.card B : ℕ) : K) * fourierCoeff e φ t ∈ O) ∧
        (IsUnit ((Fintype.card B : ℕ) : O) → ∀ t, fourierCoeff e φ t ∈ O))
def mulNat {R : Type} [CommRing R] {d : ℕ} (G : FGLaw R d) (n : ℕ) : Pt R 1 d :=
  Nat.rec (motive := fun _ => Pt R 1 d) 0 (fun _ y => G.add y (pt R d 0)) n
def ChainNat : Prop :=
  ∀ (R : Type) [CommRing R] (d : ℕ) (G : FGLaw R d) (ι : Type) [Fintype ι]
    (u : ι → Fin d → R) (P : MvPolynomial ι R) (k : ℕ), P.IsHomogeneous k →
      ∀ (n : ℕ) (f : PS R 1 d),
        constantCoeff (DpolyOf G.F u P (ev ![mulNat G n] f)) =
          (n : R) ^ k * constantCoeff (DpolyOf G.F u P f)
def ChainInt : Prop :=
  ∀ (R : Type) [CommRing R] (d : ℕ) (G : FGLaw R d) (O : Type) [CommRing O] (A : OAct O G)
    (ι : Type) [Fintype ι] (u : ι → Fin d → R) (P : MvPolynomial ι R) (k : ℕ),
      P.IsHomogeneous k → ∀ (n : ℤ) (f : PS R 1 d),
        constantCoeff (DpolyOf G.F u P (ev ![A.act (n : O)] f)) =
          (n : R) ^ k * constantCoeff (DpolyOf G.F u P f)
def Statement : Prop :=
  FourierInversion ∧ EnoughCharacters ∧ FourierDenominators ∧ ChainNat ∧ ChainInt
end GlobalTheory.IndefiniteRowSideFullHecke.PerfectPairings


