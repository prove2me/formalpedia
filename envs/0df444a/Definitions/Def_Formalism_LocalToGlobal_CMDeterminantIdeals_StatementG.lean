-- Prove2me | Definitions.Def_Formalism_LocalToGlobal_CMDeterminantIdeals_StatementG
-- name    : Formalism_LocalToGlobal_CMDeterminantIdeals_StatementG
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T14:32:29.842797+00:00
-- url     : https://prove2.me/theorems/0707ff41-f90d-462e-bd9b-30dc9fa18c01
-- title:
--   Statement G
-- statement:
--   Definitions and structural lemmas for Statement G, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CMDeterminantIdeals/StatementG.lean

import Definitions.Def_Formalism_LocalToGlobal_CMDeterminantIdeals_DetIdeal
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
namespace Formalism.L2.LamCM
open IsLocalRing
open scoped ComplexOrder
abbrev FrVar {B : Type} (m : B → ℕ) : Type := Σ b : B, Fin (m b) × Fin (m b)
variable {B : Type} {m : B → ℕ}
def evalFr {R : Type} [CommRing R] (P : MvPolynomial (FrVar m) R) (X : ∀ b, Matrix (Fin (m b)) (Fin (m b)) R) : R :=
  MvPolynomial.eval (fun v : FrVar m => X v.1 v.2.2 v.2.1) P
def substFr {R : Type} [CommRing R] (U : ∀ b, Matrix (Fin (m b)) (Fin (m b)) R) (P : MvPolynomial (FrVar m) R) :
    MvPolynomial (FrVar m) R :=
  MvPolynomial.bind₁ (fun v : FrVar m => ∑ j, MvPolynomial.C (U v.1 j v.2.2) * MvPolynomial.X (⟨v.1, (v.2.1, j)⟩ : FrVar m)) P
def LemmaGCore : Prop :=
  ∀ (R K : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [Field K] [Algebra R K] [IsFractionRing R K]
    (B : Type) [Fintype B] (m : B → ℕ) (P : MvPolynomial (FrVar m) K),
    (Infinite (ResidueField R) ∨ P.totalDegree + ∑ b, m b < Nat.card (ResidueField R)) →
    (∀ X : ∀ b, Matrix (Fin (m b)) (Fin (m b)) R, (∀ b, IsUnit (X b).det) →
      evalFr P (fun b => (X b).map (algebraMap R K)) ∈ Set.range (algebraMap R K)) →
    ∀ μ, MvPolynomial.coeff μ P ∈ Set.range (algebraMap R K)
def BigResExt : Prop :=
  ∀ (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V], IsAdicComplete (maximalIdeal V) V →
    Finite (ResidueField V) → ∀ N : ℕ,
    ∃ (W : Type) (_ : CommRing W) (_ : IsDomain W) (_ : IsDiscreteValuationRing W) (_ : Algebra V W),
      IsAdicComplete (maximalIdeal W) W ∧ Finite (ResidueField W) ∧ N < Nat.card (ResidueField W) ∧
      Function.Injective (algebraMap V W) ∧ IsLocalHom (algebraMap V W)
def LemmaG : Prop :=
  ∀ (V K : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [Field K] [Algebra V K] [IsFractionRing V K]
    (B : Type) [Fintype B] (m : B → ℕ) (P : MvPolynomial (FrVar m) K),
    IsAdicComplete (maximalIdeal V) V → Finite (ResidueField V) →
    (∀ (W KW : Type) [CommRing W] [IsDomain W] [IsDiscreteValuationRing W] [Field KW] [Algebra W KW] [IsFractionRing W KW]
      [Algebra V W] (f : K →+* KW), IsAdicComplete (maximalIdeal W) W → Finite (ResidueField W) →
      IsLocalHom (algebraMap V W) → (∀ a : V, f (algebraMap V K a) = algebraMap W KW (algebraMap V W a)) →
      ∀ X : ∀ b, Matrix (Fin (m b)) (Fin (m b)) W, (∀ b, IsUnit (X b).det) →
        evalFr (MvPolynomial.map f P) (fun b => (X b).map (algebraMap W KW)) ∈ Set.range (algebraMap W KW)) →
    ∀ μ, MvPolynomial.coeff μ P ∈ Set.range (algebraMap V K)
def SubstGauss : Prop :=
  ∀ (R K : Type) [CommRing R] [Field K] [Algebra R K] (B : Type) [Fintype B] (m : B → ℕ) (P : MvPolynomial (FrVar m) K)
    (U : ∀ b, Matrix (Fin (m b)) (Fin (m b)) K) (c : ∀ b, Fin (m b) → K),
    (∀ μ, MvPolynomial.coeff μ P ∈ Set.range (algebraMap R K)) →
    (∀ b j k, c b j * U b j k ∈ Set.range (algebraMap R K)) →
    ∀ μ : FrVar m →₀ ℕ, MvPolynomial.coeff μ (substFr U P) * ∏ v : FrVar m, c v.1 v.2.2 ^ μ v ∈ Set.range (algebraMap R K)
def IsEquiv [DecidableEq B] (a : ∀ b, Fin (m b) → ℕ) (P : MvPolynomial (FrVar m) ℂ) : Prop :=
  ∀ (X : ∀ b, Matrix (Fin (m b)) (Fin (m b)) ℂ) (b : B) (t : Matrix (Fin (m b)) (Fin (m b)) ℂ),
    (∀ b', (X b').det ≠ 0) → t.det ≠ 0 → t.BlockTriangular id →
    evalFr P (Function.update X b (X b * t)) = ReciprocityTheory.MultiplicativeHeights.triChar (a b) t * evalFr P X
def ArchTie : Prop :=
  ∀ (B : Type) [Fintype B] [DecidableEq B] (m : B → ℕ) (a : ∀ b, Fin (m b) → ℕ) (P : MvPolynomial (FrVar m) ℂ)
    (Hm U : ∀ b, Matrix (Fin (m b)) (Fin (m b)) ℂ) (nn : ∀ b, Fin (m b) → ℝ) (C La : ℝ) (r : ℕ),
    (∀ b, (Hm b).PosDef) → IsEquiv a P →
    (∀ X : ∀ b, Matrix (Fin (m b)) (Fin (m b)) ℂ, (∀ b, (X b).conjTranspose * Hm b * X b = 1) → ‖evalFr P X‖ ≤ C) →
    (∀ b j, 0 < nn b j) → 0 ≤ La → (∀ b, m b ≤ r) →
    (∀ b j, ReciprocityTheory.MultiplicativeHeights.hq (Hm b) (U b j) ≤ (La * nn b j) ^ 2) →
    ∀ z : FrVar m → ℂ, (∀ v : FrVar m, ‖z v‖ * nn v.1 v.2.2 ≤ 1) →
      ‖MvPolynomial.eval z (substFr U P)‖ ≤ C * ((r : ℝ) * La) ^ (∑ b, ∑ i, a b i)
def SubstHomog : Prop :=
  ∀ (B : Type) [Fintype B] [DecidableEq B] (m : B → ℕ) (a : ∀ b, Fin (m b) → ℕ) (P : MvPolynomial (FrVar m) ℂ)
    (U : ∀ b, Matrix (Fin (m b)) (Fin (m b)) ℂ), IsEquiv a P →
    ∀ μ : FrVar m →₀ ℕ, MvPolynomial.coeff μ (substFr U P) ≠ 0 → ∑ v : FrVar m, μ v = ∑ b, ∑ i, a b i
end Formalism.L2.LamCM


