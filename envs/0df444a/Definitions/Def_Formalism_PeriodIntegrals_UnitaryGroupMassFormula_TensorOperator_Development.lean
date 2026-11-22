-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_TensorOperator_Development
-- name    : Formalism_PeriodIntegrals_UnitaryGroupMassFormula_TensorOperator_Development
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T23:09:33.550119+00:00
-- url     : https://prove2.me/theorems/cf5e32df-4375-4aa0-8450-8d084906b5f8
-- title:
--   Development
-- statement:
--   Definitions and structural lemmas for Development, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/TensorOperator/Development.lean

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_FockRBlock
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPolynomial
noncomputable section
namespace PI.TOW
open PI.TO
def embS (K : Type) [CommRing K] {n' k : ℕ} (t : Fin n') :
    MvPolynomial (Fin k) K →ₐ[K] MvPolynomial (Fin n' × Fin k) K :=
  rename fun c => (t, c)
def liftW {n' k : ℕ} (t : Fin n') (l : List (Fin k × Fin k)) : List (Fin n' × (Fin k × Fin k)) :=
  l.map fun y => (t, y)
def concatW {n' k : ℕ} (w : Fin n' → List (Fin k × Fin k)) : List (Fin n' × (Fin k × Fin k)) :=
  (List.finRange n').flatMap fun t => liftW t (w t)
def partS {n' k : ℕ} (μ : Fin n' × Fin k →₀ ℕ) (t : Fin n') : Fin k →₀ ℕ :=
  Finsupp.equivFunOnFinite.symm fun c => μ (t, c)
def WordOK {n' k : ℕ} (TT : Finset (Fin n')) (c : ℕ) (l : List (Fin n' × (Fin k × Fin k))) : Prop :=
  (∀ z ∈ l, z.1 ∈ TT) ∧ ∀ t, (l.filter fun z => z.1 = t).length ≤ c
def combo {K : Type} [CommRing K] {n' k : ℕ} (f : List (Fin n' × (Fin k × Fin k)) →₀ K)
    (G : MvPolynomial (Fin n' × Fin k) K) : MvPolynomial (Fin n' × Fin k) K :=
  f.sum fun l a => a • opWord l G
def Ok (K : Type) [Field K] (n' m : ℕ) (vec : Fin n' → Bool) (TT : Finset (Fin n')) (d : Fin n' → ℕ) (c : ℕ)
    (β s : MvPolynomial (Fin n' × (Fin (m + 1) × Fin (m + 1))) K) : Prop :=
  ∃ f : List (Fin n' × (Fin (m + 1) × Fin (m + 1))) →₀ K, (∀ l ∈ f.support, WordOK TT c l) ∧
    ∀ G ∈ Pol K (ι := Fin n') (m + 1) d, ∀ H ∈ Pol K (ι := Fin n') (m + 1) d,
      fockR (Th0 K m vec G * s) (Th0 K m vec H * β) = fockR (Th0 K m vec (combo f G)) (Th0 K m vec H)
def StepDeg : Prop :=
  ∀ (K : Type) [Field K] (n' k : ℕ) (d : Fin n' → ℕ) (l : List (Fin n' × (Fin k × Fin k))),
    ∀ G ∈ Pol K (ι := Fin n') k d, opWord l G ∈ Pol K (ι := Fin n') k d
def StepLift : Prop :=
  ∀ (K : Type) [CommRing K] (n' k : ℕ) (w : Fin n' → List (Fin k × Fin k)) (F : Fin n' → MvPolynomial (Fin k) K),
    opWord (concatW w) (∏ t, embS K t (F t)) = ∏ t, embS K t (word1 (w t) (F t))
def StepMonoFactor : Prop :=
  ∀ (K : Type) [CommRing K] (n' k : ℕ) (μ : Fin n' × Fin k →₀ ℕ),
    monomial μ (1 : K) = ∏ t, embS K t (monomial (partS μ t) (1 : K))
def StepPure : Prop :=
  FockRBlock → OnePos →
  ∀ (K : Type) [Field K] [CharZero K] (n' m : ℕ), 1 ≤ m → ∀ (vec : Fin n' → Bool) (TT : Finset (Fin n'))
    (d : Fin n' → ℕ) (c : ℕ) (ν : Fin n' → Fin (m + 1) → ℕ), (∀ t, Antitone (ν t)) → (∀ t ∈ TT, ν t 0 ≤ c) →
    (∀ t, t ∉ TT → ν t = 0) →
    ∀ B S : Fin n' → MvPolynomial (Fin (m + 1) × Fin (m + 1)) K,
      (∀ t, B t ∈ dualWeyl K (m + 1) (m + 1) (ν t)) → (∀ t, S t ∈ dualWeyl K (m + 1) (m + 1) (ν t)) →
      Ok K n' m vec TT d c (∏ t, blockEmb K t (B t)) (∏ t, blockEmb K t (S t))
def StepSpan : Prop :=
  ∀ (K : Type) [Field K] (n' m : ℕ) (vec : Fin n' → Bool) (TT : Finset (Fin n')) (d : Fin n' → ℕ) (c : ℕ)
    (M : Fin n' → Submodule K (MvPolynomial (Fin (m + 1) × Fin (m + 1)) K)),
    (∀ B S : Fin n' → MvPolynomial (Fin (m + 1) × Fin (m + 1)) K, (∀ t, B t ∈ M t) → (∀ t, S t ∈ M t) →
      Ok K n' m vec TT d c (∏ t, blockEmb K t (B t)) (∏ t, blockEmb K t (S t))) →
    ∀ β ∈ tensorLat K K M, ∀ s ∈ tensorLat K K M, Ok K n' m vec TT d c β s
end PI.TOW


