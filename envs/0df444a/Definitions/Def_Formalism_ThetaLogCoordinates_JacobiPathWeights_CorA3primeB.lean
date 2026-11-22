-- Prove2me | Definitions.Def_Formalism_ThetaLogCoordinates_JacobiPathWeights_CorA3primeB
-- name    : Formalism_ThetaLogCoordinates_JacobiPathWeights_CorA3primeB
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T21:27:12.676602+00:00
-- url     : https://prove2.me/theorems/e8024374-aa5d-4783-a5ab-900647792ed9
-- title:
--   Cor A3prime B
-- statement:
--   Definitions and structural lemmas for Cor A3prime B, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/JacobiPathWeights/CorA3primeB.lean

import Mathlib
import Definitions.Def_Formalism_ThetaLogCoordinates_JacobiPathWeights_StatementP
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Finset MvPolynomial
namespace Formalism.InvariantFactorPaths.GelfandTsetlinBases
def valP {k : Type*} [Field k] {n : ℕ} (isVec : ℕ → Bool) (i : ℕ) (G : MvPolynomial (ℕ × Fin n) k) :
    WithTop ℤ :=
  valS (ζ := Empty) isVec {j : ℕ | j < i} (rename Sum.inl G)
def lamP {k : Type*} [Field k] {n : ℕ} (isVec : ℕ → Bool) (i : ℕ) (G : MvPolynomial (ℕ × Fin n) k) :
    WithBot ℤ :=
  lam1S (ζ := Empty) isVec {j : ℕ | j < i} (rename Sum.inl G)
def geB (x : WithTop ℤ) (θ : WithBot ℤ) : Prop := ∀ t : ℤ, θ = (t : WithBot ℤ) → (t : WithTop ℤ) ≤ x
def leT (y : WithBot ℤ) (M : WithTop ℤ) : Prop := ∀ t : ℤ, M = (t : WithTop ℤ) → y ≤ (t : WithBot ℤ)
def GoodW {n : ℕ} (θ : WithBot ℤ) (M : WithTop ℤ) (μ : Fin n → ℤ) : Prop :=
  (∀ m : Fin n, m.val + 1 = n → θ ≤ ((μ m : ℤ) : WithBot ℤ)) ∧
  (∀ m : Fin n, m.val = 0 → ((μ m : ℤ) : WithTop ℤ) ≤ M)
def GoodG {k : Type*} [Field k] {n : ℕ} (isVec : ℕ → Bool) (i : ℕ) (θ : WithBot ℤ) (M : WithTop ℤ)
    (G : MvPolynomial (ℕ × Fin n) k) : Prop :=
  geB (valP isVec i G) θ ∧ leT (lamP isVec i G) M
def psiFam (R : Type*) [CommRing R] (n N : ℕ) (isVec : ℕ → Bool) (B : ℕ → ℕ) (x : PathIdx n N isVec B) :
    MvPolynomial (ℕ × Fin n) R :=
  psiPath R isVec x.1.1 N x.1.2
def LemmaA3top : Prop :=
  ∀ (k : Type) [Field k] (n N : ℕ) (isVec : ℕ → Bool) (B : ℕ → ℕ) (θ : WithBot ℤ) (M : WithTop ℤ)
    (G : MvPolynomial (ℕ × Fin n) k), 1 ≤ n → G ∈ polB k n N B → GoodG isVec N θ M G →
    G ∈ Submodule.span k (psiFam k n N isVec B '' {x | GoodW θ M (x.1.1 N)})
def FactSplit : Prop :=
  ∀ (k : Type) [Field k] (n N i : ℕ) (isVec : ℕ → Bool) (B : ℕ → ℕ) (θ : WithBot ℤ) (M : WithTop ℤ)
    (G : MvPolynomial (ℕ × Fin n) k), i ≤ N → G ∈ polB k n N B →
    ∃ (T : Finset (ℕ × Fin n →₀ ℕ)) (Gc : (ℕ × Fin n →₀ ℕ) → MvPolynomial (ℕ × Fin n) k),
      (∀ β ∈ T, ∀ j, ∑ a, β (j, a) = if i ≤ j ∧ j < N then B j else 0) ∧
      (∀ β ∈ T, Gc β ∈ polB k n i B) ∧
      G = ∑ β ∈ T, Gc β * monomial β 1 ∧
      (GoodG isVec i θ M G → ∀ β ∈ T, GoodG isVec i θ M (Gc β))
def LemmaA3one : Prop :=
  ∀ (k : Type) [Field k] (n N i : ℕ) (isVec : ℕ → Bool) (B : ℕ → ℕ) (θ : WithBot ℤ) (M : WithTop ℤ)
    (G : MvPolynomial (ℕ × Fin n) k), 1 ≤ n → i ≤ N → G ∈ polB k n N B → GoodG isVec i θ M G →
    G ∈ Submodule.span k (psiFam k n N isVec B '' {x | GoodW θ M (x.1.1 i)})
def LemmaA3field : Prop :=
  ∀ (k : Type) [Field k] (n N : ℕ) (isVec : ℕ → Bool) (B : ℕ → ℕ) (θ : ℕ → WithBot ℤ) (M : ℕ → WithTop ℤ)
    (G : MvPolynomial (ℕ × Fin n) k), 1 ≤ n →
    ((G ∈ polB k n N B ∧ ∀ i ≤ N, GoodG isVec i (θ i) (M i) G) ↔
      G ∈ Submodule.span k (psiFam k n N isVec B '' {x | ∀ i ≤ N, GoodW (θ i) (M i) (x.1.1 i)}))
def LemmaA3int : Prop :=
  ∀ (O Kf : Type) [CommRing O] [IsDomain O] [Field Kf] [Algebra O Kf] [IsFractionRing O Kf] (n N : ℕ)
    (isVec : ℕ → Bool) (B : ℕ → ℕ) (θ : ℕ → WithBot ℤ) (M : ℕ → WithTop ℤ)
    (G : MvPolynomial (ℕ × Fin n) O), 1 ≤ n →
    ((G ∈ polB O n N B ∧ ∀ i ≤ N, GoodG isVec i (θ i) (M i) (map (algebraMap O Kf) G)) ↔
      G ∈ Submodule.span O (psiFam O n N isVec B '' {x | ∀ i ≤ N, GoodW (θ i) (M i) (x.1.1 i)}))
def CorA3primeA : Prop :=
  ∀ (O Kf : Type) [CommRing O] [IsDomain O] [Field Kf] [Algebra O Kf] [IsFractionRing O Kf] (n N : ℕ)
    (isVec : ℕ → Bool) (B : ℕ → ℕ) (θ : ℕ → WithBot ℤ) (M : ℕ → WithTop ℤ) (c : O)
    (G : MvPolynomial (ℕ × Fin n) O), 1 ≤ n → G ∈ polB O n N B →
    ((∀ i ≤ N, ∃ Z ∈ polB O n N B, ∃ H ∈ polB O n N B,
        GoodG isVec i (θ i) (M i) (map (algebraMap O Kf) Z) ∧ G = Z + c • H) ↔
      ∃ Z ∈ polB O n N B, ∃ H ∈ polB O n N B,
        (∀ i ≤ N, GoodG isVec i (θ i) (M i) (map (algebraMap O Kf) Z)) ∧ G = Z + c • H)
def CorA3primeB : Prop :=
  ∀ (O Kf F : Type) [CommRing O] [IsDomain O] [Field Kf] [Algebra O Kf] [IsFractionRing O Kf] [Field F]
    (π : O →+* F) (n N : ℕ) (isVec : ℕ → Bool) (B : ℕ → ℕ) (θ : ℕ → WithBot ℤ) (M : ℕ → WithTop ℤ)
    (G : MvPolynomial (ℕ × Fin n) O), Function.Surjective π → 1 ≤ n → G ∈ polB O n N B →
    (∀ i ≤ N, GoodG isVec i (θ i) (M i) (map π G)) →
    ∃ Z ∈ polB O n N B, ∃ H ∈ polB O n N B,
      (∀ i ≤ N, GoodG isVec i (θ i) (M i) (map (algebraMap O Kf) Z)) ∧ map π H = 0 ∧ G = Z + H
end Formalism.InvariantFactorPaths.GelfandTsetlinBases


