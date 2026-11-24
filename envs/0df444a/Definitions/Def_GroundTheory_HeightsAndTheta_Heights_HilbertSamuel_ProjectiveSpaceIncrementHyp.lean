-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_ProjectiveSpaceIncrementHyp
-- name    : GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_ProjectiveSpaceIncrementHyp
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T23:53:13.995719+00:00
-- url     : https://prove2.me/theorems/7cfba49d-57bf-41c3-a08d-22cf17077800
-- title:
--   Projective Space Increment Hyp
-- statement:
--   Definitions and structural lemmas for Projective Space Increment Hyp, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HilbertSamuel/ProjectiveSpaceIncrementHyp.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_Objects
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.HilbertSamuel
open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR
noncomputable section
universe u
section Objects
variable {K : Type*} [DecidableEq K] (ι : K → Type*) {F : Type*} [Field F]
variable {M : Type*} [AddCommGroup M] [Module (MRing ι F) M] [Module F M]
  [IsScalarTower F (MRing ι F) M]
open Classical in

structure IsMultigraded (ℳ : (K → ℤ) → Submodule F M) : Prop where
  internal : DirectSum.IsInternal ℳ
  var_mul : ∀ (v : Σ k, ι k) (m : K → ℤ), ∀ x ∈ ℳ m,
    (X v : MRing ι F) • x ∈ ℳ (m + Pi.single v.1 1)
variable {ι}
def modHilb (ℳ : (K → ℤ) → Submodule F M) (m : K → ℤ) : ℤ :=
  (Module.finrank F (ℳ m) : ℤ)
end Objects
section Support
variable {S : Type*} [CommRing S] (M : Type*) [AddCommGroup M] [Module S M]
def modMultAt (p : PrimeSpectrum S) : ℕ∞ :=
  Module.length (Localization.AtPrime p.asIdeal) (LocalizedModule p.asIdeal.primeCompl M)
end Support
section Cycle
variable {K : Type*} [Fintype K] [DecidableEq K] (ι : K → Type*) (F : Type*) [Field F]
variable (M : Type*) [AddCommGroup M] [Module (MRing ι F) M]
def topSupport (d : ℕ) : Set (PrimeSpectrum (MRing ι F)) :=
  {p | p ∈ Module.support (MRing ι F) M ∧ IsMultiProjPrime p.asIdeal ∧
    ringKrullDim (MRing ι F ⧸ p.asIdeal) = ((d + Fintype.card K : ℕ) : WithBot ℕ∞)}
def modIntNum (d : ℕ) (a : K → ℤ) : ℤ :=
  ∑ᶠ (p : PrimeSpectrum (MRing ι F)) (_ : p ∈ topSupport ι F M d),
    ((modMultAt M p).toNat : ℤ) * intNum F p.asIdeal (fun _ : Fin d => a)
end Cycle
def degSize {K : Type*} [Fintype K] (a : K → ℤ) : ℝ := ∑ k, (a k : ℝ)
section Statements
def MultigradedFiltration.Statement : Prop :=
  ∀ (F : Type u) [Field F] (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type)
    [∀ k, Fintype (ι k)] (M : Type u) [AddCommGroup M] [Module (MRing ι F) M] [Module F M]
    [IsScalarTower F (MRing ι F) M] (ℳ : (K → ℤ) → Submodule F M),
    IsMultigraded ι ℳ → Module.Finite (MRing ι F) M →
    ∃ (n : ℕ) (x : Fin n → M) (c : Fin n → K → ℤ) (q : Fin n → Ideal (MRing ι F)),
      (∀ j, x j ∈ ℳ (c j)) ∧
      (∀ j, (q j).IsPrime ∧ IsMultiHomogIdeal (q j)) ∧
      Submodule.span (MRing ι F) (Set.range x) = ⊤ ∧
      ∀ j (f : MRing ι F),
        f • x j ∈ Submodule.span (MRing ι F) (x '' {i | i < j}) ↔ f ∈ q j
def HilbertDimZero.Statement : Prop :=
  ∀ (F : Type u) [Field F] (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type)
    [∀ k, Fintype (ι k)] (q : Ideal (MRing ι F)),
    IsMultiProjPrime q → ringKrullDim (MRing ι F ⧸ q) = ((Fintype.card K : ℕ) : WithBot ℕ∞) →
    ∃ a₀ : ℕ, ∀ a : K → ℤ, (∀ k, (a₀ : ℤ) ≤ a k) →
      hilbFn q a = intNum F q (Fin.elim0 : Fin 0 → K → ℤ)
def HilbertPrime.Statement : Prop :=
  ∀ (F : Type u) [Field F] (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type)
    [∀ k, Fintype (ι k)] (d : ℕ) (q : Ideal (MRing ι F)),
    IsMultiProjPrime q → ringKrullDim (MRing ι F ⧸ q) = ((d + Fintype.card K : ℕ) : WithBot ℕ∞) →
    ∃ (a₀ : ℕ) (C : ℝ), ∀ a : K → ℤ, (∀ k, (a₀ : ℤ) ≤ a k) →
      |(hilbFn q a : ℝ) - (intNum F q (fun _ : Fin d => a) : ℝ) / (d.factorial : ℝ)| ≤
        C * (degSize a + 1) ^ ((d : ℤ) - 1)
def HilbertModule.Statement : Prop :=
  ∀ (F : Type u) [Field F] (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type)
    [∀ k, Fintype (ι k)] (M : Type u) [AddCommGroup M] [Module (MRing ι F) M] [Module F M]
    [IsScalarTower F (MRing ι F) M] (ℳ : (K → ℤ) → Submodule F M) (d : ℕ),
    IsMultigraded ι ℳ → Module.Finite (MRing ι F) M →
    (∀ p ∈ Module.support (MRing ι F) M, IsMultiProjPrime p.asIdeal →
      ringKrullDim (MRing ι F ⧸ p.asIdeal) ≤ ((d + Fintype.card K : ℕ) : WithBot ℕ∞)) →
    ∃ (a₀ : ℕ) (C : ℝ), ∀ a : K → ℤ, (∀ k, (a₀ : ℤ) ≤ a k) →
      |(modHilb ℳ a : ℝ) - (modIntNum ι F M d a : ℝ) / (d.factorial : ℝ)| ≤
        C * (degSize a + 1) ^ ((d : ℤ) - 1)
def HilbertIncrement.Statement : Prop :=
  ∀ (F : Type u) [Field F] (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type)
    [∀ k, Fintype (ι k)] (d : ℕ) (q : Ideal (MRing ι F)) (b : K) (i : ι b),
    IsMultiProjPrime q → ringKrullDim (MRing ι F ⧸ q) = ((d + Fintype.card K : ℕ) : WithBot ℕ∞) →
    1 ≤ d → (X ⟨b, i⟩ : MRing ι F) ∉ q →
    (∀ a : K → ℤ, hilbFn q a - hilbFn q (a - Pi.single b 1) =
        hilbFn (q ⊔ Ideal.span {(X ⟨b, i⟩ : MRing ι F)}) a) ∧
    ∀ W : Ideal (MRing ι F), IsMultiProjPrime W → q ⊔ Ideal.span {(X ⟨b, i⟩ : MRing ι F)} ≤ W →
      ringKrullDim (MRing ι F ⧸ W) ≤ ((d - 1 + Fintype.card K : ℕ) : WithBot ℕ∞)
def RankOfSections.Statement : Prop :=
  ∀ (ι : Unit → Type) [∀ k, Fintype (ι k)] (D : ℕ) (q : Ideal (MRing ι ℚ)),
    IsMultiProjPrime q → ringKrullDim (MRing ι ℚ ⧸ q) = ((D + 1 : ℕ) : WithBot ℕ∞) →
    (fun n : ℕ => (hilbFn q (fun _ => (n : ℤ)) : ℝ) -
        (intNum ℚ q (fun _ : Fin D => fun _ => (1 : ℤ)) : ℝ) * (n : ℝ) ^ D / (D.factorial : ℝ))
      =O[Filter.atTop] fun n : ℕ => (n : ℝ) ^ ((D : ℤ) - 1)
def MixedNumberPolynomial.Statement : Prop :=
  ∀ (F : Type u) [Field F] (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type)
    [∀ k, Fintype (ι k)] (d : ℕ) (q : Ideal (MRing ι F)),
    IsMultiProjPrime q → ringKrullDim (MRing ι F ⧸ q) = ((d + Fintype.card K : ℕ) : WithBot ℕ∞) →
    (∀ (σ : Equiv.Perm (Fin d)) (bs : Fin d → K → ℤ), intNum F q (bs ∘ σ) = intNum F q bs) ∧
    ∀ (bs : Fin d → K → ℤ) (j : Fin d) (b b' : K → ℤ),
      intNum F q (Function.update bs j (b + b')) =
        intNum F q (Function.update bs j b) + intNum F q (Function.update bs j b')
end Statements
section Examples
variable {K : Type*} [DecidableEq K] (ι : K → Type*) (F : Type*) [Field F]
def blockWeightInt : (Σ k, ι k) → K → ℤ := fun v => Pi.single v.1 1
end Examples
end
end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.HilbertSamuel


