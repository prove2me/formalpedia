-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_StatementsHilbert
-- name    : GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_StatementsHilbert
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T23:52:21.092218+00:00
-- url     : https://prove2.me/theorems/951a52d7-16e5-49c5-829f-26609b6f5137
-- title:
--   Statements Hilbert
-- statement:
--   Definitions and structural lemmas for Statements Hilbert, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HilbertSamuel/StatementsHilbert.lean

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
namespace GroundTheory.Heights₂.Heights.HilbertSamuel
open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR
noncomputable section
universe u v
section Objects
variable {K : Type*} [DecidableEq K]
def unitDeg (k : K) : K → ℤ := Pi.single k 1
variable [Fintype K] {ι : K → Type*} {F : Type*} [Field F]
structure IsMultigrading (ι : K → Type*) (M : Type*) [AddCommGroup M] [Module (MRing ι F) M] [Module F M]
    (piece : (K → ℤ) → Submodule F M) : Prop where
  internal : DirectSum.IsInternal piece
  smul_mem : ∀ (v : Σ k, ι k) (m : K → ℤ) (x : M), x ∈ piece m →
    (X v : MRing ι F) • x ∈ piece (m + unitDeg v.1)
def modMultAt {R : Type*} [CommRing R] (M : Type*) [AddCommGroup M] [Module (MRing ι R) M]
    (W : Ideal (MRing ι R)) [W.IsPrime] : ℕ∞ :=
  Module.length (Localization.AtPrime W) (LocalizedModule W.primeCompl M)
open Classical in

def topCycleNum (F : Type*) [Field F] (ι : K → Type*) (M : Type*) [AddCommGroup M] [Module (MRing ι F) M] (d : ℕ) (bs : Fin d → K → ℤ) :
    ℤ :=
  ∑ᶠ W : Ideal (MRing ι F),
    if h : IsMultiProjPrime W ∧ Module.annihilator (MRing ι F) M ≤ W ∧
        ringKrullDim (MRing ι F ⧸ W) = ((d + Fintype.card K : ℕ) : WithBot ℕ∞) then
      haveI : W.IsPrime := h.1.isPrime
      ((modMultAt M W).toNat : ℤ) * intNum F W bs
    else 0
end Objects
def MultigradedFiltration.Statement : Prop :=
  ∀ (F : Type u) [Field F] (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type)
    [∀ k, Fintype (ι k)] (M : Type v) [AddCommGroup M] [Module (MRing ι F) M] [Module F M]
    [IsScalarTower F (MRing ι F) M] [Module.Finite (MRing ι F) M]
    (piece : (K → ℤ) → Submodule F M), IsMultigrading ι M piece →
    ∃ (n : ℕ) (N : Fin (n + 1) → Submodule (MRing ι F) M) (x : Fin n → M) (c : Fin n → K → ℤ)
      (q : Fin n → Ideal (MRing ι F)),
      N 0 = ⊥ ∧ N (Fin.last n) = ⊤ ∧
      (∀ j : Fin n, x j ∈ piece (c j) ∧
        N j.succ = N j.castSucc ⊔ Submodule.span (MRing ι F) {x j} ∧
        (q j).IsPrime ∧ IsMultiHomogIdeal (q j) ∧
        ∀ s : MRing ι F, s • x j ∈ N j.castSucc ↔ s ∈ q j) ∧
      ∀ (W : Ideal (MRing ι F)) (hW : W ∈ (Module.annihilator (MRing ι F) M).minimalPrimes),
        (((Finset.univ.filter fun j => q j = W).card : ℕ) : ℕ∞) =
          haveI : W.IsPrime := hW.1.1
          modMultAt M W
def HilbertDimZero.Statement : Prop :=
  ∀ (F : Type u) [Field F] (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type)
    [∀ k, Fintype (ι k)] (q : Ideal (MRing ι F)), IsMultiProjPrime q →
    ringKrullDim (MRing ι F ⧸ q) = ((Fintype.card K : ℕ) : WithBot ℕ∞) →
    ∃ a₀ : ℕ, ∀ a : K → ℕ, (∀ k, a₀ ≤ a k) →
      hilbFn q (fun k => (a k : ℤ)) = intNum F q (![] : Fin 0 → K → ℤ)
def HilbertPrime.AtDim (d : ℕ) : Prop :=
  ∀ (F : Type u) [Field F] (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type)
    [∀ k, Fintype (ι k)] (q : Ideal (MRing ι F)), IsMultiProjPrime q →
    ringKrullDim (MRing ι F ⧸ q) = ((d + Fintype.card K : ℕ) : WithBot ℕ∞) →
    ∃ (a₀ : ℕ) (C : ℝ), ∀ a : K → ℕ, (∀ k, a₀ ≤ a k) →
      |(hilbFn q (fun k => (a k : ℤ)) : ℝ) -
          (intNum F q (fun _ : Fin d => fun k => (a k : ℤ)) : ℝ) / d.factorial| ≤
        C * ((∑ k, (a k : ℝ)) + 1) ^ ((d : ℝ) - 1)
def HilbertPrime.Statement : Prop := ∀ d : ℕ, HilbertPrime.AtDim.{u} d
def HilbertModule.AtDim (d : ℕ) : Prop :=
  ∀ (F : Type u) [Field F] (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type)
    [∀ k, Fintype (ι k)] (M : Type v) [AddCommGroup M] [Module (MRing ι F) M] [Module F M]
    [IsScalarTower F (MRing ι F) M] [Module.Finite (MRing ι F) M]
    (piece : (K → ℤ) → Submodule F M), IsMultigrading ι M piece →
    (∀ W : Ideal (MRing ι F), IsMultiProjPrime W → Module.annihilator (MRing ι F) M ≤ W →
      ringKrullDim (MRing ι F ⧸ W) ≤ ((d + Fintype.card K : ℕ) : WithBot ℕ∞)) →
    ∃ (a₀ : ℕ) (C : ℝ), ∀ a : K → ℕ, (∀ k, a₀ ≤ a k) →
      |(Module.finrank F (piece fun k => (a k : ℤ)) : ℝ) -
          (topCycleNum F ι M d (fun _ : Fin d => fun k => (a k : ℤ)) : ℝ) / d.factorial| ≤
        C * ((∑ k, (a k : ℝ)) + 1) ^ ((d : ℝ) - 1)
def HilbertModule.Statement : Prop := ∀ d : ℕ, HilbertModule.AtDim.{u, v} d
def ModulesFromPrimes.Statement : Prop :=
  ∀ d : ℕ, (∀ e ≤ d, HilbertPrime.AtDim.{u} e) → HilbertModule.AtDim.{u, v} d
def HilbertIncrement.Statement : Prop :=
  ∀ d : ℕ, HilbertModule.AtDim.{u, u} d →
  ∀ (F : Type u) [Field F] (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type)
    [∀ k, Fintype (ι k)] (q : Ideal (MRing ι F)), IsMultiProjPrime q →
    ringKrullDim (MRing ι F ⧸ q) = ((d + 1 + Fintype.card K : ℕ) : WithBot ℕ∞) →
    ∀ b : K, ∃ (a₀ : ℕ) (C : ℝ), ∀ a : K → ℕ, (∀ k, a₀ ≤ a k) →
      |((hilbFn q (fun k => (a k : ℤ)) - hilbFn q ((fun k => (a k : ℤ)) - unitDeg b) : ℤ) : ℝ) -
          (intNum F q (Matrix.vecCons (unitDeg b) fun _ : Fin d => fun k => (a k : ℤ)) : ℝ) /
            d.factorial| ≤
        C * ((∑ k, (a k : ℝ)) + 1) ^ ((d : ℝ) - 1)
open Classical in

def IntersectionRecursion.Statement : Prop :=
  ∀ (F : Type u) [Field F] (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type)
    [∀ k, Fintype (ι k)] (q : Ideal (MRing ι F)) (d : ℕ), IsMultiProjPrime q →
    ringKrullDim (MRing ι F ⧸ q) = ((d + 1 + Fintype.card K : ℕ) : WithBot ℕ∞) →
    ∀ (b : K) (i : ι b), (X ⟨b, i⟩ : MRing ι F) ∉ q → ∀ bs : Fin d → K → ℤ,
      intNum F q (Matrix.vecCons (unitDeg b) bs) =
        ∑ᶠ W : Ideal (MRing ι F),
          if h : IsMultiProjPrime W ∧ q ⊔ Ideal.span {(X ⟨b, i⟩ : MRing ι F)} ≤ W ∧
              ringKrullDim (MRing ι F ⧸ W) = ((d + Fintype.card K : ℕ) : WithBot ℕ∞) then
            haveI : W.IsPrime := h.1.isPrime
            ((multAt (q ⊔ Ideal.span {(X ⟨b, i⟩ : MRing ι F)}) W).toNat : ℤ) * intNum F W bs
          else 0
def MixedNumberPolynomial.Statement : Prop :=
  ∀ (F : Type u) [Field F] (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type)
    [∀ k, Fintype (ι k)] (q : Ideal (MRing ι F)) (d : ℕ), IsMultiProjPrime q →
    ringKrullDim (MRing ι F ⧸ q) = ((d + Fintype.card K : ℕ) : WithBot ℕ∞) →
    (∀ (σ : Equiv.Perm (Fin d)) (bs : Fin d → K → ℤ), intNum F q (bs ∘ σ) = intNum F q bs) ∧
    ∀ (bs : Fin d → K → ℤ) (j : Fin d) (x y : K → ℤ),
      intNum F q (Function.update bs j (x + y)) =
        intNum F q (Function.update bs j x) + intNum F q (Function.update bs j y)
def MultigradedHilbertPolynomial.Statement : Prop :=
  ∀ (F : Type u) [Field F] (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type)
    [∀ k, Fintype (ι k)] (q : Ideal (MRing ι F)) (d : ℕ), IsMultiProjPrime q →
    ringKrullDim (MRing ι F ⧸ q) = ((d + Fintype.card K : ℕ) : WithBot ℕ∞) →
    ∃ (p : MvPolynomial K ℚ) (a₀ : ℕ), p.totalDegree ≤ d ∧
      ∀ a : K → ℕ, (∀ k, a₀ ≤ a k) →
        (hilbFn q (fun k => (a k : ℤ)) : ℚ) = MvPolynomial.eval (fun k => (a k : ℚ)) p
def RankOfSections.Statement : Prop :=
  ∀ (ι₀ : Type) [Fintype ι₀] (q : Ideal (MRing (fun _ : Unit => ι₀) ℚ)) (D : ℕ),
    IsMultiProjPrime q →
    ringKrullDim (MRing (fun _ : Unit => ι₀) ℚ ⧸ q) = ((D + 1 : ℕ) : WithBot ℕ∞) →
    ∃ C : ℝ, ∀ n : ℕ,
      |(hilbFn q (fun _ => (n : ℤ)) : ℝ) -
          (intNum ℚ q (fun _ : Fin D => fun _ => (1 : ℤ)) : ℝ) * (n : ℝ) ^ D / D.factorial| ≤
        C * ((n : ℝ) + 1) ^ ((D : ℝ) - 1)
section Examples
variable {K : Type} [Fintype K] [DecidableEq K] {ι : K → Type} [∀ k, Fintype (ι k)]
variable {F : Type u} [Field F]
def intWeight : (Σ k, ι k) → K → ℤ := fun v => unitDeg v.1
def ringPiece (m : K → ℤ) : Submodule F (MRing ι F) :=
  weightedHomogeneousSubmodule F (intWeight (ι := ι)) m
end Examples
end
end GroundTheory.Heights₂.Heights.HilbertSamuel


