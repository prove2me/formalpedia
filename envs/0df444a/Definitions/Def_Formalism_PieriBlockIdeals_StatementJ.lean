-- Prove2me | Definitions.Def_Formalism_PieriBlockIdeals_StatementJ
-- name    : Formalism_PieriBlockIdeals_StatementJ
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T17:08:15.321173+00:00
-- url     : https://prove2.me/theorems/9935bfc6-50cf-4a26-b613-dd4910b0289d
-- title:
--   Statement J
-- statement:
--   Definitions and structural lemmas for Statement J, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PieriBlockIdeals/StatementJ.lean

import Definitions.Def_Formalism_PieriBlockIdeals_StatementC
import Definitions.Def_Formalism_PieriBlockIdeals_Statement
import Definitions.Def_Formalism_RankGapBounds_CloudMinFalse
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset
namespace Formalism.CohomologicalDescent.Joint
open Formalism.RankGapBounds.ChebyshevFactorialBounds Formalism.RankGapBounds.JumpSetsAlt Formalism.CohomologicalDescent.Cor
noncomputable section
structure Weights {ι : Type} (D : Data ι) where

  U : ι → Fin D.Nr → ℤ

  anti : ∀ τ, StrictAnti (U τ)

  inRange : ∀ τ a, 0 ≤ U τ a ∧ U τ a ≤ (D.h : ℤ)

  k_le : D.k ≤ D.Nr

  cloudIn : ∀ τ ∈ D.T2, ∀ a : Fin D.Nr, (a : ℕ) < D.k → D.xlo τ ≤ U τ a ∧ U τ a ≤ D.xhi τ

  cloudWidth : ∀ τ ∈ D.T2, D.xhi τ - D.xlo τ ≤ (D.S : ℤ)

  restLo : ι → ℤ

  restIn : ∀ τ ∈ D.T2, ∀ a : Fin D.Nr, D.k ≤ (a : ℕ) →
    restLo τ ≤ U τ a ∧ U τ a ≤ restLo τ + (D.eta' : ℤ)

  Wd : ℕ

  thinLo : ι → ℤ

  thinIn : ∀ τ, τ ∉ D.T2 → ∀ a : Fin D.Nr, thinLo τ ≤ U τ a ∧ U τ a ≤ thinLo τ + (Wd : ℤ)

  thinWidth : Wd + D.Nr ≤ D.Wthin
def Weights.cloud {ι : Type} {D : Data ι} (W : Weights D) (τ : ι) : Fin D.k → ℤ :=
  fun a => W.U τ (Fin.castLE W.k_le a)
def Weights.rest {ι : Type} {D : Data ι} (W : Weights D) (τ : ι) : Fin (D.Nr - D.k) → ℤ :=
  fun a => W.U τ ⟨D.k + (a : ℕ), by have := a.isLt; have := W.k_le; omega⟩
def Weights.set {ι : Type} {D : Data ι} (W : Weights D) (τ : ι) : Finset ℤ :=
  Finset.univ.image (W.U τ)
def LemmaAInputs {ι : Type} {D : Data ι} (W : Weights D) : Prop :=
  ∀ l : ℕ, l.Prime → l ∉ D.Exc →
    (∀ τ, D.ex τ l ≤ eExp (W.U τ) l) ∧
    (∀ τ ∈ D.T2, D.ecl τ l ≤ eExp (W.cloud τ) l ∧ D.erest τ l ≤ eExp (W.rest τ) l)
structure Windows {ι : Type} (D : Data ι) (W : Weights D) where
  minB : ι → ℤ

  maxB_eq : ∀ τ, D.maxB τ = minB τ + (D.t : ℤ) - 1
  UF : ι → ℕ → Fin D.Nr → ℤ
  minBF : ι → ℕ → ℤ
  mw_eq : ∀ τ l, D.mw τ l = Formalism.CohomologicalDescent.mwCount l (minB τ) D.t (D.kap l) (W.set τ)
  mwF_eq : ∀ τ l, D.mwF τ l =
    Formalism.CohomologicalDescent.mwCount l (minBF τ l) D.t (D.kap l) (Finset.univ.image (UF τ l))
def SepFrom (l : ℕ) (b : ℤ) (t κ : ℕ) (u : ℤ) : Prop :=
  ∀ x ∈ Finset.Icc (b - κ) (b + t - 1 + κ),
    (0 < |u - x| ∧ |u - x| < (l : ℤ)) ∨ ¬ ((l : ℤ) ∣ u - x)
def Separation {ι : Type} {D : Data ι} {W : Weights D} (B : Windows D W) : Prop :=
  ∀ l : ℕ, l.Prime → D.lJ < (l : ℝ) → l ∉ D.Bad → l ∉ D.Exc → ∀ τ : ι,
    (∀ a : Fin D.Nr, W.U τ a ∉ Finset.Icc (B.minB τ) (B.minB τ + D.t - 1) →
      SepFrom l (B.minB τ) D.t (D.kap l) (W.U τ a)) ∧
    (∀ a : Fin D.Nr, B.UF τ l a ∉ Finset.Icc (B.minBF τ l) (B.minBF τ l + D.t - 1) →
      SepFrom l (B.minBF τ l) D.t (D.kap l) (B.UF τ l a))
def JointExactExpTotal : Prop :=
  ∀ (ι : Type) (D : Data ι) (W : Weights D), LemmaAInputs W → D.ExactExpTotal
def JointExactExpStop5 : Prop :=
  ∀ (ι : Type) (D : Data ι) (W : Weights D), LemmaAInputs W → ExactExpStop5 D
def JointExactExpStopH : Prop :=
  ∀ (ι : Type) (D : Data ι) (W : Weights D), LemmaAInputs W →
    ∀ (τ : ι) (l : ℕ), l.Prime → l ∉ D.Exc → D.h < l → D.ex τ l = 0
def JointThinStop5 : Prop :=
  ∀ (ι : Type) (D : Data ι) (W : Weights D), LemmaAInputs W → ThinStop5 D
def JointCloudBound : Prop :=
  ∀ (ι : Type) (D : Data ι) (W : Weights D), LemmaAInputs W → D.CloudBound
def JointRestBound : Prop :=
  ∀ (ι : Type) (D : Data ι) (W : Weights D), LemmaAInputs W → D.RestBound
def JointNoWindow : Prop :=
  ∀ (ι : Type) (D : Data ι) (W : Weights D) (B : Windows D W), Separation B → D.NoWindowResidue
def JointInputs5 : Prop :=
  ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (D : Data ι) (W : Weights D) (B : Windows D W),
    LemmaAInputs W → Separation B → D.ExcCost → D.SumExactBound → D.CloudRestCut →
      BlockIdealBound5 D → Inputs5 D
def Corollary5J : Prop :=
  ∃ C : ℝ, 0 < C ∧
    ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (D : Data ι) (W : Weights D) (B : Windows D W),
      LemmaAInputs W → Separation B → D.ExcCost → D.SumExactBound → D.CloudRestCut →
        BlockIdealBound5 D → D.Params →
        ∀ X : ℕ, ∑ l ∈ primesUpTo X, (D.J l : ℝ) * Real.log (l : ℝ) ≤ rhs5 D C
def ESplit : Prop :=
  ∀ (ι : Type) (D : Data ι) (W : Weights D) (τ : ι) (l : ℕ),
    eExp (W.U τ) l = eExp (W.cloud τ) l + eExp (W.rest τ) l
      + ∑ a : Fin D.k, ∑ b : Fin (D.Nr - D.k),
          Formalism.RankGapBounds.JumpSetsAlt.maxVal l (W.cloud τ a - W.rest τ b - 1).toNat
def LemmaAFull {ι : Type} {D : Data ι} (W : Weights D) : Prop :=
  ∀ l : ℕ, l.Prime → l ∉ D.Exc → ∀ τ, D.ex τ l ≤ eExp (W.U τ) l
def FormulaParts {ι : Type} {D : Data ι} (W : Weights D) : Prop :=
  ∀ l : ℕ, l.Prime → l ∉ D.Exc → ∀ τ ∈ D.T2,
    D.ecl τ l = eExp (W.cloud τ) l ∧ D.erest τ l = eExp (W.rest τ) l
def JointCloudRestCutE : Prop :=
  ∀ (ι : Type) (D : Data ι) (W : Weights D), LemmaAFull W → FormulaParts W → D.CloudRestCut
def Corollary5E : Prop :=
  ∃ C : ℝ, 0 < C ∧
    ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (D : Data ι) (W : Weights D) (B : Windows D W),
      LemmaAFull W → FormulaParts W → Separation B → D.ExcCost → D.SumExactBound →
        BlockIdealBound5 D → D.Params →
        ∀ X : ℕ, ∑ l ∈ primesUpTo X, (D.J l : ℝ) * Real.log (l : ℝ) ≤ rhs5 D C
end
end Formalism.CohomologicalDescent.Joint


