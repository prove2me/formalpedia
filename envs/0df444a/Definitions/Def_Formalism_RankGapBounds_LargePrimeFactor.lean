-- Prove2me | Definitions.Def_Formalism_RankGapBounds_LargePrimeFactor
-- name    : Formalism_RankGapBounds_LargePrimeFactor
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T17:05:30.803187+00:00
-- url     : https://prove2.me/theorems/7c2d5720-d980-4822-baf6-1e0ba93df9a3
-- title:
--   Large Prime Factor
-- statement:
--   Definitions and structural lemmas for Large Prime Factor, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/RankGapBounds/LargePrimeFactor.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Real Finset
namespace Formalism.RankGapBounds.ChebyshevFactorialBounds
noncomputable section
def primesUpTo (X : ℕ) : Finset ℕ := (Finset.range (X + 1)).filter Nat.Prime
def leastRes (a : ℤ) (l : ℕ) : ℕ := sInf {d : ℕ | 1 ≤ d ∧ (l : ℤ) ∣ a - (d : ℤ)}
structure Data (ι : Type) where

  T2 : Finset ι

  Nr : ℕ
  k : ℕ
  t : ℕ
  m : ℕ
  h : ℕ
  S : ℕ
  eta' : ℕ
  Wthin : ℕ
  D0 : ℕ
  lJ : ℝ
  Kexc : ℝ
  q : ι → ℕ
  j : ι → ℕ
  xlo : ι → ℤ
  xhi : ι → ℤ
  maxB : ι → ℤ
  Exc : Finset ℕ
  Bad : Finset ℕ
  J : ℕ → ℕ
  ex : ι → ℕ → ℕ
  ecl : ι → ℕ → ℕ
  erest : ι → ℕ → ℕ
  mw : ι → ℕ → ℕ
  mwF : ι → ℕ → ℕ
namespace Data
def kap {ι : Type} (D : Data ι) (l : ℕ) : ℕ := D.h / (l - 1)
def Icl {ι : Type} (D : Data ι) (τ : ι) (l : ℕ) : ℝ := by
  classical
  exact if ∃ y : ℤ, D.xlo τ ≤ y ∧ y ≤ D.xhi τ ∧ (l : ℤ) ∣ y - D.maxB τ then 1 else 0
def d0 {ι : Type} (D : Data ι) (τ : ι) (l : ℕ) : ℕ := leastRes (D.xlo τ - D.maxB τ) l
def depth {ι : Type} (D : Data ι) (τ : ι) (l : ℕ) : ℕ :=
  D.q τ * D.h + (l * D.mwF τ l + D.mw τ l) * (D.t + 2 * D.kap l)
def cW {ι : Type} (D : Data ι) (τ : ι) (l : ℕ) : ℝ :=
  ((D.q τ : ℝ) + 2 * (D.j τ : ℝ)) * ((D.h : ℝ) + (D.Nr : ℝ)) / ((l : ℝ) - 1)
    + (D.ecl τ l : ℝ)
    + (D.k : ℝ) * ((D.S : ℝ) / (l : ℝ) + D.Icl τ l)
    + min (min (D.k : ℝ) (D.t : ℝ)) ((D.depth τ l : ℝ) / (D.d0 τ l : ℝ))
    + ((D.depth τ l : ℝ) / (l : ℝ)) * max 0 (1 + Real.log ((D.h : ℝ) / (l : ℝ)))
def ExcCost {ι : Type} (D : Data ι) : Prop :=
  ∀ l ∈ D.Exc, (D.J l : ℝ) * Real.log (l : ℝ) ≤ D.Kexc
def SumExactBound {ι : Type} [Fintype ι] (D : Data ι) : Prop :=
  ∀ l : ℕ, l.Prime → l ∉ D.Exc → D.J l ≤ ∑ τ, D.ex τ l
def ExactExpTotal {ι : Type} (D : Data ι) : Prop :=
  ∀ (τ : ι) (l : ℕ), l.Prime → l ∉ D.Exc →
    (D.ex τ l : ℝ) ≤ (D.Nr : ℝ) ^ 2 * Real.logb (l : ℝ) (2 * (D.h : ℝ) + (D.Nr : ℝ))
def ExactExpStop {ι : Type} (D : Data ι) : Prop :=
  ∀ (τ : ι) (l : ℕ), l.Prime → D.h + D.Nr < l → D.ex τ l = 0
def ThinStop {ι : Type} (D : Data ι) : Prop :=
  ∀ τ : ι, τ ∉ D.T2 → ∀ l : ℕ, l.Prime → D.Wthin < l → D.ex τ l = 0
def CloudRestCut {ι : Type} (D : Data ι) : Prop :=
  ∀ τ ∈ D.T2, ∀ l : ℕ, l.Prime → l ∉ D.Exc →
    (D.ex τ l : ℝ) ≤ (D.ecl τ l : ℝ) + (D.erest τ l : ℝ)
      + (D.k : ℝ) * ((D.Nr : ℝ) - (D.k : ℝ)) * (Nat.log l (2 * D.h + D.Nr) : ℝ)
def CloudBound {ι : Type} (D : Data ι) : Prop :=
  ∀ τ ∈ D.T2, ∀ l : ℕ, l.Prime → l ∉ D.Exc →
    D.ecl τ l ≤ D.k ^ 2 * Nat.log l (D.S + D.k) ∧ (D.S + D.k < l → D.ecl τ l = 0)
def RestBound {ι : Type} (D : Data ι) : Prop :=
  ∀ τ ∈ D.T2, ∀ l : ℕ, l.Prime → l ∉ D.Exc →
    (D.eta' + D.Nr < l → D.erest τ l = 0) ∧
    (D.erest τ l : ℝ) ≤ ((D.Nr : ℝ) - (D.k : ℝ)) ^ 2 * Real.logb (l : ℝ) (2 * (D.h : ℝ) + (D.Nr : ℝ))
def BlockIdealBound {ι : Type} [Fintype ι] [DecidableEq ι] (D : Data ι) : Prop :=
  ∀ l : ℕ, l.Prime → l ∉ D.Exc → D.h + D.Nr < l ^ 2 → D.Nr + 1 < l → D.t + 2 * D.kap l < l →
    (D.J l : ℝ) ≤ ∑ τ, (if τ ∈ D.T2 then min (D.ex τ l : ℝ) (D.cW τ l) else (D.ex τ l : ℝ))
def NoWindowResidue {ι : Type} (D : Data ι) : Prop :=
  ∀ l : ℕ, l.Prime → D.lJ < (l : ℝ) → l ∉ D.Bad → l ∉ D.Exc →
    ∀ τ : ι, D.mw τ l = 0 ∧ D.mwF τ l = 0
def Inputs {ι : Type} [Fintype ι] [DecidableEq ι] (D : Data ι) : Prop :=
  D.ExcCost ∧ D.SumExactBound ∧ D.ExactExpTotal ∧ D.ExactExpStop ∧ D.ThinStop ∧ D.CloudRestCut ∧
    D.CloudBound ∧ D.RestBound ∧ D.BlockIdealBound ∧ D.NoWindowResidue
def Params {ι : Type} (D : Data ι) : Prop :=
  1 ≤ D.h ∧ D.k ≤ D.Nr ∧ 2 ≤ D.h + D.Nr ∧ 1 ≤ D.D0 ∧ 1 < D.lJ ∧
    (D.Nr : ℝ) + 1 ≤ D.lJ ∧ (D.h : ℝ) + (D.Nr : ℝ) < D.lJ ^ 2 ∧ (D.S : ℝ) + (D.k : ℝ) ≤ D.lJ ∧
    (D.t : ℝ) + 2 * (D.h : ℝ) / (D.lJ - 1) ≤ D.lJ ∧
    ∀ τ ∈ D.T2, 0 ≤ D.maxB τ ∧ D.maxB τ + (D.D0 : ℤ) ≤ D.xlo τ ∧ D.xlo τ ≤ D.xhi τ ∧
      D.xhi τ - D.xlo τ ≤ (D.S : ℤ) ∧ D.xhi τ ≤ (D.h : ℤ) ∧ D.q τ + D.j τ ≤ D.m
def rhs {ι : Type} [Fintype ι] (D : Data ι) (C : ℝ) : ℝ :=
  (D.Exc.card : ℝ) * D.Kexc
  + ((D.Bad.card : ℝ) * (Fintype.card ι : ℝ) + ((Fintype.card ι : ℝ) - (D.T2.card : ℝ)) * (D.Wthin : ℝ))
      * (D.Nr : ℝ) ^ 2 * Real.log (2 * (D.h : ℝ) + (D.Nr : ℝ))
  + (D.T2.card : ℝ) *
    ( (D.k : ℝ) ^ 2 * ((D.S : ℝ) + (D.k : ℝ)) * Real.log ((D.S : ℝ) + (D.k : ℝ))
      + ((D.eta' : ℝ) + (D.Nr : ℝ)) * ((D.Nr : ℝ) - (D.k : ℝ)) ^ 2
          * Real.log (2 * (D.h : ℝ) + (D.Nr : ℝ))
      + D.lJ * (D.k : ℝ) * ((D.Nr : ℝ) - (D.k : ℝ)) * Real.log (2 * (D.h : ℝ) + (D.Nr : ℝ))
      + (D.k : ℝ) * ((D.S : ℝ) + 1) * Real.log ((D.h : ℝ) + (D.Nr : ℝ))
      + (D.k : ℝ) * Real.log ((D.h : ℝ) + (D.Nr : ℝ))
      + (D.m : ℝ) * (D.h : ℝ) * Real.log ((D.h : ℝ) + (D.Nr : ℝ))
          * (1 + Real.log ((D.h : ℝ) + (D.Nr : ℝ)))
      + C * ( (D.m : ℝ) * ((D.h : ℝ) + (D.Nr : ℝ)) * Real.log ((D.h : ℝ) + (D.Nr : ℝ))
          + (D.k : ℝ) * (D.S : ℝ) * Real.log ((D.h : ℝ) + (D.Nr : ℝ))
          + (D.m : ℝ) * (D.h : ℝ) * ((D.h : ℝ) + (D.Nr : ℝ)) / (D.D0 : ℝ)
          + (D.m : ℝ) * (D.h : ℝ) * (1 + Real.log (D.h : ℝ)) * Real.log ((D.h : ℝ) + (D.Nr : ℝ)) ) )
end Data
def Corollary : Prop :=
  ∃ C : ℝ, 0 < C ∧
    ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (D : Data ι), D.Inputs → D.Params →
      ∀ X : ℕ, ∑ l ∈ primesUpTo X, (D.J l : ℝ) * Real.log (l : ℝ) ≤ D.rhs C
def ChebyshevTheta : Prop :=
  ∀ n : ℕ, ∑ p ∈ primesUpTo n, Real.log (p : ℝ) ≤ Real.log 4 * (n : ℝ)
def MertensType : Prop :=
  ∃ C : ℝ, ∀ n : ℕ, 2 ≤ n → ∑ p ∈ primesUpTo n, Real.log (p : ℝ) / ((p : ℝ) - 1) ≤ C * Real.log (n : ℝ)
def LargePrimeFactor : Prop :=
  ∀ (L : ℝ) (z : ℕ), 0 ≤ L → 1 ≤ z → (z : ℝ) < L ^ 2 →
    (z.primeFactors.filter (fun p : ℕ => L < (p : ℝ))).card ≤ 1
def HarmonicLog : Prop :=
  ∀ n : ℕ, 1 ≤ n → ∑ d ∈ Finset.Icc 1 n, (1 : ℝ) / (d : ℝ) ≤ 1 + Real.log (n : ℝ)
def LeastResFacts : Prop :=
  ∀ (a : ℤ) (l : ℕ), 1 ≤ l →
    1 ≤ leastRes a l ∧ leastRes a l ≤ l ∧ (l : ℤ) ∣ a - (leastRes a l : ℤ) ∧
      (1 ≤ a → a < (l : ℤ) → (leastRes a l : ℤ) = a)
end
end Formalism.RankGapBounds.ChebyshevFactorialBounds


