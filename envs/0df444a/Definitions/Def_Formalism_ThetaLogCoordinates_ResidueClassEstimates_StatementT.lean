-- Prove2me | Definitions.Def_Formalism_ThetaLogCoordinates_ResidueClassEstimates_StatementT
-- name    : Formalism_ThetaLogCoordinates_ResidueClassEstimates_StatementT
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T21:17:23.174293+00:00
-- url     : https://prove2.me/theorems/2fc286ad-0759-4870-9b28-0598a3bb9fc3
-- title:
--   Statement T
-- statement:
--   Definitions and structural lemmas for Statement T, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/ResidueClassEstimates/StatementT.lean

import Definitions.Def_Formalism_ThetaLogCoordinates_ResidueClassEstimates_Letters
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
open Finset
namespace Formalism.InvariantFactorPaths.BranchingDimensions
open Letters
def Letters.nVec (D : Letters) (i : ℕ) : ℕ := ((Icc 1 i).filter fun l => D.vec l = true).card
def Letters.nCov (D : Letters) (i : ℕ) : ℕ := ((Icc 1 i).filter fun l => D.vec l = false).card
def PathEntryBounds : Prop :=
  ∀ (D : Letters) (mu : D.Stages), D.Wf → D.IsPATH mu →
    (∀ i, i ≤ D.n0 →
      -((∑ l ∈ (Icc 1 i).filter (fun l => D.vec l = false), D.B l : ℕ) : ℤ) ≤ ent mu i (D.k - 1) ∧
      ent mu i 0 ≤ ((∑ l ∈ (Icc 1 i).filter (fun l => D.vec l = true), D.B l : ℕ) : ℤ)) ∧
    ∀ i, i ≤ D.Ns → (∀ m, D.nVec i ≤ m → m < D.k → ent mu i m ≤ 0) ∧
      ∀ m, m + D.nCov i < D.k → 0 ≤ ent mu i m
def Letters.IsPre (D : Letters) (mu : D.Stages) : Prop :=
  (∀ m, ent mu 0 m = 0) ∧ (∀ i, i ≤ D.n0 → Dom D.k (ent mu i)) ∧
  (∀ i, 1 ≤ i → i ≤ D.n0 → D.vec i = true → HStrip D.k (ent mu (i - 1)) (ent mu i)) ∧
  (∀ i, 1 ≤ i → i ≤ D.n0 → D.vec i = false → HStrip D.k (ent mu i) (ent mu (i - 1))) ∧
  (∀ i, 1 ≤ i → i ≤ D.n0 → D.vec i = true →
    wsize D.k (ent mu i) - wsize D.k (ent mu (i - 1)) = D.B i) ∧
  (∀ i, 1 ≤ i → i ≤ D.n0 → D.vec i = false →
    wsize D.k (ent mu (i - 1)) - wsize D.k (ent mu i) = D.B i)
def PathInterlacingCriterion : Prop :=
  ∀ (D : Letters) (mu : D.Stages), D.Wf →
    (D.IsPre mu → (∀ i', 1 ≤ i' → i' ≤ D.r → ∀ m, m < i' → ent mu (D.n0 + i') m = D.be) →
      (D.IsPATH mu ↔ ∀ i', 1 ≤ i' → i' ≤ D.r →
        Interl (D.k - i') (stage mu (D.n0 + i')) (stage mu (D.n0 + i' - 1)))) ∧
    (D.IsPATH mu →
      -(D.beNeg : ℤ) ≤ ent mu D.n0 (D.k - 1) ∧ ent mu D.n0 0 ≤ (D.bePos : ℤ) ∧
      (∀ i', i' ≤ D.r → ∀ l, l < D.k - i' →
        ent mu D.n0 (D.k - 1) ≤ stage mu (D.n0 + i') l ∧ stage mu (D.n0 + i') l ≤ ent mu D.n0 0) ∧
      ∀ i', 1 ≤ i' → i' ≤ D.r →
        wsize D.k (ent mu (D.n0 + i')) - wsize D.k (ent mu (D.n0 + i' - 1)) =
          (D.be : ℤ) - (wsize (D.k - (i' - 1)) (stage mu (D.n0 + i' - 1)) -
            wsize (D.k - i') (stage mu (D.n0 + i'))) ∧
        (D.beNeg : ℤ) ≤ wsize D.k (ent mu (D.n0 + i')) - wsize D.k (ent mu (D.n0 + i' - 1)) ∧
        wsize D.k (ent mu (D.n0 + i')) - wsize D.k (ent mu (D.n0 + i' - 1)) ≤ (D.be : ℤ) + D.beNeg)
def LogBinomialProperties : Prop :=
  ∀ k' : ℕ,
    fT k' 0 = 0 ∧ (∀ y : ℕ, fT k' y = Real.log ((y + k').choose k')) ∧
    (∀ y : ℝ, 0 ≤ y → HasDerivAt (fT k') (fT' k' y) y) ∧
    (∀ y : ℝ, 0 ≤ y → 1 ≤ k' → 0 < fT' k' y) ∧
    (∀ y y' : ℝ, 0 ≤ y → y ≤ y' → fT' k' y' ≤ fT' k' y) ∧
    (∀ y : ℝ, 0 ≤ y → 1 ≤ k' → (k' : ℝ) / (y + k') ≤ fT' k' y ∧ fT' k' y ≤ (k' : ℝ) / (y + 1)) ∧
    (∀ y : ℝ, (k' : ℝ) ≤ y → 1 ≤ k' → (k' : ℝ) / (2 * y) ≤ fT' k' y) ∧
    (∀ y y' : ℝ, (k' : ℝ) ≤ y → 4 * y ≤ y' → fT' k' y' ≤ fT' k' y / 2) ∧
    (∀ x y : ℝ, 0 ≤ x → 0 ≤ y → fT k' x - fT k' y ≤ fT' k' y * (x - y))
def LogWeylDimensionEstimate : Prop :=
  ∀ (r K Ns n : ℕ) (la : ℕ → ℤ) (A0 : ℝ), 2 * Ns ≤ K → K ≤ n → n ≤ r + K → Dom n la →
    ((range n).filter fun m => 0 < la m).card ≤ Ns → ((range n).filter fun m => la m < 0).card ≤ Ns →
    ((max (la 0) 0 + max (-(la (n - 1))) 0 : ℤ) : ℝ) ≤ A0 →
    0 < weylDim n la ∧
    -(2 * (Ns : ℝ) ^ 2 * Real.log (1 + A0)) ≤
      Real.log (weylDim n la) - (∑ m ∈ range n, fT (K - 2 * Ns) ((max (la m) 0 : ℤ) : ℝ)) -
        (∑ m ∈ range n, fT (K - 2 * Ns) ((max (-(la m)) 0 : ℤ) : ℝ)) ∧
    Real.log (weylDim n la) - (∑ m ∈ range n, fT (K - 2 * Ns) ((max (la m) 0 : ℤ) : ℝ)) -
        (∑ m ∈ range n, fT (K - 2 * Ns) ((max (-(la m)) 0 : ℤ) : ℝ)) ≤
      (2 * (Ns : ℝ) * r + 8 * (Ns : ℝ) ^ 2) * Real.log (1 + A0)
def LogRankEstimate : Prop :=
  ∀ (D : Letters) (A0 : ℝ), 0 ≤ A0 → 1 ≤ D.r → D.r ≤ D.Ns → 2 * D.Ns ≤ D.K → (∀ i, 1 ≤ i → i ≤ D.n0 → (D.B i : ℝ) ≤ A0) →
    0 ≤ Real.log (D.rankAA : ℝ) - ∑ i ∈ Icc 1 D.n0, fT D.k' (D.B i) ∧
    Real.log (D.rankAA : ℝ) - ∑ i ∈ Icc 1 D.n0, fT D.k' (D.B i) ≤
      (D.Ns : ℝ) * ((D.r : ℝ) + 2 * D.Ns) * Real.log (1 + A0)
def PathTailBounds : Prop :=
  ∀ (D : Letters) (mu : D.Stages), D.Wf → D.IsPATH mu →
    (∀ i u, i ≤ D.Ns → tailPos (D.stLen i) (stage mu i) u ≤ (D.SPos u i : ℤ) ∧
      tailNeg (D.stLen i) (stage mu i) u ≤ (D.SNeg u i : ℤ)) ∧
    (∀ (i₀ u : ℕ) (X : ℝ), i₀ ≤ D.Ns → 0 ≤ X →
      ((tailPos (D.stLen i₀) (stage mu i₀) u : ℤ) : ℝ) ≤ (D.SPos u i₀ : ℝ) - X →
      ((tailPos (D.stLen D.Ns) (stage mu D.Ns)
        (u + ((Icc (i₀ + 1) D.n0).filter fun l => D.vec l = true).card) : ℤ) : ℝ) ≤
        (D.SPos (u + ((Icc (i₀ + 1) D.n0).filter fun l => D.vec l = true).card) D.n0 : ℝ) - X) ∧
    (∀ (i₀ u : ℕ) (X : ℝ), i₀ ≤ D.Ns → 0 ≤ X →
      ((tailNeg (D.stLen i₀) (stage mu i₀) u : ℤ) : ℝ) ≤ (D.SNeg u i₀ : ℝ) - X →
      ((tailNeg (D.stLen D.Ns) (stage mu D.Ns)
        (u + ((Icc (i₀ + 1) D.n0).filter fun l => D.vec l = false).card) : ℤ) : ℝ) ≤
        (D.SNeg (u + ((Icc (i₀ + 1) D.n0).filter fun l => D.vec l = false).card) D.n0 : ℝ) - X)
def LogBinomialDeficit : Prop :=
  ∀ (k' L : ℕ) (al Bs : ℕ → ℝ), 1 ≤ k' → (∀ l, 0 ≤ al l) →
    (∀ l, l < L → (k' : ℝ) ≤ Bs l) → (∀ l, l + 1 < L → 4 * Bs (l + 1) ≤ Bs l) →
    (∀ u, u < L → (∑ l ∈ Ico u L, al l) - (∑ l ∈ Ico u L, Bs l) ≤ 0) →
    (∀ u, u < L → fT' k' (Bs u) / 2 ≤ fT' k' (Bs u) - (if u = 0 then 0 else fT' k' (Bs (u - 1)))) ∧
    (∑ l ∈ range L, fT k' (al l)) - (∑ l ∈ range L, fT k' (Bs l)) ≤
      ∑ u ∈ range L, (fT' k' (Bs u) - (if u = 0 then 0 else fT' k' (Bs (u - 1)))) *
        ((∑ l ∈ Ico u L, al l) - (∑ l ∈ Ico u L, Bs l)) ∧
    (∑ u ∈ range L, (fT' k' (Bs u) - (if u = 0 then 0 else fT' k' (Bs (u - 1)))) *
        ((∑ l ∈ Ico u L, al l) - (∑ l ∈ Ico u L, Bs l))) ≤ 0 ∧
    ∀ (u₀ : ℕ) (X : ℝ), u₀ < L → 0 ≤ X → (∑ l ∈ Ico u₀ L, al l) - (∑ l ∈ Ico u₀ L, Bs l) ≤ -X →
      (∑ l ∈ range L, fT k' (al l)) - (∑ l ∈ range L, fT k' (Bs l)) ≤ -(X * fT' k' (Bs u₀) / 2) ∧
      -(X * fT' k' (Bs u₀) / 2) ≤ -(X * k' / (4 * Bs u₀))
def PathCountBound : Prop :=
  ∀ (D : Letters) (a : ℝ) (p : ℕ), D.Wf → D.Hyp a p →
    ∀ PP : Finset D.Stages, (∀ mu ∈ PP, D.IsPATH mu) →
      (PP.card : ℝ) ≤ (1 + 2 * a * D.Ns) ^ (2 * D.Ns ^ 2) ∧
      (1 + 2 * a * D.Ns) ^ (2 * D.Ns ^ 2) ≤ a ^ (6 * D.Ns ^ 2)
def Letters.TData (D : Letters) (p : ℕ) (La : ℝ) (b : ℕ → ℝ) : Prop :=
  0 < La ∧ ∀ i, D.r < i → i ≤ D.Ns → 0 < b i ∧ ∀ l, 1 ≤ l → l < i → l ≤ D.n0 → (D.B l : ℝ) ≤ 4 * b i / p
def Letters.XT (D : Letters) (p : ℕ) (La : ℝ) (b : ℕ → ℝ) : ℕ → ℝ := fun i => La * b i / (p * D.k)
def PathWeightBound : Prop :=
  ∀ (D : Letters) (a : ℝ) (p : ℕ) (La : ℝ) (b : ℕ → ℝ), D.Wf → D.Hyp a p → D.TData p La b →
    ∀ mu : D.Stages, D.IsPATH mu →
      wt mu ≤ Real.exp (9 * (D.Ns : ℝ) ^ 2 * Real.log (1 + 2 * a * D.Ns)) * D.rankAA ∧
      (¬ D.Typical (D.XT p La b) mu →
        wt mu ≤ Real.exp (9 * (D.Ns : ℝ) ^ 2 * Real.log (1 + 2 * a * D.Ns) -
          min (La * D.k' / (16 * D.k)) ((D.k' : ℝ) / 12)) * D.rankAA)
def AtypicalWeightBound : Prop :=
  ∀ (D : Letters) (a : ℝ) (p : ℕ) (La : ℝ) (b : ℕ → ℝ), D.Wf → D.Hyp a p → D.TData p La b →
    ∀ PP : Finset D.Stages, (∀ mu ∈ PP, D.IsPATH mu ∧ ¬ D.Typical (D.XT p La b) mu) →
      ∑ mu ∈ PP, wt mu ≤ Real.exp (11 * (D.Ns : ℝ) ^ 2 * Real.log (1 + 2 * a * D.Ns) -
          min La (D.k : ℝ) / 32) * D.rankAA ∧
      Real.exp (11 * (D.Ns : ℝ) ^ 2 * Real.log (1 + 2 * a * D.Ns) - min La (D.k : ℝ) / 32) * D.rankAA ≤
        a ^ (33 * D.Ns ^ 2) * Real.exp (-(min La (D.k : ℝ) / 32)) * D.rankAA ∧
      (1088 * (D.Ns : ℝ) ^ 2 * Real.log a ≤ La → 1088 * (D.Ns : ℝ) ^ 2 * Real.log a ≤ D.k →
        ∑ mu ∈ PP, wt mu ≤ (a ^ (D.Ns ^ 2))⁻¹ * D.rankAA)
def TypicalRowSumBounds : Prop :=
  ∀ (D : Letters) (a : ℝ) (p : ℕ) (La : ℝ) (b : ℕ → ℝ), D.Wf → D.Hyp a p → D.TData p La b →
    ∀ mu : D.Stages, D.IsPATH mu →
      (∀ i m, i ≤ D.Ns → m < D.r → 0 ≤ ent mu i m) ∧
      (D.Typical (D.XT p La b) mu →
        (∀ i, 1 ≤ i → i ≤ D.Ns → D.vec i = false →
          ((wsize D.r (ent mu (i - 1)) - wsize D.r (ent mu i) : ℤ) : ℝ) ≤ D.XT p La b i) ∧
        ∀ i, D.r < i → i ≤ D.Ns → D.vec i = true →
          ((wsize D.K (kaRows mu i) - wsize D.K (kaRows mu (i - 1)) : ℤ) : ℝ) ≤
            D.XT p La b i + (169 / 164 : ℝ) * D.Bo i)
def extW {n : ℕ} (la : Fin n → ℤ) : ℕ → ℤ := fun m => if h : m < n then la ⟨m, h⟩ else 0
def PieriDim : Prop :=
  ∀ (n : ℕ) (mu : Fin n → ℤ) (B : ℕ), 1 ≤ n → Dom n (extW mu) →
    ∑ᶠ (mu' : Fin n → ℤ) (_ : HStrip n (extW mu) (extW mu') ∧ wsize n (extW mu') - wsize n (extW mu) = B),
      weylDim n (extW mu') = weylDim n (extW mu) * ((B + n - 1).choose (n - 1) : ℝ)
def BranchDim : Prop :=
  ∀ (n : ℕ) (mu : Fin (n + 1) → ℤ), Dom (n + 1) (extW mu) →
    ∑ᶠ (la : Fin n → ℤ) (_ : Interl n (extW la) (extW mu)), weylDim n (extW la) = weylDim (n + 1) (extW mu)
def Letters.TotalWeight (D : Letters) : Prop :=
  {mu : D.Stages | D.IsPATH mu}.Finite ∧ ∑ᶠ (mu : D.Stages) (_ : D.IsPATH mu), wt mu = D.rankAA
def TotalWeightOfPieriBranching : Prop := PieriDim → BranchDim → ∀ D : Letters, D.Wf → D.TotalWeight
def LemmaT2share : Prop :=
  ∀ (D : Letters) (a : ℝ) (p : ℕ) (La : ℝ) (b : ℕ → ℝ), D.Wf → D.Hyp a p → D.TData p La b → D.TotalWeight →
    1088 * (D.Ns : ℝ) ^ 2 * Real.log a ≤ La → 1088 * (D.Ns : ℝ) ^ 2 * Real.log a ≤ D.k →
    (1 - (a ^ (D.Ns ^ 2))⁻¹) * D.rankAA ≤
      ∑ᶠ (mu : D.Stages) (_ : D.IsPATH mu ∧ D.Typical (D.XT p La b) mu), wt mu
end Formalism.InvariantFactorPaths.BranchingDimensions


