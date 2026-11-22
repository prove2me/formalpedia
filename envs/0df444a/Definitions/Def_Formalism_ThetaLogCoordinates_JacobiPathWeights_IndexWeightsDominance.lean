-- Prove2me | Definitions.Def_Formalism_ThetaLogCoordinates_JacobiPathWeights_IndexWeightsDominance
-- name    : Formalism_ThetaLogCoordinates_JacobiPathWeights_IndexWeightsDominance
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T21:22:13.881959+00:00
-- url     : https://prove2.me/theorems/69a50682-fcb2-4bf8-9a56-bd9e781901a0
-- title:
--   Index Weights Dominance
-- statement:
--   Definitions and structural lemmas for Index Weights Dominance, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/JacobiPathWeights/IndexWeightsDominance.lean

import Mathlib
import Definitions.Def_Formalism_ThetaLogCoordinates_JacobiPathWeights_ValuationProductsComponents
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
def hatIdx {n : ℕ} (I : ℤ → Finset (Fin n)) (c : ℤ) : Finset (Fin n) := if 1 ≤ c then I c else (I c)ᶜ
def IsStd {n : ℕ} (μ : Fin n → ℤ) (I : ℤ → Finset (Fin n)) : Prop :=
  IsIndex μ I ∧ ∀ c : ℤ, ∀ a < (hatIdx I (c + 1)).card, nthElt (hatIdx I c) a ≤ nthElt (hatIdx I (c + 1)) a
def PathIdx (n N : ℕ) (isVec : ℕ → Bool) (B : ℕ → ℕ) : Type :=
  {x : (ℕ → Fin n → ℤ) × (ℤ → Finset (Fin n)) //
    IsPath n isVec B x.1 N ∧ (∀ i, N < i → x.1 i = 0) ∧ IsStd (x.1 N) x.2}
def polB (R : Type*) [CommRing R] (n N : ℕ) (B : ℕ → ℕ) : Submodule R (MvPolynomial (ℕ × Fin n) R) :=
  ⨅ i : ℕ, weightedHomogeneousSubmodule R (fun x : ℕ × Fin n => if x.1 = i then 1 else 0)
    (if i < N then B i else 0)
def PathIdxFinite : Prop :=
  ∀ (n N : ℕ) (isVec : ℕ → Bool) (B : ℕ → ℕ), Finite (PathIdx n N isVec B)
def PolBRank : Prop :=
  ∀ (n N : ℕ) (B : ℕ → ℕ),
    {e : ℕ × Fin n →₀ ℕ | ∀ i, ∑ a, e (i, a) = if i < N then B i else 0}.ncard =
      ∏ i ∈ range N, (n + B i - 1).choose (B i) ∧
    {e : ℕ × Fin n →₀ ℕ | ∀ i, ∑ a, e (i, a) = if i < N then B i else 0}.Finite ∧
    ∀ (R : Type) [CommRing R], polB R n N B =
      Submodule.span R ((fun e => monomial e (1 : R)) ''
        {e : ℕ × Fin n →₀ ℕ | ∀ i, ∑ a, e (i, a) = if i < N then B i else 0})
def LemmaA2indep : Prop :=
  ∀ (k : Type) [Field k] (n N : ℕ) (isVec : ℕ → Bool) (B : ℕ → ℕ),
    LinearIndependent k (fun x : PathIdx n N isVec B => psiPath k isVec x.1.1 N x.1.2)
def CountP (n N : ℕ) (isVec : ℕ → Bool) (B : ℕ → ℕ) : Prop :=
  Nat.card (PathIdx n N isVec B) = ∏ i ∈ range N, (n + B i - 1).choose (B i)
def CountPle : Prop :=
  ∀ (n N : ℕ) (isVec : ℕ → Bool) (B : ℕ → ℕ),
    Nat.card (PathIdx n N isVec B) ≤ ∏ i ∈ range N, (n + B i - 1).choose (B i)
def PathBasisOfCount : Prop :=
  ∀ (n N : ℕ) (isVec : ℕ → Bool) (B : ℕ → ℕ), CountP n N isVec B →
    ∀ (R : Type) [CommRing R],
      LinearIndependent R (fun x : PathIdx n N isVec B => psiPath R isVec x.1.1 N x.1.2) ∧
      Submodule.span R (Set.range fun x : PathIdx n N isVec B => psiPath R isVec x.1.1 N x.1.2) =
        polB R n N B
def idxWeight {n : ℕ} (I : ℤ → Finset (Fin n)) (m : Fin n) : ℤ :=
  ({c : ℤ | 1 ≤ c ∧ m ∈ I c}.ncard : ℤ) - ({c : ℤ | c ≤ 0 ∧ m ∈ I c}.ncard : ℤ)
def DomLe {n : ℕ} (ν μ : Fin n → ℤ) : Prop :=
  ∑ m, ν m = ∑ m, μ m ∧ ∀ j : ℕ, ∑ m ∈ univ.filter (fun m : Fin n => m.val < j), ν m ≤
    ∑ m ∈ univ.filter (fun m : Fin n => m.val < j), μ m
def IndexWeightsDominance : Prop :=
  ∀ (n : ℕ) (μ : Fin n → ℤ) (I : ℤ → Finset (Fin n)), Antitone μ → IsIndex μ I →
    DomLe (idxWeight I) μ ∧ (idxWeight I = μ → I = canIdx μ)
def torusW {n : ℕ} (isVec : ℕ → Bool) : ℕ × Fin n → (Fin n → ℤ) :=
  fun x => if isVec x.1 then Pi.single x.2 1 else -Pi.single x.2 1
def PsiWeight : Prop :=
  ∀ (R : Type) [CommRing R] (n N : ℕ) (isVec : ℕ → Bool) (B : ℕ → ℕ) (μ : ℕ → Fin n → ℤ)
    (I : ℤ → Finset (Fin n)), IsPath n isVec B μ N → IsIndex (μ N) I →
    IsWeightedHomogeneous (torusW isVec) (psiPath R isVec μ N I) (idxWeight I)
def brk {L : Type*} [CommRing L] {n : ℕ} (g gi : Matrix (Fin n) (Fin n) L) (μ : Fin n → ℤ)
    (I : ℤ → Finset (Fin n)) : L :=
  ∏ᶠ c : ℤ, minorF (if 1 ≤ c then g else gi.transpose) (canIdx μ c) (I c)
def actAll {L : Type*} [CommRing L] {n : ℕ} (isVec : ℕ → Bool) (g gi : Matrix (Fin n) (Fin n) L) :
    MvPolynomial (ℕ × Fin n) L →ₐ[L] MvPolynomial (ℕ × Fin n) L :=
  aeval fun x =>
    if isVec x.1 then Matrix.vecMul (fun b => X (x.1, b)) (g.map C) x.2
    else Matrix.vecMul (fun b => X (x.1, b)) (gi.map C).transpose x.2
def FactEV : Prop :=
  ∀ (L : Type) [CommRing L] (n N : ℕ) (isVec : ℕ → Bool) (B : ℕ → ℕ) (μ : ℕ → Fin n → ℤ)
    (I : ℤ → Finset (Fin n)) (g : (Matrix (Fin n) (Fin n) L)ˣ), IsPath n isVec B μ N → IsIndex (μ N) I →
    (∀ ν : Fin n → ℤ,
      weightedHomogeneousComponent (torusW isVec) ν
        (actAll isVec (↑g : Matrix (Fin n) (Fin n) L) (↑g⁻¹ : Matrix (Fin n) (Fin n) L)
          (psiPath L isVec μ N I)) ≠ 0 →
      DomLe ν (μ N)) ∧
    weightedHomogeneousComponent (torusW isVec) (μ N)
        (actAll isVec (↑g : Matrix (Fin n) (Fin n) L) (↑g⁻¹ : Matrix (Fin n) (Fin n) L)
          (psiPath L isVec μ N I)) =
      C (brk (↑g : Matrix (Fin n) (Fin n) L) (↑g⁻¹ : Matrix (Fin n) (Fin n) L) (μ N) I) *
        psiPath L isVec μ N (canIdx (μ N))
def FactBrk : Prop :=
  ∀ (k : Type) [Field k] (n : ℕ) (μ : Fin n → ℤ), Antitone μ →
    LinearIndependent k (fun I : {I : ℤ → Finset (Fin n) // IsStd μ I} =>
      brk (genMat k n) (genMat k n)⁻¹ μ I.1)
end Formalism.InvariantFactorPaths.GelfandTsetlinBases


