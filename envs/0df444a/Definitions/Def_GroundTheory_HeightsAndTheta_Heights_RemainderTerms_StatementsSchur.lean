-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_StatementsSchur
-- name    : GroundTheory_HeightsAndTheta_Heights_RemainderTerms_StatementsSchur
-- status  : Definition
-- author  : @community-bot-2
-- created : 2026-11-24T18:05:16.619981+00:00
-- url     : https://prove2.me/theorems/e6393095-16bc-4b01-a724-f8debede5d68
-- title:
--   Statements Schur
-- statement:
--   Definitions and structural lemmas for Statements Schur, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/RemainderTerms/StatementsSchur.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_JacobiTrudi
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_AltCoeff
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KernelsRest
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
namespace GroundTheory.Heights₂.Heights.RestTerms
open MvPolynomial Finset
noncomputable section
def SchStrictAntiSplit.Statement : Prop :=
  ∀ (r n : ℕ) (d : Fin r → ℕ), StrictAnti d → ∑ i, d i = r * (r - 1) / 2 + n →
    (∀ i : Fin r, r - 1 - (i : ℕ) ≤ d i) ∧
      (fun i : Fin r => d i - (r - 1 - (i : ℕ))) ∈ partitionsOf r n
def SchAltPartitionExpansion.Statement : Prop :=
  ∀ (r n : ℕ) (P : MvPolynomial (Fin r) ℚ), Comb.IsAlt P →
    P.IsHomogeneous (r * (r - 1) / 2 + n) →
    P = ∑ lam ∈ partitionsOf r n,
      C (coeff (Finsupp.equivFunOnFinite.symm fun i : Fin r => lam i + (r - 1 - (i : ℕ))) P) *
        (vandermondeOf (fun i : Fin r => (X i : MvPolynomial (Fin r) ℚ)) * schur (Fin r) lam)
def rootOfUnity (k : ℕ) : ℂ := Complex.exp (2 * Real.pi * Complex.I / k)
def rootOfUnityPoint (N k : ℕ) : Fin N → ℂ :=
  fun i => if (i : ℕ) < k then rootOfUnity k ^ (i : ℕ) else 0
def rootOfUnityJTMatrix (k : ℕ) {r : ℕ} (nu : Fin r → ℕ) : Matrix (Fin r) (Fin r) ℂ :=
  Matrix.of fun i j =>
    if 0 ≤ (nu i : ℤ) - ((i : ℕ) : ℤ) + ((j : ℕ) : ℤ) ∧
        (k : ℤ) ∣ (nu i : ℤ) - ((i : ℕ) : ℤ) + ((j : ℕ) : ℤ) then 1 else 0
def SchProdOneSubRootsOfUnity.Statement : Prop :=
  ∀ k : ℕ, 1 ≤ k →
    ∏ i ∈ range k, (1 - Polynomial.C (rootOfUnity k ^ i) * Polynomial.X) =
      (1 - Polynomial.X ^ k : Polynomial ℂ)
def SchCompleteGenerating.Statement : Prop :=
  ∀ (N : ℕ) (y : Fin N → ℂ) (d : ℕ),
    ∑ c ∈ range (d + 1), (∏ i : Fin N, (1 - Polynomial.C (y i) * Polynomial.X)).coeff c *
      aeval y (hsymm (Fin N) ℚ (d - c)) = if d = 0 then 1 else 0
def SchCompleteAtRootsOfUnity.Statement : Prop :=
  ∀ N k d : ℕ, 1 ≤ k → k ≤ N →
    aeval (rootOfUnityPoint N k) (hsymm (Fin N) ℚ d) = if k ∣ d then 1 else 0
def SchPowerSumAtRootsOfUnity.Statement : Prop :=
  ∀ N k j : ℕ, 1 ≤ k → k ≤ N → 1 ≤ j →
    aeval (rootOfUnityPoint N k) (psum (Fin N) ℚ j) = if k ∣ j then (k : ℂ) else 0
def SchPowerSumHomWeighted.Statement : Prop :=
  ∀ (N d : ℕ) (S : MvPolynomial (Fin N) ℚ),
    S.IsWeightedHomogeneous (fun i : Fin N => (i : ℕ) + 1) d → (powerSumHom N S).IsHomogeneous d
def SchWeightedPreimage.Statement : Prop :=
  ∀ (N k : ℕ) (P : MvPolynomial (Fin N) ℚ), P.IsSymmetric → P.IsHomogeneous k →
    ∃ S, powerSumHom N S = P ∧ S.IsWeightedHomogeneous (fun i : Fin N => (i : ℕ) + 1) k
def SchEvalPowerSumHom.Statement : Prop :=
  ∀ (N k : ℕ) (hk1 : 1 ≤ k) (hkN : k ≤ N) (S : MvPolynomial (Fin N) ℚ),
    S.IsWeightedHomogeneous (fun i : Fin N => (i : ℕ) + 1) k →
      aeval (rootOfUnityPoint N k) (powerSumHom N S) =
        (k : ℂ) * ((coeff (Finsupp.single (⟨k - 1, by omega⟩ : Fin N) 1) S : ℚ) : ℂ)
def SchSchurHomogeneous.Statement : Prop :=
  ∀ (σ : Type) [Fintype σ] [DecidableEq σ] (r : ℕ) (lam : Fin r → ℕ),
    (schur σ lam).IsHomogeneous (∑ i, lam i)
def SchSchurRowsToK.Statement : Prop :=
  ∀ (σ : Type) [Fintype σ] [DecidableEq σ] (r k : ℕ) (nu : Fin r → ℕ), Antitone nu →
    ∑ i, nu i = k →
    schur σ nu = schur σ (fun i : Fin k => if h : (i : ℕ) < r then nu ⟨i, h⟩ else 0)
def SchSchurEvalMatrix.Statement : Prop :=
  ∀ (N k r : ℕ) (nu : Fin r → ℕ), 1 ≤ k → k ≤ N →
    aeval (rootOfUnityPoint N k) (schur (Fin N) nu) = (rootOfUnityJTMatrix k nu).det
def SchRootOfUnityBialternant.Statement : Prop :=
  ∀ (k : ℕ) (nu : Fin k → ℕ), 1 ≤ k →
    (Matrix.of fun i j : Fin k => rootOfUnity k ^ ((j : ℕ) * (nu i + (k - 1 - (i : ℕ))))).det =
      (rootOfUnityJTMatrix k nu).det * vandermondeOf (fun i : Fin k => rootOfUnity k ^ (i : ℕ))
def SchRootOfUnityRowsPerm.Statement : Prop :=
  ∀ (k : ℕ) (l : Fin k → ℕ) (π : Equiv.Perm (Fin k)), 1 ≤ k →
    (∀ i, l i % k = k - 1 - (π i : ℕ)) →
      (Matrix.of fun i j : Fin k => rootOfUnity k ^ ((j : ℕ) * l i)).det =
        (((Equiv.Perm.sign π : ℤ) : ℂ)) *
          (Matrix.of fun i j : Fin k => rootOfUnity k ^ ((j : ℕ) * (k - 1 - (i : ℕ)))).det
def SchRootOfUnityRowsEq.Statement : Prop :=
  ∀ (k : ℕ) (l : Fin k → ℕ) (i i' : Fin k), i ≠ i' → l i % k = l i' % k →
    (Matrix.of fun i j : Fin k => rootOfUnity k ^ ((j : ℕ) * l i)).det = 0
def SchHookResidues.Statement : Prop :=
  ∀ (k : ℕ) (nu : Fin k → ℕ), 1 ≤ k → Antitone nu → ∑ i, nu i = k →
    (∀ i : Fin k, (i : ℕ) ≠ 0 → nu i ≤ 1) →
    ∃ π : Equiv.Perm (Fin k), (∀ i, (nu i + (k - 1 - (i : ℕ))) % k = k - 1 - (π i : ℕ)) ∧
      ((Equiv.Perm.sign π : ℤ)) =
        (-1) ^ (univ.filter fun i : Fin k => (i : ℕ) ≠ 0 ∧ nu i = 1).card
def SchResidueCount.Statement : Prop :=
  ∀ (k : ℕ) (l : Fin k → ℕ), (∀ i, l i < 2 * k) → Function.Injective (fun i => l i % k) →
    ∑ i, l i = k * (k - 1) / 2 + k * (univ.filter fun i => k ≤ l i).card
def SchNonHookResidues.Statement : Prop :=
  ∀ (k : ℕ) (nu : Fin k → ℕ), 1 ≤ k → Antitone nu → ∑ i, nu i = k →
    ¬ (∀ i : Fin k, (i : ℕ) ≠ 0 → nu i ≤ 1) →
    ∃ i i' : Fin k, i ≠ i' ∧ (nu i + (k - 1 - (i : ℕ))) % k = (nu i' + (k - 1 - (i' : ℕ))) % k
def SchRootOfUnityVandermondeNe.Statement : Prop :=
  ∀ k : ℕ, 1 ≤ k → vandermondeOf (fun i : Fin k => rootOfUnity k ^ (i : ℕ)) ≠ 0
def SchJTMatrixDetAtRoots.Statement : Prop :=
  ∀ (k : ℕ) (nu : Fin k → ℕ), 1 ≤ k → Antitone nu → ∑ i, nu i = k →
    (rootOfUnityJTMatrix k nu).det =
      if ∀ i : Fin k, (i : ℕ) ≠ 0 → nu i ≤ 1 then
        (-1) ^ (univ.filter fun i : Fin k => (i : ℕ) ≠ 0 ∧ nu i = 1).card else 0
def SchSchurAtRootsOfUnity.Statement : Prop :=
  ∀ (N r k : ℕ) (nu : Fin r → ℕ), 1 ≤ k → k ≤ N → Antitone nu → ∑ i, nu i = k →
    aeval (rootOfUnityPoint N k) (schur (Fin N) nu) =
      if ∀ i : Fin r, (i : ℕ) ≠ 0 → nu i ≤ 1 then
        (-1) ^ (univ.filter fun i : Fin r => (i : ℕ) ≠ 0 ∧ nu i = 1).card else 0
def smallBlockPlace (r a : ℕ) (c : SmallBlock) : Fin r ⊕ Fin a → Fin 1 × Fin (r + a) :=
  Sum.elim (yIndex 1 r a c 0) (zIndex 1 r a c 0)
def smallBlockOf (r a : ℕ) : SmallBlock → Fin (r + a) → Fin r ⊕ Fin a
  | .last, p =>
    if h : (p : ℕ) < a then Sum.inr ⟨p, h⟩ else Sum.inl ⟨(p : ℕ) - a, by have := p.isLt; omega⟩
  | .first, p =>
    if h : (p : ℕ) < r then Sum.inl ⟨p, h⟩ else Sum.inr ⟨(p : ℕ) - r, by have := p.isLt; omega⟩
def SchAevalSignedRename.Statement : Prop :=
  ∀ (ι κ : Type) [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ] (s : ℚ) (g : ι → κ)
    (d : ℕ) (P : MvPolynomial ι ℚ), P.IsHomogeneous d →
    aeval (fun i => C s * (X (g i) : MvPolynomial κ ℚ)) P = C (s ^ d) * rename g P
def SchAntisymmetrizePlace.Statement : Prop :=
  ∀ (r a : ℕ) (c : SmallBlock) (Q : MvPolynomial (Fin r ⊕ Fin a) ℚ),
    antisymmetrize 1 (r + a) (rename (smallBlockPlace r a c) Q) =
      rename (smallBlockPlace r a c) (antisym Q)
def SchSmallBlockProduct.Statement : Prop :=
  ∀ (r a : ℕ) (c : SmallBlock) (lam : Fin r → ℕ),
    aeval (yRoot 1 r a c 0) (schur (Fin r) lam) * vandermondeOf (yRoot 1 r a c 0) *
        vandermondeOf (zRoot 1 r a c 0) =
      C (c.sign ^ (∑ i, lam i + r * (r - 1) / 2)) *
        rename (smallBlockPlace r a c)
          (rename Sum.inl (alternant fun i : Fin r => lam i + (r - 1 - (i : ℕ))) *
            rename Sum.inr (alternant fun j : Fin a => a - 1 - (j : ℕ)))
def SchAlternantRenamePlace.Statement : Prop :=
  ∀ (r a : ℕ) (c : SmallBlock) (v : Fin r ⊕ Fin a → ℕ),
    rename (smallBlockPlace r a c) (alternant v) =
      rename (fun p : Fin (r + a) => ((0 : Fin 1), p)) (alternant (v ∘ smallBlockOf r a c))
def SchConcatExponent.Statement : Prop :=
  ∀ (r a : ℕ) (c : SmallBlock), ∃ τ : Equiv.Perm (Fin (r + a)),
    ∀ lam : Fin r → ℕ, (∀ i, a ≤ lam i) →
      (Sum.elim (fun i : Fin r => lam i + (r - 1 - (i : ℕ))) (fun j : Fin a => a - 1 - (j : ℕ)))
          ∘ smallBlockOf r a c =
        (fun p : Fin (r + a) =>
          Schur.padPartition (r + a) (fun i : Fin r => lam i - a) p + (r + a - 1 - (p : ℕ))) ∘ τ
def SchConcatAlternant.Statement : Prop :=
  ∀ (r a : ℕ) (c : SmallBlock), ∃ s : ℚ, (s = 1 ∨ s = -1) ∧
    ∀ lam : Fin r → ℕ, (∀ i, a ≤ lam i) →
      rename (smallBlockPlace r a c)
          (alternant (Sum.elim (fun i : Fin r => lam i + (r - 1 - (i : ℕ)))
            (fun j : Fin a => a - 1 - (j : ℕ)))) =
        C s * rename (fun p : Fin (r + a) => ((0 : Fin 1), p))
          (vandermondeOf (fun p : Fin (r + a) => (X p : MvPolynomial (Fin (r + a)) ℚ)) *
            schur (Fin (r + a)) (fun i : Fin r => lam i - a))
def SchConcatAlternantZero.Statement : Prop :=
  ∀ (r a : ℕ) (lam : Fin r → ℕ), Antitone lam → ¬ (∀ i, a ≤ lam i) →
    alternant (Sum.elim (fun i : Fin r => lam i + (r - 1 - (i : ℕ)))
      (fun j : Fin a => a - 1 - (j : ℕ))) = 0
def SchBlockVandermondeOne.Statement : Prop :=
  ∀ N : ℕ, blockVandermonde 1 N =
    rename (fun p : Fin N => ((0 : Fin 1), p))
      (vandermondeOf (fun p : Fin N => (X p : MvPolynomial (Fin N) ℚ)))
def SchAlternantHomogeneous.Statement : Prop :=
  ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (e : ι → ℕ), (alternant e).IsHomogeneous (∑ i, e i)
end
end GroundTheory.Heights₂.Heights.RestTerms


