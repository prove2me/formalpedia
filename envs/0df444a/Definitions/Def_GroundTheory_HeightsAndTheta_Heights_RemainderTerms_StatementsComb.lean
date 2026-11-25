-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_StatementsComb
-- name    : GroundTheory_HeightsAndTheta_Heights_RemainderTerms_StatementsComb
-- status  : Definition
-- author  : @community-bot-5
-- created : 2026-11-25T06:16:26.182872+00:00
-- url     : https://prove2.me/theorems/bd76c3fd-bc88-5ab5-af8f-c5edf4926524
-- title:
--   Statements Comb
-- statement:
--   Definitions and structural lemmas for Statements Comb, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/RemainderTerms/StatementsComb.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_AltCoeff
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_Lattice
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_RestTerms_Comb_IsAlt_sum_a5fe0c99cdcf

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
open MvPolynomial Finset Equiv
noncomputable section
namespace Comb
def alternantPsum (m : ℕ) (ρ : List ℕ) : MvPolynomial (Fin m) ℚ :=
  vandermondeOf (fun i : Fin m => (X i : MvPolynomial (Fin m) ℚ)) *
    (ρ.map fun q => psum (Fin m) ℚ q).prod
def IsStandard {m : ℕ} {lam : Fin m → ℕ} (T : youngCells lam ≃ Fin (youngCells lam).card) : Prop :=
  ∀ p q : youngCells lam, p.1.1 ≤ q.1.1 → p.1.2 ≤ q.1.2 → T p ≤ T q
def rowWord {m : ℕ} {lam : Fin m → ℕ} (T : youngCells lam ≃ Fin (youngCells lam).card) :
    Fin (youngCells lam).card → Fin m :=
  fun t => (T.symm t).1.1
def cellOfWord {m n : ℕ} (w : Fin n → Fin m) (t : Fin n) : Fin m × ℕ :=
  (w t, pcnt w t (w t))
end Comb
open Comb
def CombCardYoungCells.Statement : Prop :=
  ∀ (m : ℕ) (lam : Fin m → ℕ), (youngCells lam).card = ∑ i, lam i
def CombYoungRowCard.Statement : Prop :=
  ∀ (m : ℕ) (lam : Fin m → ℕ) (i : Fin m),
    (univ.filter fun p : youngCells lam => p.1.1 = i).card = lam i
def CombTableauRowCount.Statement : Prop :=
  ∀ (m : ℕ) (lam : Fin m → ℕ) (T : youngCells lam ≃ Fin (youngCells lam).card) (t : ℕ)
    (i : Fin m),
    pcnt (rowWord T) t i = (univ.filter fun p : youngCells lam => p.1.1 = i ∧ (T p : ℕ) < t).card
def CombTableauRowPrefix.Statement : Prop :=
  ∀ (m : ℕ) (lam : Fin m → ℕ) (T : youngCells lam ≃ Fin (youngCells lam).card), IsStandard T →
    ∀ t : Fin (youngCells lam).card,
      (univ.filter fun p : youngCells lam =>
        p.1.1 = (T.symm t).1.1 ∧ (T p : ℕ) < (t : ℕ)).card = (T.symm t).1.2
def CombTableauRowLattice.Statement : Prop :=
  ∀ (m : ℕ) (lam : Fin m → ℕ), Antitone lam →
    ∀ (T : youngCells lam ≃ Fin (youngCells lam).card), IsStandard T →
    ∀ (t : ℕ) (i j : Fin m), i ≤ j →
      (univ.filter fun p : youngCells lam => p.1.1 = j ∧ (T p : ℕ) < t).card ≤
        (univ.filter fun p : youngCells lam => p.1.1 = i ∧ (T p : ℕ) < t).card
def CombWordOfTableau.Statement : Prop :=
  ∀ (m : ℕ) (lam : Fin m → ℕ), Antitone lam →
    ∀ (T : youngCells lam ≃ Fin (youngCells lam).card), IsStandard T →
      rowWord T ∈ latticeWords (youngCells lam).card lam ∧
        ∀ t, cellOfWord (rowWord T) t = (T.symm t).1
def CombCellOfWordMem.Statement : Prop :=
  ∀ (m : ℕ) (lam : Fin m → ℕ) (w : Fin (youngCells lam).card → Fin m),
    w ∈ latticeWords (youngCells lam).card lam → ∀ t, cellOfWord w t ∈ youngCells lam
def CombCellOfWordInj.Statement : Prop :=
  ∀ (m n : ℕ) (w : Fin n → Fin m), Function.Injective (cellOfWord w)
def CombCellOfWordMono.Statement : Prop :=
  ∀ (m n : ℕ) (w : Fin n → Fin m), IsLattice w → ∀ s t : Fin n,
    (cellOfWord w s).1 ≤ (cellOfWord w t).1 → (cellOfWord w s).2 ≤ (cellOfWord w t).2 → s ≤ t
def CombTableauOfWord.Statement : Prop :=
  ∀ (m : ℕ) (lam : Fin m → ℕ), Antitone lam →
    ∀ w ∈ latticeWords (youngCells lam).card lam,
      ∃ T : youngCells lam ≃ Fin (youngCells lam).card, IsStandard T ∧ rowWord T = w
def CombTableEqWords.Statement : Prop :=
  ∀ (m : ℕ) (lam : Fin m → ℕ), Antitone lam →
    numStandardTable lam = (latticeWords (∑ i, lam i) lam).card
def CombCfUpdateZero.Statement : Prop :=
  ∀ (m : ℕ) (A : MvPolynomial (Fin m) ℚ), IsAlt A →
    ∀ (lam : Fin m → ℕ), Antitone lam → ∀ i : Fin m, 1 ≤ lam i + stair m i →
      (lam i = 0 ∨ ¬ Antitone (Function.update lam i (lam i - 1))) →
        cf (Function.update (fun j => lam j + stair m j) i (lam i + stair m i - 1)) A = 0
def CombCfAtStair.Statement : Prop :=
  ∀ (m n : ℕ) (lam : Fin m → ℕ), Antitone lam →
    cf (fun i => lam i + stair m i) (alternantPsum m (List.replicate n 1)) =
      (latticeWords n lam).card
def CombCfMonomialPsumOne.Statement : Prop :=
  ∀ (m n : ℕ) (v l : Fin m → ℕ),
    cf l (monomial (ex v) (1 : ℚ) * psum (Fin m) ℚ 1 ^ n) =
      if (∀ i, v i ≤ l i) ∧ ∑ i, l i = ∑ i, v i + n then
        (n.factorial : ℚ) / ∏ i, ((l i - v i).factorial : ℚ)
      else 0
def CombDetDescFactorial.Statement : Prop :=
  ∀ (m : ℕ) (l : Fin m → ℕ),
    (Matrix.of fun i j : Fin m => ((l i).descFactorial (stair m j) : ℚ)).det =
      vandermondeOf (fun i => (l i : ℚ))
def CombCfVandermondePsumOne.Statement : Prop :=
  ∀ (m n : ℕ) (l : Fin m → ℕ), ∑ i, l i = ∑ i, stair m i + n →
    cf l (alternantPsum m (List.replicate n 1)) =
      (n.factorial : ℚ) * vandermondeOf (fun i => (l i : ℚ)) / ∏ i, ((l i).factorial : ℚ)
def CombVandermondeSucc.Statement : Prop :=
  ∀ (n : ℕ) (v : Fin (n + 1) → ℚ),
    vandermondeOf v = (∏ j : Fin n, (v 0 - v j.succ)) * vandermondeOf (fun j : Fin n => v j.succ)
def CombHookShapeFacts.Statement : Prop :=
  ∀ r s l : ℕ, l < s → s ≤ r → Antitone (hookShape r s l) ∧ ∑ i, hookShape r s l i = s
def CombHookBranch.Statement : Prop :=
  ∀ r s l : ℕ, 1 ≤ s → l ≤ s → s + 1 ≤ r → ∀ a : Fin r,
    (if 1 ≤ hookShape r (s + 1) l a then
      (latticeWords s (Function.update (hookShape r (s + 1) l) a
        (hookShape r (s + 1) l a - 1))).card else 0) =
      (if (a : ℕ) = 0 ∧ l < s then (latticeWords s (hookShape r s l)).card else 0) +
        (if (a : ℕ) = l ∧ 1 ≤ l then (latticeWords s (hookShape r s (l - 1))).card else 0)
def CombHookCount.Statement : Prop :=
  ∀ r s l : ℕ, l < s → s ≤ r → (latticeWords s (hookShape r s l)).card = (s - 1).choose l
def CombSortLe.Statement : Prop :=
  ∀ (m : ℕ) (u l : Fin m → ℕ) (σ : Perm (Fin m)), Antitone l → (∀ i, u i ≤ l i) →
    Antitone (u ∘ σ) → ∀ k, u (σ k) ≤ l k
def CombSortShift.Statement : Prop :=
  ∀ (m : ℕ) (lam : Fin m → ℕ), Antitone lam → ∀ (q : ℕ) (i : Fin m), q ≤ lam i + stair m i →
    Function.Injective (Function.update (fun j => lam j + stair m j) i (lam i + stair m i - q)) →
    ∃ (σ : Perm (Fin m)) (μ : Fin m → ℕ), Antitone μ ∧ (∀ k, μ k ≤ lam k) ∧
      ∀ k, Function.update (fun j => lam j + stair m j) i (lam i + stair m i - q) (σ k) =
        μ k + stair m k
def CombSortShiftDistinct.Statement : Prop :=
  ∀ (m : ℕ) (l : Fin m → ℕ), Function.Injective l → ∀ q : ℕ, 1 ≤ q →
    ∀ i j : Fin m, i ≠ j → q ≤ l i → q ≤ l j → ∀ σ τ : Perm (Fin m),
      Function.update l i (l i - q) ∘ σ ≠ Function.update l j (l j - q) ∘ τ
def CombPcntAppend.Statement : Prop :=
  ∀ (m n q : ℕ) (w : Fin n → Fin m) (s : Fin q → Fin m) (t : ℕ) (i : Fin m),
    pcnt (Fin.append w s) t i = pcnt w t i + pcnt s (t - n) i
def CombExtendWord.Statement : Prop :=
  ∀ (m n q : ℕ) (μ lam : Fin m → ℕ), Antitone μ → Antitone lam → (∀ i, μ i ≤ lam i) →
    ∑ i, lam i = ∑ i, μ i + q →
      ∃ s : Fin q → Fin m, ∀ w ∈ latticeWords n μ, Fin.append w s ∈ latticeWords (n + q) lam
def CombStripSum.Statement : Prop :=
  ∀ (m n q : ℕ) (lam : Fin m → ℕ), Antitone lam → 1 ≤ q →
    ∑ i : Fin m, (if q ≤ lam i + stair m i then
      |cf (Function.update (fun j => lam j + stair m j) i (lam i + stair m i - q))
        (alternantPsum m (List.replicate n 1))| else 0) ≤
      ((latticeWords (n + q) lam).card : ℚ)
def CombCfBound.Statement : Prop :=
  ∀ (m : ℕ) (ρ : List ℕ), (∀ q ∈ ρ, 1 ≤ q) → ∀ lam : Fin m → ℕ, Antitone lam →
    |cf (fun i => lam i + stair m i) (alternantPsum m ρ)| ≤ ((latticeWords ρ.sum lam).card : ℚ)
end
end GroundTheory.Heights₂.Heights.RestTerms


