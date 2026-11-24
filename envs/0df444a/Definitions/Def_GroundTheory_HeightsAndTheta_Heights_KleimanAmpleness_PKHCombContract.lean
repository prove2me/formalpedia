-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PKHCombContract
-- name    : GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PKHCombContract
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T05:06:35.015892+00:00
-- url     : https://prove2.me/theorems/9782fe29-b9e5-4d52-b17e-c764c2e3b5c5
-- title:
--   PKHComb Contract
-- statement:
--   Definitions and structural lemmas for PKHComb Contract, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PKHCombContract.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_KHCombContractSt
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
namespace GroundTheory.Heights₂.Heights.Kleiman
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry KHFree
noncomputable section
namespace KHCombContract
set_option linter.unusedSectionVars false
variable {K : Type} [Fintype K] [LinearOrder K] {ι : K → Type} [∀ k, Fintype (ι k)] [∀ k, LinearOrder (ι k)]
def ins (k : K) (i₀ : ι k) (T : ∀ k, Finset (ι k)) : ∀ k, Finset (ι k) :=
  Function.update T k (insert i₀ (T k))
def rem (T : ∀ k, Finset (ι k)) (l : K) (i : ι l) : ∀ k, Finset (ι k) :=
  Function.update T l ((T l).erase i)
theorem sum_card_update_of_mem (T : ∀ k, Finset (ι k)) (l : K) (A : Finset (ι l)) (s : Finset K) (hl : l ∈ s) :
    (∑ x ∈ s, ((Function.update T l A x).card - 1)) + ((T l).card - 1) =
      (∑ x ∈ s, ((T x).card - 1)) + (A.card - 1) := by
  rw [← Finset.add_sum_erase s _ hl, ← Finset.add_sum_erase s (fun x => (T x).card - 1) hl, Function.update_self]
  have : ∑ x ∈ s.erase l, ((Function.update T l A x).card - 1) = ∑ x ∈ s.erase l, ((T x).card - 1) :=
    Finset.sum_congr rfl fun x hx => by rw [Function.update_of_ne (Finset.ne_of_mem_erase hx)]
  rw [this]; ring
section Total
variable {S : Type} [CommRing S]
def tD (F : (∀ k, Finset (ι k)) → S) (T : ∀ k, Finset (ι k)) : S :=
  ∑ p ∈ Finset.univ.sigma T, KH.faceSign T p.1 p.2 • F (rem T p.1 p.2)
def tH (k : K) (i₀ : ι k) (F : (∀ k, Finset (ι k)) → S) (T : ∀ k, Finset (ι k)) : S :=
  if i₀ ∈ T k then 0 else KH.faceSign (ins k i₀ T) k i₀ • F (ins k i₀ T)
end Total
section Complex
variable {S : Type} [CommRing S]
open Classical in

def ext (J : ∀ k, Finset (ι k)) (n : ℕ) (φ : CombC S J n) (T : ∀ k, Finset (ι k)) : S :=
  if h : ((∀ l, (T l).Nonempty) ∧ ∑ l, ((T l).card - 1) = n) ∧ ∀ l, J l ⊆ T l then φ ⟨⟨T, h.1⟩, h.2⟩ else 0
def hh (J : ∀ k, Finset (ι k)) (k : K) (i₀ : ι k) (m : ℕ) (φ : CombC S J (m + 1)) : CombC S J m :=
  fun I => tH k i₀ (ext J (m + 1) φ) I.1.1
def corr (J : ∀ k, Finset (ι k)) (k : K) (i₀ : ι k) (d : ℕ) (φ : CombC S J d) (T : ∀ k, Finset (ι k)) : S :=
  if T k = ∅ then tH k i₀ (ext J d φ) T else 0
end Complex
section Final
variable {S : Type} [CommRing S]
def repl (J : ∀ k, Finset (ι k)) (k : K) (i₀ : ι k) (d : ℕ) (I : CombCell ι J d) (hJk : J k = ∅)
    (h1 : (I.1.1 k).card = 1) : CombCell ι J d :=
  ⟨⟨Function.update I.1.1 k {i₀}, fun l => by
      by_cases hl : l = k
      · subst hl; rw [Function.update_self]; exact Finset.singleton_nonempty _
      · rw [Function.update_of_ne hl]; exact I.1.2.1 l,
    by
      have h := sum_card_update_of_mem I.1.1 k {i₀} Finset.univ (Finset.mem_univ _)
      rw [Finset.card_singleton, h1, I.1.2.2] at h
      omega⟩, fun l => by
    show J l ⊆ Function.update I.1.1 k {i₀} l
    by_cases hl : l = k
    · subst hl; rw [hJk]; exact Finset.empty_subset _
    · rw [Function.update_of_ne hl]; exact I.2 l⟩
end Final
end KHCombContract
end
end GroundTheory.Heights₂.Heights.Kleiman


