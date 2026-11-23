-- Prove2me | Definitions.Def_Formalism_PadicSubsetSums_StableGradedCounts_SquareSetMemExceptionalUnion
-- name    : Formalism_PadicSubsetSums_StableGradedCounts_SquareSetMemExceptionalUnion
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T02:19:30.432687+00:00
-- url     : https://prove2.me/theorems/26eefb81-46da-448a-a9ce-3d3fa1af50ac
-- title:
--   Square Set Mem Exceptional Union
-- statement:
--   Definitions and structural lemmas for Square Set Mem Exceptional Union, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PadicSubsetSums/StableGradedCounts/SquareSetMemExceptionalUnion.lean

import Definitions.Def_Formalism_PadicSubsetSums_StableGradedCounts_CrossFactorCount
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset Polynomial
namespace Formalism.IrreducibleCountingLemmas.GaloisIrreducibility
section sets
variable (K L : Type) [Field K] [Fintype K] [Field L] [Algebra K L] [IsAlgClosed L]
open Classical in

noncomputable def e3A (δ l : ℕ) : Finset (Fin δ → K) :=
  (Finset.univ : Finset (Fin δ → K)).filter (fun c => Irreducible (monicOf c) ∧
      ¬ Set.InjOn (primeToPart l) ((monicOf c).rootSet L))
open Classical in

noncomputable def e3I (δ : ℕ) : Finset (Fin δ → K) :=
  (Finset.univ : Finset (Fin δ → K)).filter
      (fun c => Irreducible (monicOf c) ∧ (monicOf c).coeff 0 ≠ 0)
open Classical in

noncomputable def e3C (δ l : ℕ) (P' : K[X]) : Finset (Fin δ → K) :=
  (Finset.univ : Finset (Fin δ → K)).filter (fun c => Irreducible (monicOf c) ∧
      (monicOf c).coeff 0 ≠ 0 ∧ ∃ x ∈ (monicOf c).rootSet L, ∃ y ∈ P'.rootSet L,
        primeToPart l x = primeToPart l y)
def e3D (N : ℕ) (h : K[X]) : Set (Fin N → K) := {c | c ∈ sqSet K N ∧ h ∣ monicOf c}
noncomputable def e3μ (N : ℕ) : (Fin N → K) → ℝ := fun c => sqWeight (monicOf c)
def e3PA (g δ : ℕ) : Finset ℕ :=
  (g ^ δ - 1).primeFactors.filter (fun l => l ^ (4 * padicValNat l (g ^ δ - 1)) ≤ g ^ δ)
def e3PB (g δ δ' : ℕ) : Finset ℕ :=
  ((g ^ δ - 1).primeFactors ∪ (g ^ δ' - 1).primeFactors).filter
    (fun l => l ^ (4 * padicValNat l (g ^ δ - 1)) ≤ g ^ δ)
def e3SA (N : ℕ) : Set (Fin N → K) :=
  ⋃ δ ∈ Finset.Icc 2 N, ⋃ l ∈ e3PA (Fintype.card K) δ, ⋃ c' ∈ e3A K L δ l, e3D K N (monicOf c')
def e3SB (N : ℕ) : Set (Fin N → K) :=
  ⋃ δ ∈ Finset.Icc 1 N, ⋃ δ' ∈ Finset.Icc 1 δ, ⋃ l ∈ e3PB (Fintype.card K) δ δ',
    ⋃ c'' ∈ e3I K δ', ⋃ c' ∈ e3C K L δ l (monicOf c''), e3D K N (monicOf c' * monicOf c'')
variable {K L}
end sets
end Formalism.IrreducibleCountingLemmas.GaloisIrreducibility


