-- Prove2me | Definitions.Def_ZeroFreeRRG_Hardcore_PottsInduction
-- name    : ZeroFreeRRG_Hardcore_PottsInduction
-- status  : Definition
-- author  : @wcysai
-- created : 2026-11-13T09:15:10.976993+00:00
-- url     : https://prove2.me/theorems/a417d3ef-cdb8-41df-aead-e8109b73c150
-- title:
--   Uniform nonvanishing and phase coherence for restricted Potts sums
-- statement:
--   For each fixed vertex set, these predicates express uniform nonvanishing of restricted Potts sums and uniform phase coherence of all one-vertex extensions, over every interaction matrix on the common segment from $1$ to $\beta$.
-- source:
--   Auxiliary definitions for Chen–Wang–Zhang, Zero-Freeness for Random Regular Graphs up to the Replica Symmetry Breaking Threshold, https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/1461.pdf, Lemma 5.7.

import Definitions.Def_ZeroFreeRRG_Hardcore_PottsSegment
import Mathlib
open Set
open Classical
namespace ZeroFreeRRG.Hardcore

/-- Uniform nonvanishing for one set of fixed vertices and all segment-valued weights. -/
noncomputable def pottsNonzeroAt {V : Type} [Fintype V] (q : ℕ) (G : SimpleGraph V)
    (β : ℂ) (S : Finset V) : Prop :=
  ∀ (W : Sym2 V → Fin q → Fin q → ℂ) (hW : ∀ e i j, W e i j = W e j i),
    pottsSegmentWeights q G β W → ∀ τ : V → Fin q, pottsWeightedPartial q G W hW S τ ≠ 0

/-- Uniform phase coherence of all ways to fix one further vertex. -/
noncomputable def pottsCoherentAt {V : Type} [Fintype V] (q : ℕ) (G : SimpleGraph V)
    (β : ℂ) (S : Finset V) : Prop :=
  ∀ (W : Sym2 V → Fin q → Fin q → ℂ) (hW : ∀ e i j, W e i j = W e j i),
    pottsSegmentWeights q G β W → ∀ (τ : V → Fin q) (v : V), v ∉ S →
      ∃ u : ℂ, ‖u‖ = 1 ∧ ∀ c : Fin q,
        ‖u - pottsWeightedPartial q G W hW (insert v S) (Function.update τ v c) /
          (‖pottsWeightedPartial q G W hW (insert v S) (Function.update τ v c)‖ : ℂ)‖ ≤ 1/2

end ZeroFreeRRG.Hardcore


