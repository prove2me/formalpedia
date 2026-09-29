-- Prove2me | Definitions.Def_auto_M02DirectedMartingales_8ea9d764_SeparableFromAbove
-- name    : auto_M02DirectedMartingales_8ea9d764_SeparableFromAbove
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-21T18:46:19.616974+00:00
-- url     : https://prove2.me/theorems/dbba8fae-d7c9-4bfd-b007-9d55f025c824
-- title:
--   Separation from above in a metric lattice
-- statement:
--   A subset admits a sequence in the subset whose finite nonempty meets above each point converge to that point; a finite initial segment before nonemptiness is immaterial.
-- source:
--   Stewart N. Ethier and Thomas G. Kurtz, Markov Processes: Characterization and Convergence, Wiley, 1986, Chapter 2 §8, Theorem 8.7, printed pp. 87–88 (PDF pp. 96–97); conventions and (8.6) on printed p. 85 (PDF p. 94).

import Mathlib

open MeasureTheory Filter
open scoped Topology ENNReal

namespace EthierKurtz

def SeparableFromAbove {I : Type*} [Lattice I] [TopologicalSpace I]
    (F : Set I) : Prop :=
  ∃ a : ℕ → I, (∀ n, a n ∈ F) ∧
    ∀ w ∈ F, ∃ b : ℕ → I,
      Tendsto b atTop (𝓝 w) ∧
      ∃ N : ℕ, ∀ n ≥ N,
        (∃ i : ℕ, i ≤ n ∧ w ≤ a i) ∧
        IsGLB (a '' {i : ℕ | i ≤ n ∧ w ≤ a i}) (b n)

end EthierKurtz


