-- Prove2me | solution 1 for AdjacencySpectrum.hoffman_chromatic
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T12:46:44.40337+00:00
-- url     : https://prove2.me/submissions/98fb9566-b6a6-40fe-aef9-acf6d2f92951

module
public import Mathlib
public import Definitions.Def_SpectralLib_SpectralBounds
public import Definitions.Def_SpectralGraphBounds_Solution
public import Theorems.Thm_SpectralBounds_hoffman_chromatic


set_option autoImplicit true
@[expose] public section
public section
open Finset SimpleGraph
open AdjacencySpectrum
variable {V : Type*} [Fintype V] [DecidableEq V] [Nonempty V] (G : SimpleGraph V)
  [DecidableRel G.Adj] (hA : (G.adjMatrix ℝ).IsHermitian)
namespace AdjacencySpectrum
theorem _root_.solution (hE : G.edgeSet.Nonempty) {c : ℕ} (hc : G.Colorable c) :
    1 - (⨆ i, hA.eigenvalues i) / (⨅ i, hA.eigenvalues i) ≤ c :=
  SpectralBounds.hoffman_chromatic G hA hE hc
end AdjacencySpectrum
