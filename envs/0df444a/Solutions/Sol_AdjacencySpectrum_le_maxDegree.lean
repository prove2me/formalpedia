-- Prove2me | solution 1 for AdjacencySpectrum.le_maxDegree
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T12:35:50.501942+00:00
-- url     : https://prove2.me/submissions/cccf019a-534d-40b6-9d48-710565e98293

module
public import Mathlib
public import Definitions.Def_SpectralLib_SpectralBounds
public import Definitions.Def_SpectralGraphBounds_Solution
public import Theorems.Thm_SpectralBounds_le_maxDegree


set_option autoImplicit true
@[expose] public section
public section
open Finset SimpleGraph
open AdjacencySpectrum
variable {V : Type*} [Fintype V] [DecidableEq V] [Nonempty V] (G : SimpleGraph V)
  [DecidableRel G.Adj] (hA : (G.adjMatrix ℝ).IsHermitian)
namespace AdjacencySpectrum
theorem _root_.solution : ⨆ i, hA.eigenvalues i ≤ G.maxDegree :=
  SpectralBounds.le_maxDegree G hA
end AdjacencySpectrum
