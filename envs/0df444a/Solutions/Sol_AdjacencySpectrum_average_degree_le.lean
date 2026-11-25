-- Prove2me | solution 1 for AdjacencySpectrum.average_degree_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T12:41:26.428798+00:00
-- url     : https://prove2.me/submissions/7bdc8493-faa8-4822-a022-9c80c7c0f52c

module
public import Mathlib
public import Definitions.Def_SpectralLib_SpectralBounds
public import Definitions.Def_SpectralGraphBounds_Solution
public import Theorems.Thm_SpectralBounds_average_degree_le


set_option autoImplicit true
@[expose] public section
public section
open Finset SimpleGraph
open AdjacencySpectrum
variable {V : Type*} [Fintype V] [DecidableEq V] [Nonempty V] (G : SimpleGraph V)
  [DecidableRel G.Adj] (hA : (G.adjMatrix ℝ).IsHermitian)
namespace AdjacencySpectrum
theorem _root_.solution :
    2 * (#G.edgeFinset : ℝ) / Fintype.card V ≤ ⨆ i, hA.eigenvalues i :=
  SpectralBounds.average_degree_le G hA
end AdjacencySpectrum
