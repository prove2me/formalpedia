-- Prove2me | solution 1 for AdjacencySpectrum.wilf
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T12:47:11.986372+00:00
-- url     : https://prove2.me/submissions/78988a25-c302-425c-a860-cf11c91bd3d8

module
public import Mathlib
public import Definitions.Def_SpectralLib_SpectralBounds
public import Definitions.Def_SpectralGraphBounds_Solution
public import Theorems.Thm_SpectralBounds_wilf


set_option autoImplicit true
@[expose] public section
public section
open Finset SimpleGraph
open AdjacencySpectrum
variable {V : Type*} [Fintype V] [DecidableEq V] [Nonempty V] (G : SimpleGraph V)
  [DecidableRel G.Adj] (hA : (G.adjMatrix ℝ).IsHermitian)
namespace AdjacencySpectrum
theorem _root_.solution : G.Colorable (⌊⨆ i, hA.eigenvalues i⌋₊ + 1) :=
  SpectralBounds.wilf G hA
end AdjacencySpectrum
