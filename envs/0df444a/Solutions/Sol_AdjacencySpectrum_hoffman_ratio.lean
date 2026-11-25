-- Prove2me | solution 1 for AdjacencySpectrum.hoffman_ratio
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T12:47:39.363213+00:00
-- url     : https://prove2.me/submissions/b76f1c93-2f19-4a34-ae1e-10290140a655

module
public import Mathlib
public import Definitions.Def_SpectralLib_SpectralBounds
public import Definitions.Def_SpectralGraphBounds_Solution
public import Theorems.Thm_SpectralBounds_hoffman_ratio


set_option autoImplicit true
@[expose] public section
public section
open Finset SimpleGraph
open AdjacencySpectrum
variable {V : Type*} [Fintype V] [DecidableEq V] [Nonempty V] (G : SimpleGraph V)
  [DecidableRel G.Adj] (hA : (G.adjMatrix ℝ).IsHermitian)
namespace AdjacencySpectrum
theorem _root_.solution {k : ℕ} (hk : 1 ≤ k) (hreg : G.IsRegularOfDegree k) {s : Finset V}
    (hs : G.IsIndepSet (s : Set V)) :
    (#s : ℝ) ≤ Fintype.card V * (-(⨅ i, hA.eigenvalues i)) / (k - ⨅ i, hA.eigenvalues i) :=
  SpectralBounds.hoffman_ratio G hA hk hreg hs
end AdjacencySpectrum
