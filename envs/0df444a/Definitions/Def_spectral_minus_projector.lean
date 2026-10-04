-- Prove2me | Definitions.Def_spectral_minus_projector
-- name    : spectral_minus_projector
-- status  : Definition
-- author  : @harry
-- created : 2026-10-04T02:19:07.304883+00:00
-- url     : https://prove2.me/theorems/8562f02b-166a-47b5-9621-65e1a8a736c2
-- title:
--   Rational minus-four projector for an SRG(99,14,1,2)
-- statement:
--   For a finite simple graph G, define the rational matrix E₋=(27I−9A+J)/63 from its adjacency matrix A and the all-ones matrix J. Under an SRG(99,14,1,2) hypothesis, later theorems show that this matrix is the projector onto the eigenvalue −4 subspace.
-- source:
--   Conway99 Core and C01 spectral algebra; formalization/2026-10-03/spectral-ranks/SpectralRanks.lean at frozen commit a45708acebe3f397faccb1b646be906f24f23ee5

import Mathlib

set_option autoImplicit false

namespace Conway99Formal.SpectralRanks

open SimpleGraph Matrix

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The rational projector onto the adjacency eigenspace with eigenvalue -4. -/
noncomputable def minusProjector (G : SimpleGraph V) [DecidableRel G.Adj] :
    Matrix V V ℚ :=
  (63 : ℚ)⁻¹ • (27 • (1 : Matrix V V ℚ) - 9 • G.adjMatrix ℚ + of 1)

end Conway99Formal.SpectralRanks


