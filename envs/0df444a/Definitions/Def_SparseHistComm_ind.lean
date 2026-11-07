-- Prove2me | Definitions.Def_SparseHistComm_ind
-- name    : SparseHistComm_ind
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T12:36:48.053241+00:00
-- url     : https://prove2.me/theorems/e2b8ee27-4a17-4631-8e7e-e3ad59f9eb95
-- title:
--   Indicator vector $1_s \in \{0,1\}^d$ of a support
-- statement:
--   For a set $s \subseteq \{1,\dots,d\}$, the **indicator vector** $1_s \in \{0,1\}^d \subset \mathbb R^d$ has $1_s(a) = 1$ if $a \in s$ and $1_s(a) = 0$ otherwise. It turns a support back into the binary vector of Section I, so that histograms and $\ell_1$ distances can be computed.
-- source:
--   Ye–Fan, Optimal Communication for Distributed Sparse Histogram Aggregation, arXiv:2611.04285 (held version, sha256 29df82a4…f27c6f), Section I, p.2 (binary inputs $x_i \in \{0,1\}^d$)

import Mathlib

namespace SparseHistComm

/-- The indicator vector `1_s ∈ {0,1}^d` of a support `s ⊆ [d]` (Ye–Fan, *Optimal Communication for Distributed Sparse Histogram Aggregation*, arXiv:2611.04285 (held version, sha256 29df82a4…f27c6f), Section I, p.2: the binary
input `xᵢ ∈ {0,1}^d` whose support is `s`). -/
noncomputable def ind {d : ℕ} (s : Finset (Fin d)) : Fin d → ℝ :=
  fun a => if a ∈ s then 1 else 0

end SparseHistComm


