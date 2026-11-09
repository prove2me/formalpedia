-- Prove2me | Definitions.Def_CutRankSched_State
-- name    : CutRankSched_State
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T13:31:42.266728+00:00
-- url     : https://prove2.me/theorems/8d87eeec-c9a5-4abe-a665-508e59047807
-- title:
--   State of the cut-rank DP
-- statement:
--   A **state** of the cut-rank dynamic program is a pair $((U_s)_{s=1}^L, \ell)$: a family of $L$ subspaces and a labelling $\ell$ of frontier events by layers.
--
--   **Formalization Note** The subspaces live in the zero-padded space $\mathbb F_2^n$; the labelling $\ell : F^\circ_k \to [L]$ is a total map from events to optional layers, empty off its domain.
-- source:
--   Zhao, Chen, Li, Kong, Peng, Yu and Yue, Cut-Rank Dynamic Programming for Fixed-Event Hardware-Constrained Pauli-Rotation Scheduling, STOC 2027 submission (manuscript sha256 20eb83d2…), Section 5.3, p.9

import Mathlib
import Definitions.Def_CutRankSched_Instance

set_option autoImplicit false

namespace CutRankSched

/-- A state of the cut-rank DP (Zhao–Chen–Li–Kong–Peng–Yu–Yue, *Cut-Rank Dynamic Programming for Fixed-Event Hardware-Constrained Pauli-Rotation Scheduling*, STOC 2027 submission manuscript (sha256 20eb83d2…49473878), §5.3, p.9): a family `(U_s)_{s ∈ [L]}` of subspaces and a
partial frontier labelling `ℓ`.

**Formalization Note** Subspaces live in the zero-padded `𝔽₂^n` (see `signature`); the labelling
`ℓ_k : F°_k → [L]` is a total map `Fin n → Option (Fin L)` that is `none` off its domain. -/
abbrev State (I : Instance) (L : ℕ) : Type :=
  (Fin L → Submodule (ZMod 2) (Fin I.n → ZMod 2)) × (Fin I.n → Option (Fin L))

end CutRankSched


