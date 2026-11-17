-- Prove2me | Definitions.Def_CutRankSched_Supplement_GState
-- name    : CutRankSched_Supplement_GState
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T09:43:45.671049+00:00
-- url     : https://prove2.me/theorems/fee1cd45-d2c2-41f5-8679-55806249bf9a
-- title:
--   States $((V_s)_{s\in[L]},\ell)$ of the global-rank DP
-- statement:
--   For a rank factorization $A=BC$ with inner dimension $r$, a **state** of the global-rank DP is a family $(V_s)_{s\in[L]}$ of subspaces of $\mathbb F_2^r$ together with a partial labelling $\ell$ of the frontier events by layers.
--
--   **Formalization Note** The labelling is a total map from events to optional layers, undefined (`none`) off its domain, as in the base state type.
-- source:
--   Zhao, Chen, Li, Kong, Peng, Yu and Yue, Cut-Rank Dynamic Programming for Fixed-Event Hardware-Constrained Pauli-Rotation Scheduling, STOC 2027 submission (manuscript sha256 20eb83d2…), Section 5.2, Eq. (6), p.8

import Mathlib
import Definitions.Def_CutRankSched_Instance

set_option autoImplicit false

namespace CutRankSched

namespace Supplement

/-- A state of the global-rank DP (Zhao et al., *Cut-Rank Dynamic Programming for Fixed-Event Hardware-Constrained Pauli-Rotation Scheduling*, STOC 2027 submission manuscript (sha256 20eb83d2…49473878), §5.2, Eq. (6), p.8): a family `(V_s)_{s ∈ [L]}` of
subspaces of `𝔽₂^r` and a partial frontier labelling `ℓ`.

**Formalization Note** Layers are 0-based (`Fin L`); `ℓ_k : F°_k → [L]` is a total map
`Fin n → Option (Fin L)`, `none` off its domain, as in the base `CutRankSched.State`. -/
abbrev GState (I : Instance) (r L : ℕ) : Type :=
  (Fin L → Submodule (ZMod 2) (Fin r → ZMod 2)) × (Fin I.n → Option (Fin L))

end Supplement

end CutRankSched


