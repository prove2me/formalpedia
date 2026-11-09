-- Prove2me | Definitions.Def_CutRankSched_legal
-- name    : CutRankSched_legal
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T13:34:39.185128+00:00
-- url     : https://prove2.me/theorems/87723bf5-e9e9-49f1-bb62-eb48fe443db3
-- title:
--   Legality tests (10) and (5) of Algorithm 1
-- statement:
--   In Algorithm 1, when processing event $i = k+1$ from a state $((U_s)_s, \ell)$, a trial layer $t$ is **legal** if both tests pass:
--
--   1. (10) $U_t \subseteq \ker f_k$, where $f_k$ extracts the coordinate of event $i$ (Algorithm 1, line 10);
--   2. (5) $\ell(j) \ne t$ for all $j \in F^\circ_k$ with $\{j, i\} \in E(X^\circ)$ (line 12).
--
--   The test (5) reads the labels of the old frontier $F^\circ_k$, before any label is forgotten.
-- source:
--   Zhao, Chen, Li, Kong, Peng, Yu and Yue, Cut-Rank Dynamic Programming for Fixed-Event Hardware-Constrained Pauli-Rotation Scheduling, STOC 2027 submission (manuscript sha256 20eb83d2…), Algorithm 1, lines 10–13, p.10; Eq. (10), p.9; Eq. (5), p.8

import Mathlib
import Definitions.Def_CutRankSched_Instance
import Definitions.Def_CutRankSched_State
import Definitions.Def_CutRankSched_frontier
import Definitions.Def_CutRankSched_Residual

set_option autoImplicit false

namespace CutRankSched

/-- The two legality tests of Algorithm 1 for event `i = k + 1` and trial layer `t`
(Zhao–Chen–Li–Kong–Peng–Yu–Yue, *Cut-Rank Dynamic Programming for Fixed-Event Hardware-Constrained Pauli-Rotation Scheduling*, STOC 2027 submission manuscript (sha256 20eb83d2…49473878), Algorithm 1 lines 10–13, p.10; tests (10), p.9, and (5), p.8): `U_t ⊆ ker f_k`, where
`f_k` reads the coordinate of event `i`, and `ℓ(j) ≠ t` for every `j ∈ F°_k` with
`{j, i} ∈ E(X°)`.

**Formalization Note** The event is given 0-based as `i : Fin n` with `k = i.val`; the test reads
the labels on the old frontier `F°_k` before anything is forgotten. -/
def legal (I : Instance) (L : ℕ) (i : Fin I.n) (st : State I L) (t : Fin L) : Prop :=
  (∀ v ∈ st.1 t, v i = 0) ∧ ∀ j ∈ frontier I i.val, Residual I j i → st.2 j ≠ some t

end CutRankSched


