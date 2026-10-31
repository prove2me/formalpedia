-- Prove2me | Definitions.Def_MultiServerAppt_Ss
-- name    : MultiServerAppt_Ss
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T18:56:52.315209+00:00
-- url     : https://prove2.me/theorems/6e89a36e-d607-4fb1-a868-f685a0014ef1
-- title:
--   The transition matrix $S_s$, Eq. (8)
-- statement:
--   The matrix $S_s$ acts on the unsaturated states. On the block of $\xi+1$ clients it is $S^{(\xi+1)}$, and from the block of $\xi+1$ clients to the block of $\xi$ clients, for $\xi\ge 1$, it is the exit block $U^{(\xi+1)}$. Every other block is $0$.
--
--   **Formalization Note** The block of one client has no exit block in the matrix: that exit goes to the empty absorbing state. Indices of equal value are identified by `Fin.cast`, which carries a proof and so cannot give a junk value.
-- source:
--   Kuiper–Lee, Appointment Scheduling for Multiple Servers, SSRN 3975471, Eq. (8), p.12

import Mathlib
import Definitions.Def_MultiServerAppt_Sblock
import Definitions.Def_MultiServerAppt_Ublock
import Definitions.Def_MultiServerAppt_UnsatState

namespace MultiServerAppt

/-- The transition matrix `S_s` of the unsaturated system: `S^(ξ+1)` on the block of `ξ + 1` clients,
and `U^(ξ+1)` from `ξ + 1` clients to `ξ` clients, for `ξ ≥ 1`; every other block is `0`. Kuiper–Lee,
Appointment Scheduling for Multiple Servers, SSRN 3975471, Eq. (8), p.12.

**Formalization Note** The block `j = 1` has no exit block in the matrix: its exit goes to the empty
absorbing state. `Fin.cast` carries a proof, so it only renames `Fin` indices and cannot produce a
junk value at the block boundaries. -/
def Ss {ι : Type*} [Fintype ι] [DecidableEq ι] (S : Matrix ι ι ℝ) (s : ℕ) :
    Matrix (UnsatState ι s) (UnsatState ι s) ℝ :=
  Matrix.of fun p q =>
    if h : (p.1 : ℕ) = q.1 then
      Sblock S (p.1 + 1) p.2 (fun l => q.2 (Fin.cast (by omega) l))
    else if h' : (p.1 : ℕ) = q.1 + 1 then
      Ublock S (q.1 + 1) (fun l => p.2 (Fin.cast (by omega) l)) q.2
    else 0

end MultiServerAppt


