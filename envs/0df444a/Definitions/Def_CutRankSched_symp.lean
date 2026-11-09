-- Prove2me | Definitions.Def_CutRankSched_symp
-- name    : CutRankSched_symp
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T13:30:38.534205+00:00
-- url     : https://prove2.me/theorems/88933ea5-9010-4896-af15-62ec5b5b5ad5
-- title:
--   Symplectic product $\langle p, p'\rangle_s$
-- statement:
--   The **symplectic product** of two binary Pauli vectors $p = (x, z)$ and $p' = (x', z')$ is
--   $$
--   \langle (x, z), (x', z') \rangle_s = x \cdot z' + z \cdot x' \pmod 2 .
--   $$
--   The Pauli operators $P(p)$ and $P(p')$ anticommute if and only if $\langle p, p'\rangle_s = 1$.
-- source:
--   Zhao, Chen, Li, Kong, Peng, Yu and Yue, Cut-Rank Dynamic Programming for Fixed-Event Hardware-Constrained Pauli-Rotation Scheduling, STOC 2027 submission (manuscript sha256 20eb83d2…), Section 3.1, p.4

import Mathlib
import Definitions.Def_CutRankSched_Pauli

set_option autoImplicit false

namespace CutRankSched

/-- The symplectic product `⟨(x, z), (x', z')⟩_s = x · z' + z · x' (mod 2)`
(Zhao–Chen–Li–Kong–Peng–Yu–Yue, *Cut-Rank Dynamic Programming for Fixed-Event Hardware-Constrained Pauli-Rotation Scheduling*, STOC 2027 submission manuscript (sha256 20eb83d2…49473878), §3.1, p.4). Two Pauli operators anticommute iff it is `1`. -/
def symp {m : ℕ} (p p' : Pauli m) : ZMod 2 :=
  dotProduct p.1 p'.2 + dotProduct p.2 p'.1

end CutRankSched


