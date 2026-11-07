-- Prove2me | Definitions.Def_CallCountPOPBR_target
-- name    : CallCountPOPBR_target
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T08:06:20.672345+00:00
-- url     : https://prove2.me/theorems/5e96fb22-980a-4cdc-9d08-dc78cda37f9d
-- title:
--   The edge target $T_e=2^{a_z}+2^{a_i}+2^{a_j}$
-- statement:
--   For an edge $e=\{i,j\}$ of a graph on $n$ vertices, the target value is
--   $$
--   T_e=2^{a_z}+2^{a_i}+2^{a_j}.
--   $$
--   It has exactly three set bits, so it is not the sum of two powers of two.
--
--   **Formalization Note** An edge is the pair $(i,j)$ of its endpoints. Vertices of the published `NPGraph.Graph` are $0,\dots,n-1$; vertex $v$ stands for the paper's vertex $v+1$.
-- source:
--   Swain, Recursive Call-Count Sequences: Structural Realisability, Periodic Branching, and Partial-Observation Reconstruction, STOC 2027 submission (manuscript sha256 79135884dd262e4297079b8d2f7adb5deec1b329582779ed16decf34adae2411), Section 2.1, p.5

import Definitions.Def_CallCountPOPBR_vexp
import Definitions.Def_CallCountPOPBR_zexp

set_option autoImplicit false

namespace CallCountPOPBR

/-- **The edge target `T_e = 2^{a_z} + 2^{a_i} + 2^{a_j}`** of the reduction. Swain, *Recursive Call-Count Sequences: Structural Realisability, Periodic Branching, and
Partial-Observation Reconstruction*, STOC 2027 submission (manuscript sha256 79135884…), Section
2.1, p.5: "for an edge e = {i, j}, T_e = 2^{a_z} + 2^{a_i} + 2^{a_j}".

**Formalization Note.** An edge is the pair `(i, j)` of its endpoints (`NPGraph` labels). -/
def target (n : ℕ) (e : ℕ × ℕ) : ℕ := 2 ^ zexp n + 2 ^ vexp n e.1 + 2 ^ vexp n e.2

end CallCountPOPBR


