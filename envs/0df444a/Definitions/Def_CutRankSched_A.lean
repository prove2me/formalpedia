-- Prove2me | Definitions.Def_CutRankSched_A
-- name    : CutRankSched_A
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T13:31:46.069196+00:00
-- url     : https://prove2.me/theorems/f1e9bd99-20da-485b-be3c-91573c63eb05
-- title:
--   Anticommutation matrix $A_{ij}=\langle p_i,p_j\rangle_s$
-- statement:
--   The **anticommutation matrix** of an instance is the alternating binary $n \times n$ matrix
--   $$
--   A = P^{\mathsf T} J P, \qquad A_{ij} = \langle p_i, p_j \rangle_s \in \mathbb F_2 ,
--   $$
--   where $P = [p_1 \cdots p_n]$. Events $i$ and $j$ anticommute iff $A_{ij} = 1$. The matrix is symmetric with zero diagonal.
-- source:
--   Zhao, Chen, Li, Kong, Peng, Yu and Yue, Cut-Rank Dynamic Programming for Fixed-Event Hardware-Constrained Pauli-Rotation Scheduling, STOC 2027 submission (manuscript sha256 20eb83d2…), Section 3.2, p.4

import Mathlib
import Definitions.Def_CutRankSched_Instance
import Definitions.Def_CutRankSched_symp

set_option autoImplicit false

namespace CutRankSched

/-- The alternating binary anticommutation matrix `A = PᵀJP`, `A_ij = ⟨p_i, p_j⟩_s`
(Zhao–Chen–Li–Kong–Peng–Yu–Yue, *Cut-Rank Dynamic Programming for Fixed-Event Hardware-Constrained Pauli-Rotation Scheduling*, STOC 2027 submission manuscript (sha256 20eb83d2…49473878), §3.2, p.4). -/
def A (I : Instance) : Matrix (Fin I.n) (Fin I.n) (ZMod 2) :=
  fun i j => symp (I.p i) (I.p j)

end CutRankSched


