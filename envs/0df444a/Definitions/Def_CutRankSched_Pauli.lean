-- Prove2me | Definitions.Def_CutRankSched_Pauli
-- name    : CutRankSched_Pauli
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T13:29:26.3348+00:00
-- url     : https://prove2.me/theorems/8dc0f19e-3570-4fa9-9604-3d9d7d0a2ba8
-- title:
--   Binary Pauli vectors $p=(x,z)\in\mathbb F_2^{2m}$
-- statement:
--   A **binary Pauli vector** on $m$ qubits is a pair $p = (x, z)$ with $x, z \in \mathbb F_2^m$, i.e. an element of $\mathbb F_2^{2m}$. It labels the Pauli operator $P(p)$ (up to a fixed Hermitian representative) about which an event rotates.
--
--   **Formalization Note** The two halves are vectors `Fin m → ZMod 2`. The operator $P(p)$ and the rotation $R_\epsilon(P) = \exp(-i\epsilon\pi P/8)$ are not modelled: no statement of the mission refers to them.
-- source:
--   Zhao, Chen, Li, Kong, Peng, Yu and Yue, Cut-Rank Dynamic Programming for Fixed-Event Hardware-Constrained Pauli-Rotation Scheduling, STOC 2027 submission (manuscript sha256 20eb83d2…), Section 3.1, p.4

import Mathlib

set_option autoImplicit false

namespace CutRankSched

/-- A binary Pauli vector on `m` qubits, `p = (x, z) ∈ 𝔽₂^{2m}` (Zhao–Chen–Li–Kong–Peng–Yu–Yue, *Cut-Rank Dynamic Programming for Fixed-Event Hardware-Constrained Pauli-Rotation Scheduling*, STOC 2027 submission manuscript (sha256 20eb83d2…49473878), §3.1, p.4).

**Formalization Note** The pair `(x, z)` is stored as two vectors `Fin m → ZMod 2`; the
Hermitian representative `P(p)` and the rotation `R_ε(P)` of p.4 are not needed by any
statement of the mission and are not modelled. -/
abbrev Pauli (m : ℕ) : Type := (Fin m → ZMod 2) × (Fin m → ZMod 2)

end CutRankSched


