-- Prove2me | Definitions.Def_CutRankSched_Instance
-- name    : CutRankSched_Instance
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T13:30:26.356038+00:00
-- url     : https://prove2.me/theorems/3155cb7c-9ef2-46e7-8c08-0c6988816499
-- title:
--   Fixed-event exposure scheduling instance $(H, (p_i, \epsilon_i, T_i)_{i=1}^n)$
-- statement:
--   An **instance** of fixed-event exposure scheduling consists of:
--
--   1. a finite undirected **hardware coupling graph** $H = (Q, E_H)$ with $|Q| = m$ physical qubits;
--   2. a fixed trace of $n$ event occurrences $e_1, \dots, e_n$ in a specified total order;
--   3. for each event $i$: a binary Pauli vector $p_i \in \mathbb F_2^{2m}$, a sign $\epsilon_i \in \{+1, -1\}$ (whether the rotation is $T$- or $T^\dagger$-type), and an **exposure region** $T_i$, a subgraph of $H$.
--
--   Distinct occurrences with the same Pauli label remain distinct events. The exposure regions are fixed input data, not routes chosen during optimization.
--
--   **Formalization Note** Qubits are `Fin m` and events `Fin n`, 0-based (event `i` is the paper's $e_{i+1}$). The sign is a Boolean (`true` for $+1$); it enters no constraint. The conditions $p_i \ne 0$, $\operatorname{supp}(p_i) \subseteq V(T_i)$ and connectedness of $T_i$ are the separate predicate `Instance.Valid`.
-- source:
--   Zhao, Chen, Li, Kong, Peng, Yu and Yue, Cut-Rank Dynamic Programming for Fixed-Event Hardware-Constrained Pauli-Rotation Scheduling, STOC 2027 submission (manuscript sha256 20eb83d2…), Section 3.1, p.4; Problem 3.2, p.5

import Mathlib
import Definitions.Def_CutRankSched_Pauli

set_option autoImplicit false

namespace CutRankSched

/-- An instance of fixed-event exposure scheduling (Zhao–Chen–Li–Kong–Peng–Yu–Yue, *Cut-Rank Dynamic Programming for Fixed-Event Hardware-Constrained Pauli-Rotation Scheduling*, STOC 2027 submission manuscript (sha256 20eb83d2…49473878), §3.1, p.4, and Problem 3.2, p.5):
a finite undirected hardware coupling graph `H` on the qubits `Q = Fin m`, and a fixed trace of
`n` events `e_1, …, e_n` in this order; event `i` carries a binary Pauli vector `p_i`, a sign
`ε_i` and an exposure subgraph `T_i ⊆ H`.

**Formalization Note** Events are 0-based: event `i : Fin n` is the paper's `e_(i+1)`. The sign
`ε_i ∈ {+1, −1}` is a `Bool` (`true` = `+1`); it is input data only and enters no constraint.
The conditions `p_i ≠ 0`, `supp(p_i) ⊆ V(T_i)` and `T_i` connected are `Instance.Valid`. -/
structure Instance where
  /-- number of physical qubits `m = |Q|` -/
  m : ℕ
  /-- number of events `n` -/
  n : ℕ
  /-- the hardware coupling graph `H = (Q, E_H)` -/
  H : SimpleGraph (Fin m)
  /-- the binary Pauli vector `p_i` of event `i` -/
  p : Fin n → Pauli m
  /-- the sign `ε_i` (`true` = `+1`, `false` = `−1`) -/
  sign : Fin n → Bool
  /-- the exposure region `T_i ⊆ H` of event `i` -/
  T : Fin n → H.Subgraph

end CutRankSched


