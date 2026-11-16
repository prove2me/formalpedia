-- Prove2me | Definitions.Def_TFNPRom_Supplement_ueoplSol
-- name    : TFNPRom_Supplement_ueoplSol
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T04:25:45.705225+00:00
-- url     : https://prove2.me/theorems/e390c910-1235-4793-869c-5ff0b3f477e7
-- title:
--   Solutions of $\mathrm{UEoPL}_N$
-- statement:
--   Let $N\ge 2$ and fix a UEoPL instance with activity as above. A node $u$ is a **proper sink** if it is inactive but some active node has $u$ as its successor. A node $(i,j)$ is a **proper source** if it is active, $i<N$, and no active node has $(i,j)$ as its successor. The solutions of the instance are
--
--   1. $(1,1)$, if $(1,1)$ is inactive (inactive distinguished source);
--   2. $(N,j)$, if $(N,j)$ is active (active sink);
--   3. $(i,j)$, if $(i,j)$ is a proper sink;
--   4. $(i,j)$, if $(i,j)\neq(1,1)$ and $(i,j)$ is a proper source;
--   5. the pair $(i,j)$ and $(i,j')$, if $j\neq j'$ and both nodes are active (two parallel lines).
--
--   $\mathrm{UEoPL}_N$ is the relation of instances and their solutions. Every instance has a solution, so UEoPL is a TFNP problem; it is the problem solved in Theorem 15.
--
--   **Formalization Note** A candidate solution is a single node or an ordered pair of nodes; both orders of a parallel pair are solutions. The distinguished node $(1,1)$ is index $(0,0)$.
-- source:
--   Fleming, Göös, Guan, Korten, Mitropolsky, Pitassi, Riazanov, Sokolov, Yang, Yuan, TFNP in the Random Oracle Model, arXiv:2611.05308 (held version, sha256 e11eb9c3…9bb), Definition 3, pp.19–20; App. A, p.42

import Mathlib
import Definitions.Def_TFNPRom_Supplement_ueoplActive
import Definitions.Def_TFNPRom_Supplement_ueoplIsSucc

namespace TFNPRom.Supplement

/-- The solutions of `UEoPL_N` (Fleming et al., *TFNP in the Random Oracle Model*, arXiv:2611.05308 (held version, sha256 e11eb9c3…9bb), Definition 3, pp.19–20; App. A, p.42). With activity as in
`ueoplActive`, a proper sink is an inactive node that is the successor of some active node, and a
proper source is an active node `(i, j)` with `i < N` that is the successor of no active node. The
solutions of an instance are
1. `(1, 1)`, if `(1, 1)` is inactive (inactive distinguished source);
2. `(N, j)`, if `(N, j)` is active (active sink);
3. `(i, j)`, if `(i, j)` is a proper sink;
4. `(i, j)`, if `(i, j) ≠ (1, 1)` and `(i, j)` is a proper source;
5. `(i, j)` and `(i, j′)`, if `j ≠ j′` and both nodes are active (two parallel lines).

**Formalization Note** A candidate solution is a single node (`Sum.inl`) or a pair of nodes
(`Sum.inr`); the pair is ordered, and both orders of a parallel pair are solutions. 0-based `Fin N`:
the distinguished node `(1, 1)` is `(0, 0)` and row `N` is index `N − 1`. -/
def ueoplSol (N : ℕ) (succ pred : Fin N → Fin N → Option (Fin N)) :
    (Fin N × Fin N) ⊕ ((Fin N × Fin N) × (Fin N × Fin N)) → Prop
  | .inl v =>
      (v.1.val = 0 ∧ v.2.val = 0 ∧ ¬ ueoplActive N succ pred v) ∨
      (v.1.val + 1 = N ∧ ueoplActive N succ pred v) ∨
      (¬ ueoplActive N succ pred v ∧ ∃ w, ueoplActive N succ pred w ∧ ueoplIsSucc N succ w v) ∨
      (¬ (v.1.val = 0 ∧ v.2.val = 0) ∧ ueoplActive N succ pred v ∧ v.1.val + 1 < N ∧
        ¬ ∃ w, ueoplActive N succ pred w ∧ ueoplIsSucc N succ w v)
  | .inr (v, w) =>
      v.1 = w.1 ∧ v.2 ≠ w.2 ∧ ueoplActive N succ pred v ∧ ueoplActive N succ pred w

end TFNPRom.Supplement


