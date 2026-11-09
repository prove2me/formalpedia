-- Prove2me | Definitions.Def_WeldedPath_successProb
-- name    : WeldedPath_successProb
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T06:21:43.197596+00:00
-- url     : https://prove2.me/theorems/49ecdf58-6086-4618-9c44-5b6fd7706304
-- title:
--   Success probability of outputting an entrance–exit path
-- statement:
--   A $q$-query algorithm $A$ applies oracle-independent unitaries $A_0,\dots,A_q$ interleaved with $q$ calls to $O^{(wt)}_\sigma$ and measures in the computational basis. Its output is read as a list $(\alpha_1,z_1),\dots,(\alpha_m,z_m)$, with $z_0=0$ the entrance label. The output is an **entrance–exit walk** for $\sigma$ when $m\ge 1$, every $z_i$ encodes a label in $[0,M]$,
--   $$
--   F^{(wt)}_\sigma(z_{i-1},\alpha_i)=z_i\neq z_{i-1}\quad(i=1,\dots,m),
--   $$
--   and $z_m=\sigma_{\mathrm{label}}(r(T_2))$ is the exit's label. The **success probability** is
--   $$
--   \Pr[A \text{ outputs a path from entrance to exit}]=\mathbb E_{\sigma\sim D_{\mathrm{sing}}}\Pr_{\text{measurement}}[\text{the output is an entrance–exit walk for }\sigma].
--   $$
--   A more general version averages the probability of any $\sigma$-indexed event over any finite set of $\sigma$.
--
--   **Formalization Note** The algorithm is the published `QAlgorithms.QueryAlg` with query register (label bits, color) and answer register (label bits), any finite workspace, and an output map on measurement outcomes. Walks need not have distinct labels; every path from the entrance to the exit is a walk.
-- source:
--   Carolan, Childs, Coudron, Gilani, Miloschewsky, Podder, Algorithmic Wave-Particle Duality: Pathfinding in Welded Trees is Hard, arXiv:2611.05912 (sha256 b31400a0…), p.8 (query model), p.17 (27), p.22 (candidate paths), Algorithm 3.9 p.23, Theorem 4.1 p.26

import Mathlib
import Definitions.Def_QAlgorithms_Defs_Query
import Definitions.Def_WeldedPath_singSupport

namespace WeldedPath

namespace WeldedInstance

variable {n : ℕ}

/-- The output steps `(α_1, z_1), …, (α_m, z_m)` starting at label `z` follow edges of the graph
and end at the exit label (arXiv:2611.05912 (sha256 b31400a0…), p.22 and Algorithm 3.9, step 3,
p.23): each `z_i` encodes a label in `[0, M]`, `F^{(wt)}_σ(z_{i−1}, α_i) = z_i ≠ z_{i−1}`, and the
last label is `σ_label(r(T_2))`. -/
def WalkFrom (l : ℕ) (G : WeldedInstance n) (σ : Equiv.Perm (Label n) × Equiv.Perm G.edges) :
    Label n → List (Fin 3 × QAlgorithms.Qubits (2 * n + 1)) → Prop
  | z, [] => z = σ.1 (exitLabelIdx n)
  | z, (α, b) :: L =>
      ∃ h : QAlgorithms.bitsToNat b < labelBound n + 1,
        G.F l σ z α = ⟨_, h⟩ ∧ (⟨_, h⟩ : Label n) ≠ z ∧ G.WalkFrom l σ ⟨_, h⟩ L

/-- The output `(z_0 = 0, α_1, z_1, …, α_m, z_m)`, `m ≥ 1`, is a walk from the entrance to the
exit in the graph `σ` (arXiv:2611.05912 (sha256 b31400a0…), p.22, Theorem 4.1, p.26).

**Formalization Note.** The output list holds the steps `(α_i, z_i)`; `z_0 = 0` is implicit
(`σ_label(0) = 0` is the entrance label). The labels need not be pairwise distinct: a walk is
accepted, a generalization of the source's path (loops can be removed without queries, p.22). -/
def IsEntranceExitWalk (l : ℕ) (G : WeldedInstance n)
    (σ : Equiv.Perm (Label n) × Equiv.Perm G.edges)
    (L : List (Fin 3 × QAlgorithms.Qubits (2 * n + 1))) : Prop :=
  L ≠ [] ∧ G.WalkFrom l σ 0 L

open Classical in
/-- The probability, over `σ` uniform on the finite set `S` and the final computational-basis
measurement, that the `q`-query algorithm `A` with output map `out` and oracle
`O^{(wt)}_σ = xorOracle (oracleFn σ)` produces an outcome satisfying `acc σ`
(arXiv:2611.05912 (sha256 b31400a0…), §2 p.8 and (27), p.17). -/
noncomputable def probOver (l : ℕ) (G : WeldedInstance n)
    (S : Finset (Equiv.Perm (Label n) × Equiv.Perm G.edges))
    {W : Type*} [Fintype W] [DecidableEq W] {q : ℕ}
    (A : QAlgorithms.QueryAlg (QAlgorithms.Qubits (2 * n + 1) × Fin 3)
      (QAlgorithms.Qubits (2 * n + 1)) W q)
    (acc : Equiv.Perm (Label n) × Equiv.Perm G.edges →
      ((QAlgorithms.Qubits (2 * n + 1) × Fin 3) × QAlgorithms.Qubits (2 * n + 1)) × W → Prop) :
    ℝ :=
  avgOver S fun σ =>
    QAlgorithms.probEvent (A.finalState (QAlgorithms.xorOracle (G.oracleFn l σ))) (acc σ)

/-- `Pr[A outputs a path from entrance to exit]` for `σ ∼ D_sing` (Theorem 4.1, arXiv:2611.05912
(sha256 b31400a0…), p.26): the measured outcome `z` is mapped to the output list `out z`, which
succeeds when it is an entrance–exit walk in `σ`. -/
noncomputable def successProb (l : ℕ) (G : WeldedInstance n)
    {W : Type*} [Fintype W] [DecidableEq W] {q : ℕ}
    (A : QAlgorithms.QueryAlg (QAlgorithms.Qubits (2 * n + 1) × Fin 3)
      (QAlgorithms.Qubits (2 * n + 1)) W q)
    (out : ((QAlgorithms.Qubits (2 * n + 1) × Fin 3) × QAlgorithms.Qubits (2 * n + 1)) × W →
      List (Fin 3 × QAlgorithms.Qubits (2 * n + 1))) : ℝ :=
  G.probOver l (G.singSupport l) A fun σ z => G.IsEntranceExitWalk l σ (out z)

end WeldedInstance

end WeldedPath


