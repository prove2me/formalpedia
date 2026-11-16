-- Prove2me | Definitions.Def_WeldedPath_Supplement_pCross
-- name    : WeldedPath_Supplement_pCross
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T01:14:23.654586+00:00
-- url     : https://prove2.me/theorems/5e37670f-8c8f-43ab-867b-660fe13c8d05
-- title:
--   The crossing probability $p_{\mathrm{cross}}$ of Algorithm 3.10
-- statement:
--   For an edge database $C$ let $\hat G(I)$ be the graph of recorded edges, with edge set $\hat E(I)=\{\{\mathrm{tail}(e),\mathrm{head}(f)\}:C_b(e)=f\text{ for some }b\in B_{\mathrm{edge}}\}$. It **contains a crossing** if it has a path from a vertex of column $n-l-1$ to a vertex of column $n+l+1$; $\Pi_{\mathrm{Cross}}$ is the projector onto the database states $|I\rangle$ whose $\hat G(I)$ contains a crossing (it reads only $C$).
--
--   **Algorithm 3.10** initializes the databases to $|\bot\rangle_I$, runs a $q$-query algorithm $A$ with the exact compressed oracle $\widehat{\mathrm{cpWT}}$, and accepts on the outcome $\Pi_{\mathrm{Cross}}$:
--   $$
--   p_{\mathrm{cross}}=\bigl\|\Pi_{\mathrm{Cross}}\,A_q\,\widehat{\mathrm{cpWT}}\,A_{q-1}\cdots\widehat{\mathrm{cpWT}}\,A_0\,|0\rangle_A|\bot\rangle_I\bigr\|^2 .
--   $$
--   Unlike the standard verifier it makes no further queries; it depends on the graph and on $l$, not on a random permutation. Theorem 3.12 bounds the standard success probability by it.
--
--   **Formalization Note** The algorithm is a published `QAlgorithms.QueryAlg`; its unitaries act as the identity on $I$, the oracle on the query registers and $I$, and its input-independent start state stands for $|0\rangle_A$.
-- source:
--   Carolan, Childs, Coudron, Gilani, Miloschewsky, Podder, Algorithmic Wave-Particle Duality: Pathfinding in Welded Trees is Hard, arXiv:2611.05912 (sha256 b31400a0…), Ĝ(I), Π_Cross and Algorithm 3.10, p.23; final state under (40), p.19

import Mathlib
import Definitions.Def_QAlgorithms_Defs_Query
import Definitions.Def_WeldedPath_Supplement_exactCpWT

namespace WeldedPath

namespace Supplement

open QAlgorithms WeldedInstance InjDb

variable {n : ℕ}

/-! ### Running a query algorithm against a database oracle -/

section Run

variable {ι κ W D : Type*} [Fintype ι] [Fintype κ] [Fintype W] [Fintype D]
  [DecidableEq ι] [DecidableEq κ] [DecidableEq W] [DecidableEq D]

/-- An algorithm unitary `U` on the algorithm registers `(ι × κ) × W`, tensored with the identity
on a database register `D`. -/
noncomputable def liftAlgU (U : Matrix ((ι × κ) × W) ((ι × κ) × W) ℂ) :
    Hil (((ι × κ) × W) × D) →L[ℂ] Hil (((ι × κ) × W) × D) :=
  ofBasis fun p => ketTensor (act U (ket p.1)) (ket p.2)

/-- An oracle `O` acting on the query registers and a database register `D`, tensored with the
identity on the workspace `W`. -/
noncomputable def liftOracle (O : Hil ((ι × κ) × D) →L[ℂ] Hil ((ι × κ) × D)) :
    Hil (((ι × κ) × W) × D) →L[ℂ] Hil (((ι × κ) × W) × D) :=
  ofBasis fun p => partImg O (p.1.1, p.2) fun q => ((q.1, p.1.2), q.2)

/-- The state `A_t O A_{t−1} ⋯ O A_0 (|start⟩ ⊗ |d₀⟩)` of the algorithm `A` run with the database
oracle `O` from the database state `|d₀⟩` (arXiv:2611.05912 (sha256 b31400a0…), display under
(40), p.19): the unitaries of `A` act on its registers, `O` on the query registers and the
database. -/
noncomputable def stateAtDb {T : ℕ} (A : QueryAlg ι κ W T)
    (O : Hil ((ι × κ) × D) →L[ℂ] Hil ((ι × κ) × D)) (d₀ : D) :
    Fin (T + 1) → Hil (((ι × κ) × W) × D) :=
  Fin.induction (liftAlgU (A.U 0 : Matrix _ _ ℂ) (ketTensor A.start (ket d₀)))
    (fun i ψ => liftAlgU (A.U i.succ : Matrix _ _ ℂ) (liftOracle O ψ))

/-- The final state `|ψ^{(O)}_{A,q}⟩ = A_q O A_{q−1} ⋯ O A_0 |start⟩ |d₀⟩` (arXiv:2611.05912
(sha256 b31400a0…), p.19). -/
noncomputable def finalStateDb {T : ℕ} (A : QueryAlg ι κ W T)
    (O : Hil ((ι × κ) × D) →L[ℂ] Hil ((ι × κ) × D)) (d₀ : D) : Hil (((ι × κ) × W) × D) :=
  stateAtDb A O d₀ (Fin.last T)

end Run

/-! ### The crossing projector -/

/-- The graph `Ĝ(I)` of recorded edges (arXiv:2611.05912 (sha256 b31400a0…), p.23): the edges
`{tail(e), head(f)}` with `C_b(e) = f` for some `b ∈ B_edge`, on structural indices. -/
noncomputable def recordedGraph (l : ℕ) (G : WeldedInstance n) (C : EdgeDb l G) :
    SimpleGraph ℕ :=
  SimpleGraph.fromRel fun a c =>
    ∃ (b : PClass n l) (j j' : Fin (classSize l G b)), C b j = some j' ∧
      a = ((edgeIdx l G b).symm j).1.tail ∧ c = ((edgeIdx l G b).symm j').1.head n

/-- `Ĝ(I)` contains a crossing: a path from a vertex of `col(n − l − 1)` to a vertex of
`col(n + l + 1)` (arXiv:2611.05912 (sha256 b31400a0…), p.23). Only the edge database is read. -/
def HasCrossing (l : ℕ) (G : WeldedInstance n) (C : EdgeDb l G) : Prop :=
  ∃ a c, IsVertex n a ∧ col n a = n - l - 1 ∧ IsVertex n c ∧ col n c = n + l + 1 ∧
    (recordedGraph l G C).Reachable a c

open Classical in
/-- The projector `Π_Cross` on the database register, tensored with the identity on the algorithm
registers (arXiv:2611.05912 (sha256 b31400a0…), p.23): `|I⟩ ↦ |I⟩` if `Ĝ(I)` contains a crossing,
`0` otherwise. -/
noncomputable def projCross (l : ℕ) (G : WeldedInstance n) (W : Type*) [Fintype W]
    [DecidableEq W] :
    Hil ((QReg n × W) × Db l G) →L[ℂ] Hil ((QReg n × W) × Db l G) :=
  diagProj fun p : (QReg n × W) × Db l G => HasCrossing l G p.2.2

/-- The success probability `p_cross` of Algorithm 3.10 (arXiv:2611.05912 (sha256 b31400a0…),
p.23): initialize `I = (L, C)` to `|⊥⟩_I`, run `A` with `q` queries to `\widehat{cpWT}`, and
measure `{Π_Cross, 1 − Π_Cross}` on `I`; `p_cross = ‖Π_Cross |ψ^{(\widehat{cpWT})}_{A,q}⟩‖²`.

**Formalization Note.** `A` is a published `QAlgorithms.QueryAlg` with query register
`(2n+1)`-bit label × color and `(2n+1)`-bit answer register and workspace `W`; its unitaries act
as the identity on `I`, and `\widehat{cpWT}` acts on the query registers and `I`. The start state
is `A`'s input-independent start state (the source's `|0⟩_A`). `p_cross` depends on the instance
`G` and on `l`, not on `σ`. -/
noncomputable def pCross (l : ℕ) (G : WeldedInstance n) {W : Type*} [Fintype W] [DecidableEq W]
    {q : ℕ} (A : QueryAlg (Qubits (2 * n + 1) × Fin 3) (Qubits (2 * n + 1)) W q) : ℝ :=
  ‖projCross l G W (finalStateDb A (exactCpWT l G) (emptyDb l G))‖ ^ 2

end Supplement

end WeldedPath


