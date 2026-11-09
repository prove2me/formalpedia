-- Prove2me | Definitions.Def_OracleStateHSP_QueryAlgorithm
-- name    : OracleStateHSP_QueryAlgorithm
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T11:30:19.84862+00:00
-- url     : https://prove2.me/theorems/efb820bd-7069-4c47-bbb3-d1b20f0bec10
-- title:
--   $T$-query algorithm $A^O = U_T \tilde O_T U_{T-1} \cdots U_1 \tilde O_1 U_0$
-- statement:
--   A **$T$-query algorithm** on $\mathcal H = S \oplus (\mathcal H_S \otimes W)$ consists of unitaries $U_0, \dots, U_T$ on $\mathcal H$, independent of the oracle, and the kind of each of its $T$ queries, fixed in advance. On an oracle $O$ it applies
--   $$
--   A^O = U_T \tilde O_T U_{T-1} \cdots U_1 \tilde O_1 U_0 ,
--   $$
--   where $\tilde O_i$ is the query operator of the $i$-th kind. The algorithm belongs to the model of **Definition 4.1** when every query is a forward or an inverse query. The state after $U_t$ and the final state $A^O|\psi_0\rangle$ from an initial vector $|\psi_0\rangle$ are defined accordingly.
--
--   By deferred measurement this model captures adaptive algorithms (Remark 4.2), and the direct sum gives controlled queries.
--
--   **Formalization Note** The query register has a finite basis $Q$; $S$ and $W$ are finite types. Oracle-independent fixed gates (for instance the controlled representation $U_R$) are among the $U_i$.
-- source:
--   Liu–Carrasco–Eisert–Bellante, The power of oracle access, arXiv:2609.35656, Definition 4.1, eq. (49), p.35; Theorem 4.10, p.40

import Mathlib
import Definitions.Def_QAlgorithms_Defs_Query
import Definitions.Def_OracleStateHSP_queryOp

namespace OracleStateHSP

open QAlgorithms

/-- A `T`-query algorithm in the model of Liu–Carrasco–Eisert–Bellante, *The power of oracle access*, arXiv:2609.35656, Definition 4.1, p.35 (eq. (49)),
extended by the conjugate and transpose queries of Theorem 4.10 (p.40): unitaries
`U_0, …, U_T` on `H = S ⊕ (H_S ⊗ W)`, independent of the oracle, and the kind of each of the `T`
queries, "fixed in advance". On oracle `O` the algorithm applies
`A^O = U_T Õ_T U_{T−1} ⋯ U_1 Õ_1 U_0`.

**Formalization Note.** The query register `H_S` has basis `Q`; the spaces `S` and `W` are finite
types chosen by the algorithm. Controlled queries are modelled by the direct sum, as in the paper
(p.35). The paper's Definition 4.1 proper is the class `IsDef41` of algorithms whose queries are all
forward or inverse. Oracle-independent fixed gates (such as the controlled representation `U_R` of
p.6) are among the unitaries `U_i`. -/
structure QueryAlgorithm (Q S W : Type*) [Fintype Q] [Fintype S] [Fintype W] [DecidableEq Q]
    [DecidableEq S] [DecidableEq W] (T : ℕ) where
  /-- The oracle-independent unitaries `U_0, …, U_T`. -/
  U : Fin (T + 1) → Matrix.unitaryGroup (S ⊕ (Q × W)) ℂ
  /-- The kind of the `i`-th query (`i = 0, …, T−1`), fixed in advance. -/
  kind : Fin T → QueryKind

namespace QueryAlgorithm

variable {Q S W : Type*} [Fintype Q] [Fintype S] [Fintype W] [DecidableEq Q] [DecidableEq S]
  [DecidableEq W] {T : ℕ}

/-- The algorithm belongs to the model of Definition 4.1 (arXiv:2609.35656, p.35): every query is
a forward or an inverse query (no conjugate or transpose queries). -/
def IsDef41 (A : QueryAlgorithm Q S W T) : Prop :=
  ∀ i, (A.kind i).IsForwardOrInverse

/-- The state `U_t Õ_t ⋯ U_1 Õ_1 U_0 |ψ₀⟩` after `U_t` has been applied, for the oracle `O` and the
initial state `ψ₀` (arXiv:2609.35656, eq. (49), p.35). -/
noncomputable def stateAt (A : QueryAlgorithm Q S W T) (O : Matrix Q Q ℂ)
    (ψ₀ : EuclideanSpace ℂ (S ⊕ (Q × W))) : Fin (T + 1) → EuclideanSpace ℂ (S ⊕ (Q × W)) :=
  Fin.induction (act (A.U 0 : Matrix _ _ ℂ) ψ₀)
    (fun i ψ => act (A.U i.succ : Matrix _ _ ℂ) (act (queryOp (A.kind i) O) ψ))

/-- The final state `A^O |ψ₀⟩ = U_T Õ_T ⋯ Õ_1 U_0 |ψ₀⟩` (arXiv:2609.35656, eq. (49), p.35). -/
noncomputable def finalState (A : QueryAlgorithm Q S W T) (O : Matrix Q Q ℂ)
    (ψ₀ : EuclideanSpace ℂ (S ⊕ (Q × W))) : EuclideanSpace ℂ (S ⊕ (Q × W)) :=
  A.stateAt O ψ₀ (Fin.last T)

end QueryAlgorithm

end OracleStateHSP


