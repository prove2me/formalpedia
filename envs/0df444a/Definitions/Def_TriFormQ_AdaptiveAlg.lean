-- Prove2me | Definitions.Def_TriFormQ_AdaptiveAlg
-- name    : TriFormQ_AdaptiveAlg
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T21:44:25.042961+00:00
-- url     : https://prove2.me/theorems/afb3eef5-b707-4b3b-973f-836b7b85bbb9
-- title:
--   Adaptive randomized quantum query algorithm with an $\mathbb F_q$-valued oracle
-- statement:
--   Fix a finite query index set $\iota$, a finite additive group $\kappa$ of oracle answers (here $\kappa=\mathbb F_q$), and an output type $\alpha$. An **adaptive quantum query algorithm** is a finite tree of the following kind. Either it **halts** with an output $a\in\alpha$, or it runs a **round**: a $T$-query quantum algorithm $U_T O U_{T-1}\cdots U_1 O U_0$ on the query register $\iota\times\kappa$ and a workspace of size $w$, starting from a fixed state, followed by a measurement of the whole register in the computational basis; on outcome $z$ it continues with the algorithm $\mathrm{next}(z)$.
--
--   The unitaries, start states and the tree are fixed before the oracle is chosen; the oracle $O$ enters only when the algorithm is run. Classical randomness is the outcome of a round with $0$ queries, and classical control between rounds, including all computation on explicitly given data, is the choice of the next round. This is the model of "a randomized quantum query algorithm" in every statement of the mission.
--
--   **Formalization Note** A copy of the platform's Bool-only `QAlgorithms.AdaptiveQueryAlg` (definition 08848af9) with an oracle valued in any finite additive group. Each round is a platform `QAlgorithms.QueryAlg`.
-- source:
--   Grigorescu–Juba–Wimmer–Xie, Optimal Quantum Query Bounds for Identifying Classes of 3-Tensors, STOC 2027 submission (manuscript sha256 c56b0365…), Theorem 1, p.3 (PDF p.6); §1, p.2 (PDF p.5)

import Definitions.Def_QAlgorithms_Defs_Query

namespace TriFormQ

/-- Grigorescu–Juba–Wimmer–Xie, *Optimal Quantum Query Bounds for Identifying Classes of
3-Tensors*, STOC 2027 submission (manuscript sha256 c56b0365…), Theorem 1, p.3 (PDF p.6): "a
randomized quantum query algorithm" with oracle access to `g : ι → κ` and output type `α`. It
either halts with output `a`, or runs a `T`-query `QAlgorithms.QueryAlg` with workspace `Fin w`
against the standard oracle of `g`, measures its whole register in the computational basis,
and continues with `next z` on outcome `z`.

**Formalization Note.** A copy of the platform's Bool-only `QAlgorithms.AdaptiveQueryAlg`
(definition 08848af9) with an oracle valued in any finite additive group `κ` (here `κ = 𝔽_q`).
The tree is data fixed before the oracle: the oracle enters only through `outProb` and
`maxQueries`. Classical coin flips are measurement outcomes of a 0-query round, and the
classical control between rounds (including all offline computation on explicitly given data)
is the choice of `next`; by deferred measurement this class has the same power as a unitary
algorithm with intermediate measurements, round by round. -/
inductive AdaptiveAlg (ι κ : Type) [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
    (α : Type) : Type where
  | halt (a : α)
  | round (T w : ℕ) (A : QAlgorithms.QueryAlg ι κ (Fin w) T)
      (next : (ι × κ) × Fin w → AdaptiveAlg ι κ α)

end TriFormQ


