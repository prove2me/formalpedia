-- Prove2me | Definitions.Def_DattaDiscord_IsRankOnePOVM
-- name    : DattaDiscord_IsRankOnePOVM
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T15:21:14.247434+00:00
-- url     : https://prove2.me/theorems/b584c667-31dc-4d88-a6d8-8d1d79ffb888
-- title:
--   Rank-one POVM on $B$
-- statement:
--   Let $B$ be a finite set indexing an orthonormal basis of a finite-dimensional Hilbert space $\mathcal H_B$, so that operators on $\mathcal H_B$ are complex $B\times B$ matrices. A finite family $\{\Pi_i\}_{i=0}^{n-1}$ of such matrices is a **rank-one POVM** if
--
--   1. it is a POVM: every $\Pi_i$ is positive semidefinite and $\sum_{i}\Pi_i = I$;
--   2. every $\Pi_i$ has rank exactly one, i.e. $\Pi_i=|v_i\rangle\langle v_i|$ for a nonzero vector $v_i$.
--
--   Datta's discord is minimized over exactly these measurements ("where $\{\Pi_i\}$ are now, and henceforth in the paper, rank 1 POVMs"). The number of outcomes $n$ is arbitrary.
--
--   **Formalization Note** The POVM condition is the published `QAlgorithms.IsPOVM`; the outcomes are indexed by `Fin n`, and rank is `Matrix.rank` over $\mathbb C$.
-- source:
--   Datta, A Condition for the Nullity of Quantum Discord, arXiv:1003.5256v2, p.1 (after Eq. (2), "where {Πi} are now, and henceforth in the paper, rank 1 POVMs")

import Definitions.Def_QAlgorithms_Defs_Information
import Definitions.Def_QAlgorithms_Defs_Measurement
import Definitions.Def_QAlgorithms_Defs_Ensemble

open scoped ComplexConjugate

namespace DattaDiscord

/-- **Rank-one POVM on `B`**, Datta, *A Condition for the Nullity of Quantum Discord*, arXiv:1003.5256v2, p.1 (after Eq. (2): "where {Πi} are now, and
henceforth in the paper, rank 1 POVMs"). A finite family `Π₀, …, Π_{n-1}` of matrices on the
space indexed by `B` is a rank-one POVM if it is a POVM (each `Πᵢ` positive semidefinite,
`∑ᵢ Πᵢ = I`, the published `QAlgorithms.IsPOVM`) and every `Πᵢ` has rank exactly one.

**Formalization Note** The outcomes are `Fin n` for an arbitrary `n`; the number of outcomes is
not bounded. A positive semidefinite rank-one matrix is `|v⟩⟨v|` for a nonzero vector `v`. -/
def IsRankOnePOVM {B : Type*} [Fintype B] [DecidableEq B] {n : ℕ}
    (M : Fin n → Matrix B B ℂ) : Prop :=
  QAlgorithms.IsPOVM M ∧ ∀ i, (M i).rank = 1

end DattaDiscord


