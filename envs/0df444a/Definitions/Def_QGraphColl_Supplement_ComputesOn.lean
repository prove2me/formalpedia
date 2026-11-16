-- Prove2me | Definitions.Def_QGraphColl_Supplement_ComputesOn
-- name    : QGraphColl_Supplement_ComputesOn
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T03:31:52.230216+00:00
-- url     : https://prove2.me/theorems/930c2e37-79e4-4895-b6de-8d02111301f7
-- title:
--   Bounded-error computation of a partial function with a $q$-ary standard oracle
-- statement:
--   Let $\kappa$ be a finite alphabet carrying an additive group structure (for an alphabet of size $q$, the integers mod $q$), let $D\subseteq\kappa^n$ and $f:D\to\{0,1\}$. For an input $x\in\kappa^n$ the **standard oracle** is
--   $$O_x:\ |i,c\rangle\ \longmapsto\ |i,\,c+x_i\rangle\qquad(i\in[n],\ c\in\kappa),$$
--   so one query reads one alphabet symbol. A $T$-query algorithm $A$ (the published query model: input-independent start state and unitaries $U_0,\dots,U_T$ interleaved with $T$ applications of $O_x\otimes I$, followed by a measurement in the computational basis and a classical output map) **computes $f$ on $D$ with error at most $\varepsilon$** when for every $x\in D$
--   $$\Pr[A^{O_x}\text{ outputs }f(x)]\ \ge\ 1-\varepsilon.$$
--   With $\varepsilon=1/3$ this is the notion behind $Q_2(f)$, the quantum query complexity with error at most $1/3$ on every input of the domain.
--
--   This extends the published binary notion `QAlgorithms.QueryAlg.ComputesWithError` from the alphabet $\{0,1\}$ to arbitrary finite alphabets; for $\kappa=\{0,1\}$ the two coincide.
--
--   **Formalization Note** The input is not binary-encoded; a binary encoding would change the query count by a factor $\log q$.
-- source:
--   Cornelissen, Gilani, Kintali, Le Gall, Patro, Zhou, Breaking the quantum barriers for Graph Collision, arXiv:2611.05356 (version of October 2026, sha256 21da7ff0…), §5, p.31 (Q2(f) with error at most 1/3); §2, p.12 (error on every input)

import Mathlib
import Definitions.Def_QAlgorithms_Defs_Query

open QAlgorithms

namespace QGraphColl.Supplement

/-- §5, p.31 of A. Cornelissen, A. S. Gilani, S. Kintali, F. Le Gall, S. Patro, X. Zhou,
*Breaking the quantum barriers for Graph Collision*, arXiv:2611.05356 (version of October 2026,
sha256 21da7ff0…) ("Write `Q₂(f)` for the quantum query complexity with error at most `1/3`"), with
the convention of p.12 ("error at most 1/3 on every input"): a `T`-query algorithm with query
register `ι × κ` over the alphabet `κ` computes the partial Boolean function `f` on the domain
`D ⊆ κ^ι` with error at most `ε` when, for **every** `x ∈ D`, querying the standard oracle
`|i, c⟩ ↦ |i, c + x_i⟩` (`xorOracle x`; addition in the alphabet's group, `mod q` for
`κ = Fin q`) it outputs `f x` with probability at least `1 − ε`.

This is the published `QAlgorithms.QueryAlg.ComputesWithError` with the input alphabet generalised
from `Bool` to an arbitrary finite additive group `κ`; for `κ = Bool` the two coincide.

**Formalization Note.** The oracle is the `q`-ary one: one query reads one alphabet symbol `x_i`.
Inputs are not binary-encoded (that would change the query count by a factor `log q`). Values of
`f` outside `D` are never read. -/
def ComputesOn {ι κ W : Type*} [Fintype ι] [Fintype κ] [Fintype W] [DecidableEq ι]
    [DecidableEq κ] [DecidableEq W] [AddCommGroup κ] {T : ℕ} (A : QueryAlg ι κ W T)
    (out : (ι × κ) × W → Bool) (D : Finset (ι → κ)) (f : (ι → κ) → Bool) (ε : ℝ) : Prop :=
  ∀ x ∈ D, A.outputProb (xorOracle x) out (f x) ≥ 1 - ε

end QGraphColl.Supplement


