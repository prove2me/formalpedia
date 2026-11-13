-- Prove2me | Definitions.Def_RvsCert_quantQC
-- name    : RvsCert_quantQC
-- status  : Definition
-- author  : @iris
-- created : 2026-11-12T06:38:29.819539+00:00
-- url     : https://prove2.me/theorems/f31cb1f3-cc6e-4a9d-bf99-b260aca1646c
-- title:
--   Bounded-error quantum query complexity $Q(f)$
-- statement:
--   A $T$-query quantum algorithm starts from a fixed unit vector on a query register $\iota\times\{0,1\}$ together with a finite workspace, and applies fixed unitaries $U_0,\dots,U_T$ interleaved with $T$ standard queries $O_x:|i,b\rangle\mapsto|i,b\oplus x_i\rangle$; its output is a Boolean function of the measured basis state. For a Boolean function $f$, $Q(f)$ is the least $T$ such that some $T$-query algorithm outputs $f(x)$ with probability at least $2/3$ on **every** input $x$ ($\infty$ if none exists).
--
--   **Formalization Note** Built on the published `QAlgorithms.QueryAlg`, `xorOracle` and `ComputesWithError` (domain all inputs, error $1/3$); the workspace is `Fin m` for some $m$; the value lies in `ℕ∞`.
-- source:
--   Ben-David–Kothari, Randomized query complexity can beat certificate complexity, arXiv:2609.15063v1, Theorem 1, p.1; Lemma 5, p.3 (standard notion, [BdW02])

import Mathlib
import Definitions.Def_QAlgorithms_Defs_Query

namespace RvsCert

/-- **Bounded-error quantum query complexity** `Q(f)` (standard, [BdW02]; Theorem 1, p.1 and
Lemma 5, p.3 of Ben-David–Kothari, *Randomized query complexity can beat certificate complexity*, arXiv:2609.15063v1): the least `T` such that some `T`-query quantum
algorithm with standard (XOR) queries `|i, b⟩ ↦ |i, b ⊕ xᵢ⟩` and a finite workspace `Fin m`
outputs `f x` with probability at least `2/3` on **every** input `x`.

**Formalization Note.** Uses the published `QAlgorithms.QueryAlg` (input-independent unit start
vector and unitaries, exactly `T` queries), `xorOracle` and `ComputesWithError` with domain
`Finset.univ` (a total function) and error `1/3`. The output is a Boolean function `out` of the
measured basis state. The value lies in `ℕ∞` (`⊤` if infeasible). -/
noncomputable def quantQC {ι : Type} [Fintype ι] [DecidableEq ι] (f : (ι → Bool) → Bool) : ℕ∞ :=
  ⨅ (T : ℕ) (_ : ∃ (m : ℕ) (A : QAlgorithms.QueryAlg ι Bool (Fin m) T)
      (out : (ι × Bool) × Fin m → Bool), A.ComputesWithError out Finset.univ f (1 / 3)),
    (T : ℕ∞)

end RvsCert


