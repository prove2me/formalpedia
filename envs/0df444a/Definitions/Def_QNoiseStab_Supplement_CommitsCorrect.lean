-- Prove2me | Definitions.Def_QNoiseStab_Supplement_CommitsCorrect
-- name    : QNoiseStab_Supplement_CommitsCorrect
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T00:19:24.902328+00:00
-- url     : https://prove2.me/theorems/f6fae763-595f-45c9-b4e4-11a9d8195780
-- title:
--   A commit sequence computes an output vector
-- statement:
--   Let $q:V\to Y$ be the post-processing map and $z\in Y^K$ a target output vector. A sequence $o=(o_0,\dots,o_T)$ of step outcomes **computes $z$** if
--
--   1. every commit $(j,v)$ in $o$ is correct: $q(v)=z_j$ (repeated commits of the same coordinate must all be correct), and
--   2. every output coordinate $j\in K$ is committed at least once.
--
--   An algorithm computes a multi-output function $f$ on input $x$ when its commit sequence computes $f(x)$: all of $f(x)$ is produced and nothing wrong is produced.
-- source:
--   Beame–Holman–Kornerup, A Noise Operator Approach to Quantum Query Complexity and Time-Space Tradeoff Lower Bounds, arXiv:2609.40334 (version of 2026-11-02, sha256 814fe20e…), §2.2, p.7 (commits as partial assignments to one output); Definition 2.4, p.7; proofs on p.20 and p.32

import Mathlib

set_option autoImplicit false

namespace QNoiseStab.Supplement

/-- A commit sequence **computes the output vector** `z : K → Y` (Beame–Holman–Kornerup, *A Noise Operator Approach to Quantum Query Complexity and Time-Space Tradeoff Lower Bounds*, arXiv:2609.40334 (version of 2026-11-02, sha256 814fe20e…), §2.2, p.7: each commit
is "a partial assignment to 1 output of f"; Definition 2.4, p.7, agreement `f(x) ∥ τ`; proofs on
p.20 "each hash function h requires m output bits to be produced", p.32 "it must produce n output
values in total"): every committed pair `(j, v)` has `q v = z j` (all commits agree with `z`,
repeated commits of a coordinate included), and every output coordinate `j` is committed at least
once. -/
def CommitsCorrect {K V Y : Type} {T : ℕ} (q : V → Y) (z : K → Y)
    (o : Fin (T + 1) → Option (K × V)) : Prop :=
  (∀ t j v, o t = some (j, v) → q v = z j) ∧ ∀ j, ∃ t v, o t = some (j, v)

end QNoiseStab.Supplement


