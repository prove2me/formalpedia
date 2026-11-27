-- Prove2me | Definitions.Def_WildeQIT_Compression_Supplement_QFeedbackCode_errorProb
-- name    : WildeQIT_Compression_Supplement_QFeedbackCode_errorProb
-- status  : Definition
-- author  : @iris
-- created : 2026-11-27T04:02:58.234594+00:00
-- url     : https://prove2.me/theorems/0acfb7d8-3b8f-5b3e-ae14-f741679d65c0
-- title:
--   Error probability $\Pr\{M'\neq M\}$ of a quantum-feedback protocol
-- statement:
--   For a protocol for classical communication with quantum feedback over $n$ channel uses, with a uniformly distributed message $M$ and Bob's estimate $M'$ obtained by measuring his systems $B_nB'_n$ at the end,
--
--   $$
--   \Pr\{M'\neq M\}=\frac1{|\mathcal M|}\sum_{m\in\mathcal M}\operatorname{Tr}\{(I-\Lambda_m)\,\omega^m_{B_nB'_n}\},
--   $$
--
--   where $\omega^m_{B_nB'_n}$ is Bob's state after the $n$-th channel use when the message is $m$. A protocol is $\varepsilon$-good if $\Pr\{M'\neq M\}\le\varepsilon$.
--
--   **Formalization Note** $\omega^m_{B_nB'_n}$ is the partial trace over Alice's memory of the state after the $n$-th channel use. The value at $n=0$ (no channel use) is not meaningful; achievability only uses large $n$.
-- source:
--   Wilde, From Classical to Quantum Shannon Theory, arXiv:1106.1445v8, proof of Theorem 21.5.2, p. 606

import Mathlib
import Definitions.Def_WildeQIT_Compression_Supplement_QFeedbackCode_afterChannel
import Definitions.Def_WildeQIT_partialTrace

/-!
Wilde, *From Classical to Quantum Shannon Theory*, arXiv:1106.1445v8, p. 606 (the error
probability `Pr{M′ ≠ M}` of a protocol for classical communication with quantum feedback).
-/

open Matrix

namespace WildeQIT.Compression.Supplement

/-- **Error probability `Pr{M′ ≠ M}`** of a quantum-feedback protocol with `n` channel uses
(Wilde, *From Classical to Quantum Shannon Theory*, arXiv:1106.1445v8, p. 606): "we assume that the
random variable `M` modeling Alice's message selection is a uniform random variable, and Bob
obtains a random variable `M′` by measuring all of his systems `Bₙ` and `B′ₙ` at the end of the
protocol. For any ε-good protocol … the bound `Pr{M′ ≠ M} ≤ ε` applies." With Bob's state
`ωᵐ_{BₙB′ₙ}` after the last channel use given message `m`,
`Pr{M′ ≠ M} = (1/|M|) ∑_m Tr{(I − Λ_m) ωᵐ_{BₙB′ₙ}}`.

**Formalization Note.** `ωᵐ_{BₙB′ₙ}` is `Tr_{A′ₙ}` (published `WildeQIT.partialTraceLeft`, after
regrouping) of `c.afterChannel N m (n − 1)`, the state after the `n`-th channel use. The value at
`n = 0` (no channel use) is not meaningful; achievability only uses large `n`. The trace of a
positive semidefinite operator is real; its real part is taken. -/
noncomputable def QFeedbackCode.errorProb {a b : Type} [Fintype a] [Fintype b]
    [DecidableEq a] [DecidableEq b] {n k : ℕ} (c : QFeedbackCode a b n k) (N : QChannel a b) : ℝ :=
  (1 / (k : ℝ)) * ∑ m : Fin k,
    (((1 : Matrix (b × Fin c.dB) (b × Fin c.dB) ℂ) - c.meas m) *
      WildeQIT.partialTraceLeft
        (Matrix.reindex (Equiv.prodAssoc _ _ _) (Equiv.prodAssoc _ _ _)
          (c.afterChannel N m (n - 1)))).trace.re

end WildeQIT.Compression.Supplement


