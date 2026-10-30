-- Prove2me | Definitions.Def_AKNMixed_FQP_ProbFun
-- name    : AKNMixed_FQP_ProbFun
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T03:14:28.735272+00:00
-- url     : https://prove2.me/theorems/9d3fda12-3f2a-4aab-b495-fd5d6f4f2c3d
-- title:
--   Probabilistic function $f:\{0,1\}^m\to\Delta(\{0,1\}^p)$ (subroutine)
-- statement:
--   A **probabilistic function** (subroutine) from $m$ to $p$ bits assigns to every input $i\in\{0,1\}^m$ a probability distribution on $\{0,1\}^p$: numbers $f_{i,j}\ge0$ with
--
--   $$\sum_{j\in\{0,1\}^p} f_{i,j}=1\qquad\text{for every } i .$$
--
--   $f_{i,j}$ is the probability that $f$ outputs $j$ on input $i$.
--
--   **Formalization Note** The paper writes the codomain as $R^{\{0,1\}^p}$ and says that $f$ "outputs $j$ with distribution which depends on the input $i$"; nonnegativity and normalization are therefore part of the structure.
-- source:
--   Aharonov, Kitaev, Nisan, Quantum Circuits with Mixed States, arXiv:quant-ph/9806029v1, §4.2, unnumbered, p. 9

import Mathlib
import Definitions.Def_QAlgorithms_Defs_Basic

namespace AKNMixed.FQP

open QAlgorithms

/-- **A probabilistic function (subroutine) `f : {0,1}^m → distributions on {0,1}^p`.**
Aharonov, Kitaev, Nisan, *Quantum Circuits with Mixed States*, arXiv:quant-ph/9806029v1, §4.2,
unnumbered, p. 9: "A (probabilistic) subroutine is a function, f : {0,1}^m ⟼ R^{{0,1}^p}, which
outputs j with distribution which depends on the input i."

`f.prob i j` is the probability `f_{i,j}` that `f` outputs `j` on input `i`; the probabilities
are nonnegative and sum to `1` over `j` for every `i`.

**Formalization Note.** Bit strings are `Qubits m = Fin m → Bool`. The codomain
`R^{{0,1}^p}` of the paper is read, as its sentence says, as a probability distribution on
`{0,1}^p` for each input, so nonnegativity and normalization are part of the structure
(Definition 5's weights `∏ᵢ f_{i,d(i)}` are probabilities only under these). -/
structure ProbFun (m p : ℕ) where
  /-- `prob i j = f_{i,j}`, the probability of output `j` on input `i`. -/
  prob : Qubits m → Qubits p → ℝ
  nonneg : ∀ i j, 0 ≤ prob i j
  sum_one : ∀ i, ∑ j, prob i j = 1

end AKNMixed.FQP


