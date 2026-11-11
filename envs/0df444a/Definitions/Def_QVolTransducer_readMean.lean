-- Prove2me | Definitions.Def_QVolTransducer_readMean
-- name    : QVolTransducer_readMean
-- status  : Definition
-- author  : @iris
-- created : 2026-11-10T21:22:50.621367+00:00
-- url     : https://prove2.me/theorems/609e0a23-d761-4d06-a775-a8ab3c08fc80
-- title:
--   Mean, variance and event probabilities of a value read out from an output register
-- statement:
--   Let $\varphi$ be a state of an output register with an answer part indexed by $i\in\{0,\dots,a\}$ and a garbage part indexed by $j\in\{0,\dots,g\}$, and let $\mathrm{val}(i)\in\mathbb R$ be the value attached to the answer $i$. Measuring $\varphi$ gives $(i,j)$ with probability $|\varphi(i,j)|^2$ and outputs $\bar\mu=\mathrm{val}(i)$. The module defines
--
--   $$
--   \mathbb E[\bar\mu]=\sum_{i,j}|\varphi(i,j)|^2\,\mathrm{val}(i),\qquad
--   \mathrm{Var}[\bar\mu]=\sum_{i,j}|\varphi(i,j)|^2\,(\mathrm{val}(i)-\mathbb E[\bar\mu])^2,
--   $$
--
--   and $\mathbb P[\bar\mu\in P]=\sum_{(i,j):\,\mathrm{val}(i)\in P}|\varphi(i,j)|^2$. These are the output laws of the mean and quantile estimation transducers.
--
--   **Formalization Note** Garbage registers are allowed, as the paper's estimators measure a subset of the qubits (p.25). For the output of a transducer applied to a unit vector, $\varphi$ is a unit vector, so these sums are the law of the measured value.
-- source:
--   Cornelissen, Apers, Gribling, Improved quantum volume estimation with transducers and amortized quantum walks, arXiv:2609.40217 (version of November 3, 2026, sha256 40d7b52d…), Theorems 10.2 and 10.3, pp.68–69 (PDF pp.70–71)

import Mathlib

namespace QVolTransducer

/-- The mean `E[µ̄]` of the value read out from an output register (Cornelissen, Apers, Gribling,
*Improved quantum volume estimation with transducers and amortized quantum walks*, arXiv:2609.40217
(version of November 3, 2026, sha256 40d7b52d…), Theorems 10.2 and 10.3, pp.68–69, where a
transducer "outputs a value"). The output register is `ℂ^(Fin (a+1) × Fin (g+1))`: an answer
register and a garbage register. Measuring a state `φ` of it in the computational basis gives the
outcome `(i, j)` with probability `|φ(i, j)|²` and the value `val i`; the mean of that value is
`Σ_{(i,j)} |φ(i,j)|² val(i)`.

**Formalization Note** Garbage registers are allowed, as the paper's estimators measure a subset
of the qubits (p.25). `φ` is a unit vector whenever it is the output of a transducer applied to a
unit vector, so these sums are the law of the measured value. -/
noncomputable def readMean {a g : ℕ} (φ : EuclideanSpace ℂ (Fin (a + 1) × Fin (g + 1)))
    (val : Fin (a + 1) → ℝ) : ℝ :=
  ∑ p, ‖φ p‖ ^ 2 * val p.1

/-- The variance `Var[µ̄] = Σ_{(i,j)} |φ(i,j)|² (val(i) − E[µ̄])²` of the value read out from the
output register (arXiv:2609.40217, Theorem 10.2, p.68). -/
noncomputable def readVar {a g : ℕ} (φ : EuclideanSpace ℂ (Fin (a + 1) × Fin (g + 1)))
    (val : Fin (a + 1) → ℝ) : ℝ :=
  ∑ p, ‖φ p‖ ^ 2 * (val p.1 - readMean φ val) ^ 2

open Classical in
/-- The probability that the value read out from the output register satisfies `P`
(arXiv:2609.40217, Theorem 10.3, p.69: "with probability at least 1 − ρ, …"):
`Σ_{(i,j) : P(val(i))} |φ(i,j)|²`. -/
noncomputable def readProb {a g : ℕ} (φ : EuclideanSpace ℂ (Fin (a + 1) × Fin (g + 1)))
    (val : Fin (a + 1) → ℝ) (P : ℝ → Prop) : ℝ :=
  ∑ p ∈ Finset.univ.filter (fun p => P (val p.1)), ‖φ p‖ ^ 2

end QVolTransducer


