-- Prove2me | Definitions.Def_TTTSampling_alg3Abort
-- name    : TTTSampling_alg3Abort
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T21:43:26.01321+00:00
-- url     : https://prove2.me/theorems/55af04b1-ba08-44b8-9cf4-e924a5b5adbf
-- title:
--   Algorithm 3 with the abort rule of the proof of Theorem 3.2
-- statement:
--   The proof of Theorem 3.2 runs Algorithm 3 with failure tolerance $\delta/2$ and modifies it so that "whenever its number of oracle calls reaches the threshold in (34), it aborts and outputs an arbitrary symbol".
--
--   For constants $C_{\mathsf N}$ and $C$, the **aborted algorithm** runs Algorithm 3 with tolerance $\delta/2$ and threshold
--   $$
--   \theta=C\cdot n\cdot|\Sigma|\cdot R^{12}\cdot\sqrt{\log|\mathcal F|}\cdot\log\frac1{\delta'}\cdot\log\frac{R\log|\mathcal F|}{\delta'},\qquad \delta'=\min(\delta,1/2);
--   $$
--   a run that would use more than $\theta$ oracle calls outputs $x_0$ instead, having made at most $\lfloor\theta\rfloor$ calls.
--
--   **Formalization Note** The abort is defined on the joint law of (output, count): runs with count above $\theta$ are replaced by $(x_0,\lfloor\theta\rfloor)$. The δ-factors of the threshold use $\delta'=\min(\delta,1/2)$, matching the corrected Theorem 3.2.
-- source:
--   Golowich, Moitra, Rohatgi, The Power of Test-Time Training for Approximate Sampling, arXiv:2606.11437 (version of November 3, 2026), proof of Theorem 3.2, p.32 (PDF p.34), (34)

import Mathlib
import Definitions.Def_TTTSampling_alg3
import Definitions.Def_TTTSampling_qBound

namespace TTTSampling

/-- **Algorithm 3 with the abort rule** of the proof of Theorem 3.2.

Golowich, Moitra, Rohatgi, arXiv:2606.11437 (version of November 3, 2026), proof of Theorem 3.2,
printed p.32 (PDF p.34): "Run Algorithm 3 with failure tolerance δ/2. … We can modify Algorithm 3
so that, whenever its number of oracle calls reaches the threshold in (34), it aborts and outputs
an arbitrary symbol."

`alg3Abort C_N C R δ ℱ µ̂ x₀` runs `alg3` with tolerance `δ/2`; with the threshold
`thr = C · qBound n |Σ| R |ℱ| (min δ (1/2))` (the bound (34) with its constant `C`), a run whose
count exceeds `thr` is replaced by the output `x₀` with count `⌊thr⌋`.

**Formalization Note**
* The abort is encoded on the joint law of (output, count): a run is aborted exactly when its
  count exceeds the threshold, and an aborted run has made at most `⌊thr⌋` calls. So the count
  bound of the aborted algorithm holds by construction; its content is the output law.
* The δ-factors of the threshold are evaluated at `min δ (1/2)`, as in the corrected Theorem 3.2
  (the printed bound tends to `0` as `δ → 1`). -/
noncomputable def alg3Abort {α : Type} [Fintype α] [LinearOrder α] {n : ℕ} (C_N : ℕ) (C R δ : ℝ)
    (F : Finset (PMF (Fin n → α))) (μh : List α → NNReal) (x₀ : Fin n → α) :
    PMF ((Fin n → α) × ℕ) :=
  (alg3 C_N R (δ / 2) F μh x₀).map fun r =>
    if (r.2 : ℝ) ≤ C * qBound n (Fintype.card α) R F.card (min δ (1 / 2)) then r
    else (x₀, ⌊C * qBound n (Fintype.card α) R F.card (min δ (1 / 2))⌋₊)

end TTTSampling


