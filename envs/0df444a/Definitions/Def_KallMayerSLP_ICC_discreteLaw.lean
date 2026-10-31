-- Prove2me | Definitions.Def_KallMayerSLP_ICC_discreteLaw
-- name    : KallMayerSLP_ICC_discreteLaw
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T22:09:57.732814+00:00
-- url     : https://prove2.me/theorems/70c9760a-46d0-41af-8d86-47c102c53d31
-- title:
--   Finite discrete distribution (4.7)
-- statement:
--   A random vector $\xi$ with **finite discrete distribution** takes the realizations $\hat\xi^1,\dots,\hat\xi^N$ with probabilities $p_1,\dots,p_N$. Its law is
--   $$
--   \sum_{k=1}^N p_k\,\delta_{\hat\xi^k}.
--   $$
--   The expectations in the polyhedral representations are taken against this measure, so each integrated probability function becomes a finite sum.
--
--   **Formalization Note** The conditions $p_k>0$ and $\sum_k p_k=1$ are hypotheses of the theorems. The realizations need not be distinct. Indices are $0$-based: `Fin N` stands for $\mathcal N=\{1,\dots,N\}$.
-- source:
--   Kall & Mayer, Stochastic Linear Programming (2005), Chapter 2, (4.7), p.151 (PDF 161)

import Mathlib

open MeasureTheory

namespace KallMayerSLP.ICC

/-- **The finite discrete distribution (4.7).**
Kall & Mayer, *Stochastic Linear Programming* (2005), Chapter 2, (4.7), p.151 (PDF 161): `ξ` has a
finite discrete distribution with `N` realizations `ξ̂¹, …, ξ̂ᴺ` and probabilities `p₁, …, p_N`; the
law is `Σ_k p_k δ_{ξ̂ᵏ}`.

**Formalization Note.** The conditions `p_k > 0` and `Σ_k p_k = 1` are hypotheses of the theorems,
not part of this definition. Index base `0`: `Fin N` stands for `𝒩 = {1, …, N}`. The realizations
are not required to be distinct; repeated atoms simply add their weights. -/
noncomputable def discreteLaw {Ξ : Type*} [MeasurableSpace Ξ] {N : ℕ} (p : Fin N → ℝ)
    (ξhat : Fin N → Ξ) : Measure Ξ :=
  ∑ k, ENNReal.ofReal (p k) • Measure.dirac (ξhat k)

end KallMayerSLP.ICC


