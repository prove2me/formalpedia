-- Prove2me | Definitions.Def_ABPOnline_coupledZ
-- name    : ABPOnline_coupledZ
-- status  : Definition
-- author  : @iris
-- created : 2026-11-05T20:55:45.076644+00:00
-- url     : https://prove2.me/theorems/75ed837c-fd4b-462e-a0e4-459d7633cdb8
-- title:
--   Brownian mesh, mesh $\sigma$-fields $\mathcal G^B_k$, and the coupled inputs $Z_{k+1}$ and signs $\varepsilon_{k+1}$
-- statement:
--   Let $B=(B_1,\dots,B_M)$ be an $M$-dimensional process, $t_k=k/N$, and write $B_{t_k}\in\mathbb R^M$ for the mesh values and $\Delta B_{k+1}:=B_{t_{k+1}}-B_{t_k}$ for the mesh increments. The **Brownian mesh $\sigma$-field** is
--   $$
--   \mathcal G^B_k:=\sigma(B_{t_0},\dots,B_{t_k}).
--   $$
--   Given drifts $b_0,b_1,\dots$ (random vectors in $\mathbb R^M$), the **coupled Gaussian input** $Z_{k+1}$ is obtained from $\Delta B_{k+1}$ by the inverse steering map of Lemma 2.5 with the drift $b_k$, and the **online sign** $\varepsilon_{k+1}$ is the sign (10) of the steering construction for $b_k$ and $Z_{k+1}$. The module also defines $\sigma(Z_1,\dots,Z_k)$.
--
--   This is the coupling between signed Gaussian columns and Brownian increments analysed in Lemma B.1 and Proposition 4.6.
--
--   **Formalization Note** Indices are $0$-based: `coupledZ N b B k` is $Z_{k+1}$ and `coupledSign N b B k` is $\varepsilon_{k+1}$.
-- source:
--   Jo, Lee, The Exact Online Threshold for the Asymmetric Binary Perceptron, arXiv:2609.02124 (artifact sha256 bd5e2bdb18a47b7e806191ae9b888a6e4e7e150a9bd50e541b7587007d07a7a2), (23), p.15 (PDF p.16); §B and Lemma B.1, p.33 (PDF p.34)

import Mathlib
import Definitions.Def_ABPOnline_steerSign

set_option autoImplicit false

open MeasureTheory
open scoped NNReal

namespace ABPOnline

variable {Ω : Type*} {M : ℕ}

/-- The Brownian mesh value `B_{t_k} ∈ ℝ^M` at `t_k = k/N` (arXiv:2609.02124, (23), printed
p.15, PDF p.16, and §B, p.33). -/
noncomputable def meshVal (B : Fin M → ℝ≥0 → Ω → ℝ) (N k : ℕ) (ω : Ω) : Fin M → ℝ :=
  fun i => B i ((k : ℝ≥0) / N) ω

/-- The mesh increment `∆B_{k+1} = B_{t_{k+1}} − B_{t_k} ∈ ℝ^M` (arXiv:2609.02124, §B, p.33). -/
noncomputable def meshIncr (B : Fin M → ℝ≥0 → Ω → ℝ) (N k : ℕ) (ω : Ω) : Fin M → ℝ :=
  fun i => B i (((k + 1 : ℕ) : ℝ≥0) / N) ω - B i ((k : ℝ≥0) / N) ω

/-- The Brownian mesh σ-algebra `G^B_k = σ(B_{t_0}, …, B_{t_k})` (arXiv:2609.02124, (23),
p.15). -/
noncomputable def meshSigma [MeasurableSpace Ω] (B : Fin M → ℝ≥0 → Ω → ℝ) (N k : ℕ) : MeasurableSpace Ω :=
  ⨆ j ∈ Finset.range (k + 1), MeasurableSpace.comap (meshVal B N j) inferInstance

/-- The Gaussian input `Z_{k+1}` produced from the Brownian increment `∆B_{k+1}` by the inverse map
of Lemma 2.5 with the drift `b_k` (arXiv:2609.02124, Lemma B.1, printed p.33, PDF p.34, and
Proposition 4.6, p.15). `b k ω` is the drift `b_k` at the sample point `ω`. -/
noncomputable def coupledZ (N : ℕ) (b : ℕ → Ω → Fin M → ℝ) (B : Fin M → ℝ≥0 → Ω → ℝ)
    (k : ℕ) (ω : Ω) : Fin M → ℝ :=
  steerInv N (b k ω) (meshIncr B N k ω)

/-- The online sign `ε_{k+1}`: the sign (10) of the steering construction for the drift `b_k`
and the input `Z_{k+1}` (arXiv:2609.02124, Proposition 4.6, p.15). -/
noncomputable def coupledSign (N : ℕ) (b : ℕ → Ω → Fin M → ℝ) (B : Fin M → ℝ≥0 → Ω → ℝ)
    (k : ℕ) (ω : Ω) : ℝ :=
  steerSign N (b k ω) (coupledZ N b B k ω)

/-- The σ-algebra `σ(Z_1, …, Z_k)` of the first `k` Gaussian inputs of the coupling
(arXiv:2609.02124, (82), p.33). -/
noncomputable def coupledZSigma [MeasurableSpace Ω] (N : ℕ) (b : ℕ → Ω → Fin M → ℝ)
    (B : Fin M → ℝ≥0 → Ω → ℝ) (k : ℕ) : MeasurableSpace Ω :=
  ⨆ j ∈ Finset.range k, MeasurableSpace.comap (coupledZ N b B j) inferInstance

end ABPOnline


