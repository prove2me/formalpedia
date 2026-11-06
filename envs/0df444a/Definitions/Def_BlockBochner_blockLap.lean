-- Prove2me | Definitions.Def_BlockBochner_blockLap
-- name    : BlockBochner_blockLap
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T01:37:59.258213+00:00
-- url     : https://prove2.me/theorems/83e79b3a-fc82-40ac-81a9-ed15251f2c6c
-- title:
--   Block Glauber Laplacian $L^{T_1,\dots,T_m}_{\mathrm{Glaub}}$
-- statement:
--   Let $T_1,\dots,T_m$ be disjoint sets of sites, $T=\bigsqcup_aT_a$, and $Y_a=X_{T_a}$. The block Glauber dynamics is the Glauber dynamics of the $m$-site spin system $(Y_1,\dots,Y_m)$ under the marginal $\mu_T$: it chooses a block uniformly and resamples its configuration conditioned on the other blocks. Its Laplacian on $L^2(\mu_T)$ is
--   $$L^{T_1,\dots,T_m}_{\mathrm{Glaub}}=\frac1m\sum_{a=1}^m\Bigl(I-E_{\mu_T}\bigl[\,\cdot\mid X_{T\setminus T_a}\bigr]\Bigr).$$
--
--   **Formalization Note** The factor is $1/m$, with $m$ the number of blocks. An empty block contributes the zero operator.
-- source:
--   Leake–Li, Beyond the Bochner Method: Optimal Spectral Gaps for Block Dynamics of Spin Systems like the O(N) Model, arXiv:2611.05228, Sec. 1.2, p.3

import Mathlib
import Definitions.Def_BlockBochner_condExpOn
import Definitions.Def_BlockBochner_blockUnion
import Definitions.Def_BlockBochner_marg

open MeasureTheory

namespace BlockBochner

/-- **Block Glauber Laplacian `L^{T₁,…,T_m}_Glaub`.** Leake–Li, *Beyond the Bochner Method: Optimal Spectral Gaps for Block Dynamics of Spin Systems like the O(N) Model*, arXiv:2611.05228, Sec. 1.2, p.3: the Glauber dynamics of the
`m`-site spin system `(Y₁, …, Y_m)`, `Y_a = X_{T_a}`, under the marginal of `µ` on `T`, "which chooses a
block uniformly and resamples its configuration conditioned on the other blocks under this marginal
law". Its Laplacian is `(1/m) Σ_a (I − E_{µ_T}[· | Y_b, b ≠ a])` on `L²(µ_T)`.

**Formalization Note** The operator acts on `L²` of the marginal `marg µ T` on `∏_{v∈T} S_v`;
conditioning on the other blocks is conditioning on the coordinates of `T ∖ T_a`. The factor is
`1/m`, with `m` the number of blocks. -/
noncomputable def blockLap {V : Type*} [DecidableEq V] {S : V → Type*} [∀ v, MeasurableSpace (S v)]
    (μ : Measure (∀ v, S v)) {m : ℕ} (T : Fin m → Finset V) :
    Lp ℝ 2 (marg μ (blockUnion T)) →L[ℝ] Lp ℝ 2 (marg μ (blockUnion T)) :=
  (m : ℝ)⁻¹ • ∑ a, (1 - condExpOn (marg μ (blockUnion T)) {v : blockUnion T | v.1 ∉ T a})

end BlockBochner


