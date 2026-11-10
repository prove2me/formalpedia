-- Prove2me | Definitions.Def_QThermalClassical_HasStepExpect
-- name    : QThermalClassical_HasStepExpect
-- status  : Definition
-- author  : @iris
-- created : 2026-11-09T23:15:40.152943+00:00
-- url     : https://prove2.me/theorems/6082336e-0fd6-488a-91b8-a10ee3360c1c
-- title:
--   Expectation over one iteration of Algorithm 1
-- statement:
--   For two samplers $\sigma_1,\sigma_2$ and $q$, the expectation over one iteration of Algorithm 1 draws $(b_1,E_1)\sim\sigma_1$ and independently $(b_2,E_2)\sim\sigma_2$ (lines 8–9), and $J$ with probabilities $p_1=q$, $p_{J}=(1-q)/6$ for $J\neq1$ (line 10):
--   $$
--   \mathbb E[F]=\sum_{(t_1,t_2)\in\mathbb N^2}w^{(1)}_{t_1}w^{(2)}_{t_2}\sum_{j_1,j_2}q^{(1)}_{t_1,j_1}q^{(2)}_{t_2,j_2}\sum_{J=1}^7p_J\,F(o^{(1)}_{t_1,j_1},o^{(2)}_{t_2,j_2},J).
--   $$
--   This is the expectation $\mathbb E$ of Lemma 12, eq. (87).
--
--   **Formalization Note** The sum over pairs of blocks is unconditional; independence is the product of the block weights.
-- source:
--   J. Cotler, H. Putterman, A. Zlokapa, When quantum thermal states look classical, arXiv:2607.28536 (held version, sha256 7491d0b2…), Algorithm 1, lines 8–10, p.27; Lemma 12, eq. (87), p.29

import Mathlib
import Definitions.Def_QThermalClassical_pinStep

set_option autoImplicit false

namespace QThermalClassical

variable {Q : Type} [Fintype Q] [DecidableEq Q]

/-- The expectation over one iteration of Algorithm 1 (lines 8–10): `(b₁, E₁)` drawn from `σ₁`
and, independently, `(b₂, E₂)` from `σ₂`, and `J` drawn with probabilities `p_J` (`pJ q`).
`HasStepExpect q σ₁ σ₂ F A` says `𝔼[F(o₁, o₂, J)] = A`, where the pair of blocks `(t₁, t₂)` has
probability `w₁(t₁) w₂(t₂)` and inside it the finite conditional mean is taken.

Source: J. Cotler, H. Putterman, A. Zlokapa, *When quantum thermal states look classical*,
arXiv:2607.28536 (held version, sha256 7491d0b2…), Algorithm 1, lines 8–10, p.27; Lemma 12,
eq. (87), p.29.

**Formalization Note.** The sum over block pairs `(t₁, t₂) ∈ ℕ × ℕ` is an unconditional
(`HasSum`) sum; independence of the two samples is the product of their weights. -/
def HasStepExpect (q : ℝ) (σ₁ σ₂ : Sampler Q) (F : Outcome Q → Outcome Q → Fin 7 → Op Q)
    (A : Op Q) : Prop :=
  HasSum (fun t : ℕ × ℕ => (σ₁.w t.1 * σ₂.w t.2) •
    ∑ j₁, ∑ j₂, (σ₁.q t.1 j₁ * σ₂.q t.2 j₂) •
      ∑ J : Fin 7, pJ q J • F (σ₁.o t.1 j₁) (σ₂.o t.2 j₂) J) A

end QThermalClassical


