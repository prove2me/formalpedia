-- Prove2me | Definitions.Def_mme_subrank_capacity
-- name    : mme_subrank_capacity
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-05-31T17:30:08.101103+00:00
-- url     : https://prove2.me/theorems/a5715fab-9034-49cb-938d-f5545b5c4486
-- statement:
--   **Subrank capacity** — the asymptotic value functional that controls every matrix-multiplication exponent bound through Strassen's τ-theorem.
--
--   For an order-3 tensor `T : TensorObj K 3`,
--
--   $$\widetilde V(T) \;:=\; \sup\Bigl\{ V \geq 1 \;\Bigm|\; \forall \varepsilon > 0,\; \exists^{\infty} N,\; \exists\; \bigoplus_{i=1}^{k_N}\langle a_i, b_i, c_i\rangle \;\leq_{\mathrm{Strassen}}\; T^{\otimes N},\;\; V^N(1-\varepsilon) \leq \sum_{i=1}^{k_N} (a_i b_i c_i)^{1/3} \Bigr\}.$$
--
--   **Interpretation.** $\widetilde V(T)$ measures how rich the "direct sum of matrix-multiplication" Strassen-degenerations of $T$ can be made, asymptotically, with the matrix-multiplication dimensions weighted by their $1/3$-power. It is the *asymptotic value at the trivial spectrum point* in Wigderson–Zuiddam's terminology.
--
--   **Why this functional.** When $T$ has a known asymptotic-rank upper bound $\widetilde R(T) \leq R$, Schönhage's τ-theorem (already on the platform as `mme_asymptotic_sum_inequality`) gives
--
--   $$\sum_i (a_i b_i c_i)^{\omega/3} \;\leq\; \widetilde R(T)^N \;\leq\; R^N$$
--
--   for every realising family. Combined with $\sum_i (a_i b_i c_i)^{1/3} \geq V^N(1-\varepsilon)$ via Hölder's inequality, this yields the canonical abstract bound
--
--   $$\omega \;\leq\; \frac{\log R}{\log \widetilde V(T)}.$$
--
--   **Reusability.** This definition is **paper-agnostic**. Every present and future ω-bound improvement — Strassen 1986 (τ-theorem), Coppersmith–Winograd 1990 ($\omega < 2.376$), Stothers 2010 ($\omega < 2.3737$), Vassilevska Williams 2012 ($\omega < 2.3727$), Le Gall 2014 ($\omega < 2.3729$), Alman–Vassilevska Williams 2020 ($\omega < 2.3729$) — reduces to producing a lower bound on $\widetilde V(T)$ for the paper's specific tensor $T$. The abstract bridge `mme_omega_le_of_subrank_capacity` then converts that lower bound, together with an asymptotic-rank upper bound, into a bound on $\omega$.
-- source:
--   https://arxiv.org/abs/2212.11824

import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Order.Filter.AtTopBot.Defs
import Definitions.Def_mme_tensor_rank

/-! # Subrank capacity — the asymptotic value functional

The **subrank capacity** of an order-3 tensor `T` is the asymptotic value
that a direct sum of matrix-multiplication tensors can achieve as a Strassen
restriction of a Kronecker power of `T`. It is a *single real number*
controlled by every laser-style argument in the matrix-multiplication
literature: Strassen 1986, CW 1990, Stothers 2010, VW 2012, Le Gall 2014.

Concretely, `subrankCapacity T` is the supremum of `V ≥ 1` such that for
every `ε > 0`, infinitely often as `N → ∞`, there is a Strassen restriction
`⊕_i ⟨a_i, b_i, c_i⟩ ≤ T^{⊗N}` with `∑_i (a_i·b_i·c_i)^{1/3} ≥ V^N · (1-ε)`.

Coupled with the τ-theorem (`mme_asymptotic_sum_inequality`), this functional
yields the abstract reduction `ω ≤ log R̄(T) / log subrankCapacity(T)` (see
`Thm_mme_omega_le_of_subrank_capacity`). Every concrete tensor that bounds
`ω` from above does so by lower-bounding its `subrankCapacity`. -/

universe u

open BigOperators Filter

namespace MME

variable {K : Type u} [Field K]

/-- The asymptotic value functional. -/
noncomputable def subrankCapacity (T : TensorObj K 3) : ℝ :=
  sSup { V : ℝ | 1 ≤ V ∧
    ∀ ε > (0 : ℝ), ∃ᶠ N in atTop,
      ∃ (k : ℕ) (a b c : Fin k → ℕ),
        TensorObj.Restrict
          (TensorObj.bigAdd (fun i => MMObj K (a i) (b i) (c i)))
          (T.kronPow N)
        ∧ V ^ N * (1 - ε) ≤ ∑ i, ((a i * b i * c i : ℕ) : ℝ) ^ ((1 : ℝ) / 3) }

end MME


