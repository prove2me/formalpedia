-- Prove2me | Definitions.Def_MaxEntSampling_zPC
-- name    : MaxEntSampling_zPC
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T18:59:18.540291+00:00
-- url     : https://prove2.me/theorems/72021883-4e3b-4712-add8-6bac04addef9
-- title:
--   The value $z^{LD}$ of the primal characterization PC (9)
-- statement:
--   Let $v_i\in\mathbb R^d$ be the $i$-th column of $V\in\mathbb R^{d\times n}$. The **primal characterization** of the Lagrangian dual is
--
--   $$
--   z^{LD} := \max_x\Bigl\{\Gamma_s\Bigl(\sum_{i\in[n]}x_iv_iv_i^\top\Bigr) : \sum_{i\in[n]}x_i=s,\ x\in[0,1]^n\Bigr\}.
--   $$
--
--   Theorem 2 shows that it equals the value of LD (5) and is attained; α-optimality (§3.1) is measured against it.
--
--   **Formalization Note** The value is the supremum in the extended reals over $D$; $\sum_i x_iv_iv_i^\top$ is `PropVolSampling.Reduction.weightedGram V x`.
-- source:
--   Li, Xie, Best Principal Submatrix Selection for the Maximum Entropy Sampling Problem, arXiv:2001.08537v3, eq. (9), p.9 (PDF p.9)

import Mathlib
import Definitions.Def_PropVolSampling_Reduction_Model
import Definitions.Def_MaxEntSampling_GammaS
import Definitions.Def_MaxEntSampling_feasD

namespace MaxEntSampling

open PropVolSampling.Reduction

/-- **The optimal value `z^LD` of the primal characterization PC (9).**
Li, Xie, *Best Principal Submatrix Selection for the Maximum Entropy Sampling Problem*,
arXiv:2001.08537v3, eq. (9), p.9 (PDF p.9):
"(PC) z^LD := max_x { Γs(Σ_{i∈[n]} xi vi vi^⊤) : Σ_{i∈[n]} xi = s, x ∈ [0,1]^n }".

`zPC V s` is the supremum of `Γ_s(Σ_i x_i v_i v_iᵀ)` over `x ∈ D`, where `v_i` is the `i`-th
column of `V`.

**Formalization Note.** `Σ_i x_i v_i v_iᵀ` is `PropVolSampling.Reduction.weightedGram V x`. The
value is the supremum in `EReal` (`sSup`); Theorem 2 states that it is attained. -/
noncomputable def zPC {d n : ℕ} (V : Matrix (Fin d) (Fin n) ℝ) (s : ℕ) : EReal :=
  sSup ((fun x => GammaS s (weightedGram V x)) '' feasD n s)

end MaxEntSampling


