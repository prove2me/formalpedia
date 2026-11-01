-- Prove2me | Definitions.Def_RelaxRoundPoA_IsSmoothHalf
-- name    : RelaxRoundPoA_IsSmoothHalf
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T07:50:30.39726+00:00
-- url     : https://prove2.me/theorems/7003fd58-c340-4fe1-b6f4-becfae9d424f
-- title:
--   $(\lambda,\mu)$-smooth for deviations to half the value
-- statement:
--   A mechanism $M$ with feasible outcomes $F$ is **$(\lambda,\mu)$-smooth for deviations to half the value**, $\lambda,\mu\ge0$, if for all valuation and bid profiles $v,b$ drawn from the weight classes, with $b_i'=\tfrac12v_i$,
--
--   $$
--   \sum_{i\in N}u_i\bigl((b_i',b_{-i}),v_i\bigr)\ \ge\ \lambda\,\mathrm{OPT}(v)-\mu\sum_{i\in N}\mathbf E\bigl[p_i(b)\bigr],\qquad \mathrm{OPT}(v)=\max_{x\in F}\sum_{i\in N}v_i(x).
--   $$
--
--   This is smoothness with one fixed deterministic deviation that depends only on the agent's own valuation. Lemma 1 derives it from smoothness, and Theorem 3′ transfers it through rounding.
--
--   **Formalization Note** $\mathrm{OPT}(v)$ is replaced by "for every $x\in F$", which is equivalent when the maximum exists.
-- source:
--   Dütting, Kesselheim, Tardos, Algorithms as Mechanisms: The Price of Anarchy of Relax-and-Round, arXiv:1511.09208v1, §3, p.8 (Lemma 1) and p.9 (Theorem 3′)

import Mathlib
import Definitions.Def_RelaxRoundPoA_Mechanism
import Definitions.Def_RelaxRoundPoA_IsProfile
import Definitions.Def_RelaxRoundPoA_utility

open MeasureTheory NNReal

namespace RelaxRoundPoA

/-- **(λ, µ)-smooth for deviations to half the value.**
Dütting, Kesselheim, Tardos, arXiv:1511.09208v1, §3, p.8 (Lemma 1): "`M` is (λ/2, µ)-smooth for
deviations to half the value. That is, for all bid vectors `b` and bids `b'_i = ½ v_i` for all
`i ∈ N`, `∑_{i∈N} u_i((b'_i, b_{−i}), v_i) ≥ (λ/2) OPT(v) − µ ∑_{i∈N} p_i(b)`"; Theorem 3′ (p.9)
uses the same notion for `M'`.

`IsSmoothHalf Val Feas M lam mu` says `0 ≤ lam`, `0 ≤ mu`, and for all profiles `v`, `b` drawn from
`Val` and every feasible `x ∈ Feas`,
`lam · ∑_i v_i(x) − mu · ∑_i E[p_i(b)] ≤ ∑_i u_i((½ v_i, b_{−i}), v_i)`.

**Formalization Note** `λ, µ ≥ 0` are part of the definition of smoothness on p.7. `OPT(v)` is the
maximum of `∑_i v_i` over the feasible outcomes; the inequality is required for every `x ∈ Feas`,
which is equivalent when the maximum exists. -/
def IsSmoothHalf {N : Type*} [Fintype N] [DecidableEq N] {Ω' : Type*} [MeasurableSpace Ω']
    (Val : N → Set (Ω' → ℝ≥0)) (Feas : Set Ω') (M : Mechanism N Ω') (lam mu : ℝ) : Prop :=
  0 ≤ lam ∧ 0 ≤ mu ∧
    ∀ v : N → Ω' → ℝ≥0, IsProfile Val v → ∀ b : N → Ω' → ℝ≥0, IsProfile Val b → ∀ x ∈ Feas,
      lam * ∑ i, (v i x : ℝ) - mu * ∑ i, M.expPay b i ≤
        ∑ i, utility M i (Function.update b i (fun y => v i y / 2)) (v i)

end RelaxRoundPoA


