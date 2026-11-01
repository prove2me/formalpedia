-- Prove2me | Definitions.Def_RelaxRoundPoA_IsSmooth
-- name    : RelaxRoundPoA_IsSmooth
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T07:50:42.562827+00:00
-- url     : https://prove2.me/theorems/3b1c8e0a-9688-41d3-9f11-6e15e4f387d3
-- title:
--   $(\lambda,\mu)$-smooth mechanism
-- statement:
--   Let $F\subseteq\Omega'$ be the mechanism's feasible outcomes and $\lambda,\mu\ge0$. A mechanism $M$ is **$(\lambda,\mu)$-smooth** (Syrgkanis–Tardos) if for every valuation profile $v$ there are randomized deviations $b_i'$, one for each agent $i$, each depending only on $v$ and on agent $i$'s own bid $b_i$, such that for every bid profile $b$
--
--   $$
--   \sum_{i\in N}\mathbf E\bigl[u_i((b_i',b_{-i}),v_i)\bigr]\ \ge\ \lambda\cdot\max_{x\in F}\sum_{i\in N}v_i(x)\;-\;\mu\cdot\sum_{i\in N}\mathbf E\bigl[p_i(b)\bigr].
--   $$
--
--   Here the expectation on the left is over the randomization of $b_i'$ (and of the mechanism); valuation and bid profiles are drawn from the weight classes. Smoothness yields Price of Anarchy bounds of $\max(1,\mu)/\lambda$ for many equilibrium notions.
--
--   **Formalization Note** The dependence of $b_i'$ is encoded by quantifying "for every $v$ there exist maps $b_i\mapsto b_i'$ such that for every $b$". The expected utility of each deviation must be integrable. The maximum over $F$ is replaced by "for every $x\in F$", which is equivalent when the maximum exists.
-- source:
--   Dütting, Kesselheim, Tardos, Algorithms as Mechanisms: The Price of Anarchy of Relax-and-Round, arXiv:1511.09208v1, §2, p.7

import Mathlib
import Definitions.Def_RelaxRoundPoA_Mechanism
import Definitions.Def_RelaxRoundPoA_IsProfile
import Definitions.Def_RelaxRoundPoA_utility
import Definitions.Def_RelaxRoundPoA_RandomBid

open MeasureTheory NNReal

namespace RelaxRoundPoA

/-- **(λ, µ)-smooth mechanism** (Syrgkanis–Tardos).
Dütting, Kesselheim, Tardos, arXiv:1511.09208v1, §2, p.7: "A mechanism is (λ, µ)-smooth for
`λ, µ ≥ 0` if for all valuation profiles `v` and all bid profiles `b` there exists a possibly
randomized strategy `b'_i` for every agent `i` that may depend on the valuation profile `v` of all
agents and the bid `b_i` of that agent such that
`∑_{i∈N} E[u_i((b'_i, b_{−i}), v_i)] ≥ λ · max_{x∈Ω} ∑_{i∈N} v_i(x) − µ · ∑_{i∈N} E[p_i(b)]`."

`IsSmooth Val Feas M lam mu` says `0 ≤ lam`, `0 ≤ mu`, and for every valuation profile `v` drawn
from `Val` there are deviation maps `σ i : (Ω' → ℝ≥0) → RandomBid Val i` (agent `i`'s randomized
deviation as a function of its own bid) such that for every bid profile `b` drawn from `Val`, with
`(A_i, P_i, X_i) = σ i (b i)`:
1. each `a ↦ u_i((X_i a, b_{−i}), v_i)` is `P_i`-integrable, and
2. for every feasible `x ∈ Feas`,
   `lam · ∑_i v_i(x) − mu · ∑_i E[p_i(b)] ≤ ∑_i ∫ u_i((X_i a, b_{−i}), v_i) dP_i(a)`.

**Formalization Note** The quantifier order `∀ v ∃ σ ∀ b`, with `σ i` a function of `b i`, is the
printed dependence of `b'_i` on `v` and `b_i` only. `max_{x∈Ω}` is replaced by "for every
`x ∈ Feas`", which is equivalent when the maximum exists and never uses a junk supremum. `Feas` is
the mechanism's outcome set: `Set.univ` for the relaxation, `Ω` for the original problem. -/
def IsSmooth {N : Type*} [Fintype N] [DecidableEq N] {Ω' : Type*} [MeasurableSpace Ω']
    (Val : N → Set (Ω' → ℝ≥0)) (Feas : Set Ω') (M : Mechanism N Ω') (lam mu : ℝ) : Prop :=
  0 ≤ lam ∧ 0 ≤ mu ∧
    ∀ v : N → Ω' → ℝ≥0, IsProfile Val v →
      ∃ σ : (i : N) → (Ω' → ℝ≥0) → RandomBid Val i,
        ∀ b : N → Ω' → ℝ≥0, IsProfile Val b →
          (∀ i, Integrable
              (fun a => utility M i (Function.update b i ((σ i (b i)).X a)) (v i)) (σ i (b i)).P) ∧
          ∀ x ∈ Feas,
            lam * ∑ i, (v i x : ℝ) - mu * ∑ i, M.expPay b i ≤
              ∑ i, ∫ a, utility M i (Function.update b i ((σ i (b i)).X a)) (v i) ∂(σ i (b i)).P

end RelaxRoundPoA


