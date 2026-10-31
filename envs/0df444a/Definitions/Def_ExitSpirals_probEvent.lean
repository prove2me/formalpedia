-- Prove2me | Definitions.Def_ExitSpirals_probEvent
-- name    : ExitSpirals_probEvent
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T22:02:12.554611+00:00
-- url     : https://prove2.me/theorems/e996d67c-42b8-46bc-9a4e-d6c667e0e6ee
-- title:
--   Random coupled network: uniform simple digraphs with given degrees and Bernoulli shocks
-- statement:
--   For population size $n$, let $G(n,d^+,d^-)$ be the set of loopless simple digraphs on $\{1,\dots,n\}$ in which agent $i$ has out-degree $d^+_i$ and in-degree $d^-_i$. The random coupled network draws
--
--   1. $G_R$ uniformly from $G(n,d^+_{R,n},d^-_{R,n})$,
--   2. $G_C$ uniformly from $G(n,d^+_{C,n},d^-_{C,n})$,
--   3. a shocked set $W$ containing each agent independently with probability $1-x$,
--
--   all three independently. `expectation dR dC x n X` is $\mathbb E[X(G_R,G_C,W)]$, `probEvent` is the probability of an event, and the **expected activity** is
--   $$\hat{\mathcal A}_n(x)=\mathbb E\big[\mathcal A(G_R,G_C,W)\big],$$
--   the analyst's ex-ante expected activity of §3.1 at population size $n$.
--
--   **Formalization Note** The law is written as an explicit finite sum with weights $|G_R|^{-1}|G_C|^{-1}\prod_i(1-x\text{ if }i\in W\text{, else }x)$; if a degree set is empty its weight is $0$. Shocks are meaningful for $0\le x\le1$, and the theorems restrict $x$ to $[0,1]$.
-- source:
--   Aymanns, Georg, Golub, Exit Spirals in Coupled Networked Markets, SSRN 2881814 (preprint, sha256 12000f11…6c84d2), §3.1, p.15 (Â = E[A]); Assumption 4.2 and (4), p.22 (shock of size 1 − x); §4.3.1, pp.24–25 and Assumption 4.4, p.25 (uniform independent draws); Appendix A.3, pp.47–48

import Mathlib
import Definitions.Def_ExitSpirals_Network
import Definitions.Def_ExitSpirals_activity
import Definitions.Def_ExitSpirals_WellBehaved

namespace ExitSpirals

/-- **The set `G(n, d⁺, d⁻)` of simple graphs with given degrees** (p.25, Appendix A.3, p.47):
the loopless networks on `Fin n` in which agent `i` has out-degree `dOut i` and in-degree `dIn i`.
Aymanns, Georg, Golub, *Exit Spirals in Coupled Networked Markets*, SSRN 2881814. -/
noncomputable def graphsWith {n : ℕ} (dOut dIn : Fin n → ℕ) : Finset (Network n) := by
  classical
  exact Finset.univ.filter fun E : Network n =>
    IsLoopless E ∧ (∀ i, outDeg E i = dOut i) ∧ (∀ i, inDeg E i = dIn i)

/-- Probability of the shocked set `W` when each agent is shocked independently with probability
`1 − x` (Assumption 4.2, p.22: "a fraction 1 − x of agents, drawn uniformly at random, will
receive a cost draw that exceeds the maximum benefit"; "The agents' costs are i.i.d"). -/
noncomputable def shockWeight {n : ℕ} (x : ℝ) (W : Finset (Fin n)) : ℝ :=
  ∏ i : Fin n, if i ∈ W then 1 - x else x

/-- **Expectation over the random coupled network and the shock**, at population size `n`.
Aymanns, Georg, Golub, *Exit Spirals in Coupled Networked Markets*, SSRN 2881814, p.25: "A random
network G_µ … is then a draw from G_µ(n, d⁺_µ, d⁻_µ) uniformly at random"; Assumption 4.4, p.25:
"The random networks G_R and G_C are independent realizations"; p.48: "The networks G_{R,n} and
G_{C,n} are independent, uniform draws"; Assumption 4.2, p.22 (i.i.d. costs, shock of size 1 − x).

`expectation dR dC x n X` is the expectation of `X(G_R, G_C, W)` where `G_R` is uniform on
`G(n, d⁺_{R,n}, d⁻_{R,n})`, `G_C` is uniform on `G(n, d⁺_{C,n}, d⁻_{C,n})`, and `W` contains each
agent independently with probability `1 − x`, all three independent.

**Formalization Note.** The law is written as an explicit finite sum with weights
`|G_R|⁻¹ |G_C|⁻¹ ∏_i (1 − x or x)`. If a degree set is empty (an unrealizable degree sequence),
the weight is `0` (Lean's `0⁻¹ = 0`). The shock probability is meaningful for `0 ≤ x ≤ 1`; the
theorems restrict `x` to `[0, 1]`. -/
noncomputable def expectation (dR dC : DegreeTuple) (x : ℝ) (n : ℕ)
    (X : Network n → Network n → Finset (Fin n) → ℝ) : ℝ :=
  ∑ ER ∈ graphsWith (dR.dOut n) (dR.dIn n), ∑ EC ∈ graphsWith (dC.dOut n) (dC.dIn n),
    ∑ W : Finset (Fin n),
      ((graphsWith (dR.dOut n) (dR.dIn n)).card : ℝ)⁻¹ *
      ((graphsWith (dC.dOut n) (dC.dIn n)).card : ℝ)⁻¹ * shockWeight x W * X ER EC W

/-- Probability of an event about `(G_R, G_C, W)` at population size `n` (the expectation of its
indicator). -/
noncomputable def probEvent (dR dC : DegreeTuple) (x : ℝ) (n : ℕ)
    (P : Network n → Network n → Finset (Fin n) → Prop) : ℝ := by
  classical
  exact expectation dR dC x n fun ER EC W => if P ER EC W then 1 else 0

/-- **Expected activity** `Â = E[A((G_µ)_µ)]` (§3.1, p.15) at population size `n`: the expectation
of `activity G_R G_C W`, the fraction of agents active in the maximal equilibrium. -/
noncomputable def expectedActivity (dR dC : DegreeTuple) (x : ℝ) (n : ℕ) : ℝ :=
  expectation dR dC x n fun ER EC W => activity ER EC W

end ExitSpirals


