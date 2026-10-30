-- Prove2me | Definitions.Def_NemirovskiProx_IsBasicImplRun
-- name    : NemirovskiProx_IsBasicImplRun
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-30T01:46:48.624699+00:00
-- url     : https://prove2.me/theorems/b2f30110-7436-4a26-813a-20297b6002a8
-- title:
--   $N$ steps of the basic implementation, (3.2)–(3.4)
-- statement:
--   The **basic implementation** of step $t$ of the prox-method, applied at a point $z_{t-1}\in Z$ that does not satisfy (2.8), uses the constant stepsize $\gamma$ (in (3.2), $\gamma=\alpha/(\sqrt2L)$) and builds, starting with $w_{t,0}=z_{t-1}$, the inner iterates
--   $$w_{t,s}=P_{z_{t-1}}(\gamma F(w_{t,s-1})),\qquad s=1,2,\dots \tag{3.3}$$
--   until the condition
--   $$\langle\gamma F(w_{t,s-1}),w_{t,s-1}-w_{t,s}\rangle+\omega(z_{t-1})+\langle\omega'(z_{t-1}),w_{t,s}-z_{t-1}\rangle-\omega(w_{t,s})\le0 \tag{3.4}$$
--   is met. With $s_t$ the first such $s$, it sets $w_t=w_{t,s_t-1}$ and $z_t=w_{t,s_t}$.
--
--   The predicate says that $(z_t)$, $(w_t)$, $(s_t)$ form a run of $N$ such steps from $z_0\in Z$, none of which terminates by (2.8).
--
--   **Formalization Note** $\gamma$ is a parameter; the theorems substitute $\alpha/(\sqrt2L)$. "Denote by $s_t$ the corresponding value of $s$" is encoded as: (3.4) holds at $s_t\ge1$ and fails at every $1\le s<s_t$.
-- source:
--   Nemirovski, Prox-Method with Rate of Convergence O(1/t) for Variational Inequalities with Lipschitz Continuous Monotone Operators and Smooth Convex-Concave Saddle Point Problems, SIAM J. Optim. 15(1) (2004), 229–251, doi:10.1137/S1052623403425629, §3, basic implementation, (3.2)–(3.4), p. 237

import Mathlib
import Definitions.Def_NemirovskiProx_IsProxPointOn
import Definitions.Def_NemirovskiProx_stepGap

open scoped InnerProductSpace

namespace NemirovskiProx

/-- **`n` non-terminating steps of the basic implementation with stepsize `γ`.**
Nemirovski, *Prox-Method with Rate of Convergence O(1/t) for Variational Inequalities with
Lipschitz Continuous Monotone Operators and Smooth Convex-Concave Saddle Point Problems*,
SIAM J. Optim. 15(1) (2004), §3, (3.2)–(3.4), p. 237: "Given a point zt−1 ∈ Z which does not satisfy (2.8), set
γt = γ ≡ α/(√2L); build, starting with wt,0 ≡ zt−1, the iterates wt,s = Pzt−1(γF(wt,s−1)),
s = 1, 2, . . . , until the condition ⟨γF(wt,s−1), wt,s−1 − wt,s⟩ + ω(zt−1) + ⟨ω′(zt−1),
wt,s − zt−1⟩ − ω(wt,s) ≤ 0 is met. Denote by st the corresponding value of s and set
wt = wt,st−1 [⇒ zt = wt,st]."

`IsBasicImplRun Z F ω ω' γ z w s n` says: `z 0 ∈ Z`, and for each step `t + 1 ≤ n` the point
`z t` fails (2.8), and there are inner iterates `v 0 = z t`, `v (j+1) = P_{z t}(γ F(v j))`
for `j < s (t+1)`, such that `s (t+1) ≥ 1` is the **first** `s` at which (3.4) holds, and
`w (t+1) = v (s (t+1) − 1)`, `z (t+1) = v (s (t+1))`.

**Formalization Note.** `γ` is a parameter; the theorems pass `α / (√2 L)` of (3.2). The
minimality clause encodes "the corresponding value of s": `s_t` is the first inner iteration
at which (3.4) is met. Natural subtraction occurs only as `s (t+1) − 1` with `s (t+1) ≥ 1`
and `j − 1` with `j ≥ 1`. -/
def IsBasicImplRun {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (Z : Set E) (F : E → E) (ω : E → ℝ) (ω' : E → E) (γ : ℝ) (z w : ℕ → E) (s : ℕ → ℕ)
    (n : ℕ) : Prop :=
  z 0 ∈ Z ∧ ∀ t < n,
    ¬ IsProxPointOn Z ω ω' (z t) (F (z t)) (z t) ∧
    ∃ v : ℕ → E, v 0 = z t ∧
      (∀ j < s (t + 1), IsProxPointOn Z ω ω' (z t) (γ • F (v j)) (v (j + 1))) ∧
      1 ≤ s (t + 1) ∧
      stepGap ω ω' (z t) (v (s (t + 1) - 1)) (v (s (t + 1))) (γ • F (v (s (t + 1) - 1))) ≤ 0 ∧
      (∀ j, 1 ≤ j → j < s (t + 1) →
        0 < stepGap ω ω' (z t) (v (j - 1)) (v j) (γ • F (v (j - 1)))) ∧
      w (t + 1) = v (s (t + 1) - 1) ∧ z (t + 1) = v (s (t + 1))

end NemirovskiProx


