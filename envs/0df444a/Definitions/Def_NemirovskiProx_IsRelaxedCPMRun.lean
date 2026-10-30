-- Prove2me | Definitions.Def_NemirovskiProx_IsRelaxedCPMRun
-- name    : NemirovskiProx_IsRelaxedCPMRun
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-30T01:46:23.952118+00:00
-- url     : https://prove2.me/theorems/d6981d40-5615-415c-91ce-4b13398cd717
-- title:
--   $N$ non-terminating steps of the relaxed conceptual prox-method
-- statement:
--   The **relaxed conceptual prox-method** starts at $z_0\in Z$. At step $t=1,2,\dots$ it checks whether $P_{z_{t-1}}(F(z_{t-1}))=z_{t-1}$ (2.8); if so it terminates. Otherwise it chooses $\gamma_t>0$ and $w_t\in Z$ such that
--   $$\langle w_t-P_{z_{t-1}}(\gamma_tF(w_t)),\gamma_tF(w_t)\rangle+\omega(z_{t-1})+\langle\omega'(z_{t-1}),P_{z_{t-1}}(\gamma_tF(w_t))-z_{t-1}\rangle-\omega(P_{z_{t-1}}(\gamma_tF(w_t)))\le\epsilon_t \tag{2.11}$$
--   and sets $z_t=P_{z_{t-1}}(\gamma_tF(w_t))$.
--
--   The predicate says that $(z_t)$, $(w_t)$, $(\gamma_t)$ form a run of this method that does not terminate in the course of $N$ steps, with tolerances $\epsilon_t$.
--
--   **Formalization Note** The paper's step $t$ is index $t+1$ for $t<N$; the termination test uses $F$, not $\gamma_tF$, and, the prox point being unique, is "$z_{t-1}$ is the prox point of $F(z_{t-1})$ at $z_{t-1}$".
-- source:
--   Nemirovski, Prox-Method with Rate of Convergence O(1/t) for Variational Inequalities with Lipschitz Continuous Monotone Operators and Smooth Convex-Concave Saddle Point Problems, SIAM J. Optim. 15(1) (2004), 229–251, doi:10.1137/S1052623403425629, CPM, §2.3, (2.8)–(2.9), p. 233; Proposition 2.2, (2.11), p. 234

import Mathlib
import Definitions.Def_NemirovskiProx_IsProxPointOn
import Definitions.Def_NemirovskiProx_stepGap

open scoped InnerProductSpace

namespace NemirovskiProx

/-- **`n` non-terminating steps of the relaxed conceptual prox-method.**
Nemirovski, *Prox-Method with Rate of Convergence O(1/t) for Variational Inequalities with
Lipschitz Continuous Monotone Operators and Smooth Convex-Concave Saddle Point Problems*,
SIAM J. Optim. 15(1) (2004), CPM, §2.3, p. 233: "Initialization. Choose starting point z0 ∈ Z. Step t, t = 1, 2, . . . :
Given zt−1, check whether Pzt−1(F(zt−1)) = zt−1. (2.8) If it is the case, claim that zt−1 is the
solution to the variational inequality associated with Z, F and terminate. Otherwise choose
γt > 0 and a point wt ∈ Z such that (2.9) [...] Set zt = Pzt−1(γtF(wt))"; Proposition 2.2,
p. 234: the relaxed version, "where condition (2.9) is weakened to (2.11)", and (ii) "does not
terminate in the course of N steps".

`IsRelaxedCPMRun Z F ω ω' γs εs z w n` says: `z 0 ∈ Z`, and for each step `t + 1 ≤ n` the
point `z t` fails the termination test (2.8), `γs (t+1) > 0`, `w (t+1) ∈ Z`,
`z (t+1) = P_{z t}(γs (t+1) F(w (t+1)))`, and (2.11) holds with `ϵ_{t+1} = εs (t+1)`.

**Formalization Note.** Step `t + 1` of the paper is written `∀ t < n`, which avoids natural
subtraction. (2.8) is `P_{z}(F(z)) = z`, with `F`, not `γF`; since the prox point is unique it
is "`z` is a prox point of `F z` at `z`". -/
def IsRelaxedCPMRun {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (Z : Set E) (F : E → E) (ω : E → ℝ) (ω' : E → E) (γs εs : ℕ → ℝ) (z w : ℕ → E)
    (n : ℕ) : Prop :=
  z 0 ∈ Z ∧ ∀ t < n,
    ¬ IsProxPointOn Z ω ω' (z t) (F (z t)) (z t) ∧
    0 < γs (t + 1) ∧ w (t + 1) ∈ Z ∧
    IsProxPointOn Z ω ω' (z t) (γs (t + 1) • F (w (t + 1))) (z (t + 1)) ∧
    stepGap ω ω' (z t) (w (t + 1)) (z (t + 1)) (γs (t + 1) • F (w (t + 1))) ≤ εs (t + 1)

end NemirovskiProx


