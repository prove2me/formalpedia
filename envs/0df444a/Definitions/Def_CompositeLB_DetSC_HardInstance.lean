-- Prove2me | Definitions.Def_CompositeLB_DetSC_HardInstance
-- name    : CompositeLB_DetSC_HardInstance
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-09T07:24:23.986665+00:00
-- url     : https://prove2.me/theorems/26e92756-509b-49c7-bf93-38c44c52474e
-- title:
--   Appendix B.4, pp. 16–17 — hard components, Q, q, and the candidate minimizer
-- statement:
--   Given directions $v_0,\ldots,v_k$, indicators $\delta_{i,r}$, and real parameters $\lambda,C,\zeta$, Appendix B.4 defines
--
--   $$f_i(x)=\frac{1-\lambda}{8}\left[\delta_{i,1}(\langle x,v_0\rangle^2-2C\langle x,v_0\rangle)+\delta_{i,k}\zeta\langle x,v_k\rangle^2+\sum_{r=1}^k\delta_{i,r}\langle x,v_{r-1}-v_r\rangle^2\right]+\frac\lambda2\lVert x\rVert^2.$$
--
--   Their average is $F$. The paper sets $Q=(\lfloor m/2\rfloor/m)(1/\lambda-1)+1$, $q=(\sqrt Q-1)/(\sqrt Q+1)$, and proposes $x^*=C\sum_{r=0}^kq^{r+1}v_r$. These are the common objects of the appendix's algebraic milestones.
--
--   **Formalization Note** The Lean parameter lam denotes $\lambda$. Natural division m / 2 is $\lfloor m/2\rfloor$; the sum uses $r\ge1$, so $r-1$ is ordinary subtraction. Positivity, orthonormality, and indicator conditions belong to the theorems that use these expressions.
-- source:
--   Woodworth & Srebro, arXiv:1605.08003v3, App. B.4, pp. 16–17, component formula and displays defining Q, q and x*

import Mathlib
import Definitions.Def_CompositeLB_DetSmooth_Model

namespace CompositeLB.DetSC

/-- Appendix B.4's component function at smoothness normalization γ = 1.
The parameter `lam` is the paper's λ (`λ` is a Lean keyword); `delta r` is δ_{i,r}
for one fixed component `i`, and `v r` are the directions v_r. -/
noncomputable def hardF {d : ℕ} (lam C zeta : ℝ) (k : ℕ)
    (v : ℕ → CompositeLB.DetLip.E d) (delta : ℕ → ℝ) (x : CompositeLB.DetLip.E d) : ℝ :=
  (1 - lam) / 8 *
    (delta 1 * ((inner ℝ x (v 0)) ^ 2 - 2 * C * inner ℝ x (v 0)) +
      delta k * zeta * (inner ℝ x (v k)) ^ 2 +
      ∑ r ∈ Finset.Icc 1 k, delta r * (inner ℝ x (v (r - 1) - v r)) ^ 2) +
    lam / 2 * ‖x‖ ^ 2

/-- The quantity `Q` in Appendix B.4; `m / 2` is natural division, hence `⌊m/2⌋`. -/
noncomputable def bigQ (m : ℕ) (lam : ℝ) : ℝ :=
  (((m / 2 : ℕ) : ℝ) / (m : ℝ)) * (1 / lam - 1) + 1

/-- The contraction factor `q = (√Q - 1)/(√Q + 1)` in Appendix B.4. -/
noncomputable def qq (m : ℕ) (lam : ℝ) : ℝ :=
  (Real.sqrt (bigQ m lam) - 1) / (Real.sqrt (bigQ m lam) + 1)

/-- Appendix B.4's full objective, averaged over the components. -/
noncomputable def hardAvg {m d : ℕ} (lam C zeta : ℝ) (k : ℕ)
    (v : ℕ → CompositeLB.DetLip.E d) (delta : Fin m → ℕ → ℝ) (x : CompositeLB.DetLip.E d) : ℝ :=
  CompositeLB.DetLip.avgF (fun i => hardF lam C zeta k v (delta i)) x

/-- The candidate minimizer `x* = C ∑_{r=0}^k q^(r+1) v_r`. -/
noncomputable def hardXstar {d : ℕ} (m : ℕ) (lam C : ℝ) (k : ℕ)
    (v : ℕ → CompositeLB.DetLip.E d) : CompositeLB.DetLip.E d :=
  C • ∑ r ∈ Finset.range (k + 1), (qq m lam ^ (r + 1)) • v r

end CompositeLB.DetSC


