-- Prove2me | Definitions.Def_DissolveCDF_epsX
-- name    : DissolveCDF_epsX
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T21:34:15.55852+00:00
-- url     : https://prove2.me/theorems/510af4b6-d41e-40d0-abe7-6a0ba8e54b7e
-- title:
--   §2.3 — the radius $\varepsilon_x$ of $\Omega_x$
-- statement:
--   For $x\in\mathcal M$,
--
--   $$
--   \varepsilon_x:=\min\Big\{\frac{\rho_x}{2},\ \frac{\sigma_{x,c}}{32L_{x,c}(M_{x,A}+1)},\ \frac{\sigma_{x,c}^2}{8L_{x,b}M_{x,c}}\Big\},
--   $$
--
--   and $\Omega_x:=\{y\in\mathbb R^n:\|y-x\|\le\varepsilon_x\}$. The paper notes that $\varepsilon_x>0$ for every $x\in\mathcal M$. Lemmas 3.1–3.3 and Theorem 3.10 hold on $\Omega_x$.
--
--   **Formalization Note** The minimum is encoded as the largest $\varepsilon\in(0,\rho_x/2]$ with $32L_{x,c}(M_{x,A}+1)\varepsilon\le\sigma_{x,c}$ and $8L_{x,b}M_{x,c}\varepsilon\le\sigma_{x,c}^2$. For $x\in\mathcal M$ this is the printed minimum with the convention that a quotient with zero denominator is $+\infty$ (e.g. $L_{x,c}=0$ for affine $c$). Lean's division would give $\sigma/0=0$ and collapse $\Omega_x$ to $\{x\}$. In Lean, $\Omega_x$ is `Metric.closedBall x (epsX c A x)`.
-- source:
--   Xiao, Liu & Toh, Dissolving Constraints for Riemannian Optimization, arXiv:2203.10319v3, §2.3, p.7 (and p.8: ε_x > 0)

import Mathlib
import Definitions.Def_DissolveCDF_rhoX
import Definitions.Def_DissolveCDF_sigmaXC
import Definitions.Def_DissolveCDF_MXc
import Definitions.Def_DissolveCDF_MXA
import Definitions.Def_DissolveCDF_LXc
import Definitions.Def_DissolveCDF_LXb

namespace DissolveCDF

/-- Xiao, Liu & Toh, *Dissolving Constraints for Riemannian Optimization*, arXiv:2203.10319v3, §2.3 (p.7):
`ε_x := min { ρ_x/2, σ_{x,c} / (32 L_{x,c}(M_{x,A} + 1)), σ_{x,c}² / (8 L_{x,b} M_{x,c}) }`.
The paper's sets are `Ω_x := {y : ‖y − x‖ ≤ ε_x}` (here `Metric.closedBall x (epsX c A x)`).

**Formalization Note** The minimum is encoded as the largest `ε ∈ (0, ρ_x/2]` with
`32 L_{x,c}(M_{x,A} + 1) ε ≤ σ_{x,c}` and `8 L_{x,b} M_{x,c} ε ≤ σ_{x,c}²` (an `sSup`). For
`x ∈ M` (where `σ_{x,c} > 0`) this is exactly the printed minimum with the convention that a
quotient with zero denominator is `+∞`, i.e. a term whose denominator vanishes (`L_{x,c} = 0`, e.g.
affine `c`, or `L_{x,b} = 0`) drops out. Writing the printed minimum with Lean's division would
give `σ/0 = 0` and collapse `Ω_x` to `{x}`. -/
noncomputable def epsX {n p : ℕ} (c : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin p))
    (A : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)) (x : EuclideanSpace ℝ (Fin n)) : ℝ :=
  sSup {ε : ℝ | 0 < ε ∧ ε ≤ rhoX c x / 2 ∧
    32 * LXc c x * (MXA c A x + 1) * ε ≤ sigmaXC c x ∧
    8 * LXb c A x * MXc c x * ε ≤ sigmaXC c x ^ 2}

end DissolveCDF


