-- Prove2me | Definitions.Def_FBMStrongSim_RecordBreak_Supplement_YoungConstants
-- name    : FBMStrongSim_RecordBreak_Supplement_YoungConstants
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-23T22:29:02.827599+00:00
-- url     : https://prove2.me/theorems/2db5dfcf-dc69-42e4-9603-c9f298e7d107
-- title:
--   Young–Euler constants and the corrected local variant of Lemma 5.8
-- statement:
--   Let $d,h\ge1$, $1/2<\alpha\le1$, $C>0$, and let $F_0,F_1>0$, $F_2\ge0$ be the coefficient envelopes. The file computes the constants of pp. 30–31, rather than quantifying over unrelated constants. In particular,
--   $$K(2\alpha)=1+\sum_{m\ge1}m^{-2\alpha},\quad G_1^*=2h\lceil(2dhCK(2\alpha)F_1)^{1/\alpha}\rceil^{1-\alpha}F_0C,\quad G_2^*=dhK(2\alpha)F_1CG_1^*.$$
--   The printed constants used by Lemma 5.9 and Theorem 5.5 are:
--   $$L=\frac{4(hC)^2F_1F_0}{1-2^{1-2\alpha}},\quad\omega=(hF_0C/L)^{1/\alpha},\quad G_1=(L+hF_0C)(1+\omega^{-1}),$$
--   $$G_2=\max\{(2\omega^{-\alpha}+\omega^{-1-\alpha})(L+hF_0C),L\}.$$
--   The remaining definitions are
--   $$\zeta=hK(2\alpha)C[dF_1+d^2F_2(G_1^*+G_1)],\quad\upsilon=C[d^2hK(2\alpha)F_2(G_1^*+G_1)+dF_1],$$
--   $$\Gamma_1=2G_2^*,\quad\Upsilon_1=\Gamma_1/(4\zeta),\quad\Gamma_k=2(G_2^*+\upsilon\Upsilon_{k-1}),\quad\Upsilon_k=\Gamma_k/(4\zeta)+\Upsilon_{k-1}.$$
--   Finally $G=\Upsilon_{\lceil(4\zeta)^{1/\alpha}\rceil}+G_1^*$. The unused index zero is set to $(\Gamma_0,\Upsilon_0)=(0,0)$; the index used by the theorem is positive. The file also defines correctedL=dL and correctedG1,correctedG2 by substituting correctedL in the local formulas, solely for the corrected Lemma 5.8. DISPROOF.md gives the analytic counterexample and Appendix C.2 evidence. This repair is not propagated into the printed constants of the distinct Lemma 5.9 and Theorem 5.5 targets. Zero derivative norms are covered by positive upper envelopes, as the printed formula otherwise has undefined divisions.
--
--   Differences from the source:
--   - correction: formulas evaluated at exact norms, including zero derivative norms → the same formulas evaluated at the explicit positive F0,F1 and nonnegative F2 envelopes; reason: DISPROOF.md refutes the zero-derivative formula for G1*; no vector field is excluded
--   - correction: the printed L without d under the entrywise derivative reading → additional correctedL=d·L and its associated local constants for Lemma 5.8 only; reason: the sine-field counterexample and Appendix C.2 justify the dimension factor; the independent Lemma 5.9 and Theorem 5.5 targets keep their printed constants
--   - encoding: positive-index K series, integer ceilings and recurrence indexed from 1 → a series reindexed by q+1, natural ceilings on positive arguments, and an unused zero recurrence value; reason: α>1/2 ensures summability and positive dimensions and envelopes ensure the ceiling used by the theorem is at least one
-- source:
--   Chen, Dong & Ni, ε-Strong simulation of fractional Brownian motion and related stochastic differential equations, arXiv:1902.07824v1, pp. 30–31, constants preceding Theorem 5.5 and (5.6); Appendix C.2, pp. 44–45

import Mathlib

namespace FBMStrongSim.RecordBreak.Supplement

/-- K(2α) of the Young–Loève estimate; converges for α>1/2. -/
noncomputable def youngK (alpha : ℝ) : ℝ := 1 + ∑' q : ℕ, ((q + 1 : ℕ) : ℝ) ^ (-2 * alpha)

noncomputable def Gstar1 (d h : ℕ) (alpha C F0 F1 : ℝ) : ℝ :=
  2 * h * (⌈(2 * d * h * C * youngK alpha * F1) ^ (1 / alpha)⌉₊ : ℝ) ^ (1 - alpha) * F0 * C

noncomputable def Gstar2 (d h : ℕ) (alpha C F0 F1 : ℝ) : ℝ :=
  d * h * youngK alpha * F1 * C * Gstar1 d h alpha C F0 F1

/-- The printed constant L of p.30. The uniform-rate target retains this formula. -/
noncomputable def localL (d h : ℕ) (alpha C F0 F1 : ℝ) : ℝ :=
  4 / (1 - (2 : ℝ) ^ (1 - 2 * alpha)) * ((h : ℝ) * C) ^ 2 * F1 * F0

noncomputable def localOmega (d h : ℕ) (alpha C F0 F1 : ℝ) : ℝ :=
  ((h : ℝ) * F0 * C / localL d h alpha C F0 F1) ^ (1 / alpha)

noncomputable def G1 (d h : ℕ) (alpha C F0 F1 : ℝ) : ℝ :=
  (localL d h alpha C F0 F1 + h * F0 * C) * (1 + (localOmega d h alpha C F0 F1)⁻¹)

noncomputable def G2 (d h : ℕ) (alpha C F0 F1 : ℝ) : ℝ :=
  max ((2 * localOmega d h alpha C F0 F1 ^ (-alpha) +
    localOmega d h alpha C F0 F1 ^ (-1 - alpha)) *
    (localL d h alpha C F0 F1 + h * F0 * C)) (localL d h alpha C F0 F1)

/-- Corrected entrywise constants for Lemma5.8 only; see DISPROOF.md. -/
noncomputable def correctedL (d h : ℕ) (alpha C F0 F1 : ℝ) : ℝ :=
  4 / (1 - (2 : ℝ) ^ (1 - 2 * alpha)) * ((h : ℝ) * C) ^ 2 * d * F1 * F0

noncomputable def correctedOmega (d h : ℕ) (alpha C F0 F1 : ℝ) : ℝ :=
  ((h : ℝ) * F0 * C / correctedL d h alpha C F0 F1) ^ (1 / alpha)

noncomputable def correctedG1 (d h : ℕ) (alpha C F0 F1 : ℝ) : ℝ :=
  (correctedL d h alpha C F0 F1 + h * F0 * C) * (1 + (correctedOmega d h alpha C F0 F1)⁻¹)

noncomputable def correctedG2 (d h : ℕ) (alpha C F0 F1 : ℝ) : ℝ :=
  max ((2 * correctedOmega d h alpha C F0 F1 ^ (-alpha) +
    correctedOmega d h alpha C F0 F1 ^ (-1 - alpha)) *
    (correctedL d h alpha C F0 F1 + h * F0 * C)) (correctedL d h alpha C F0 F1)

noncomputable def zeta (d h : ℕ) (alpha C F0 F1 F2 : ℝ) : ℝ :=
  h * youngK alpha * C * (d * F1 + (d : ℝ) ^ 2 * F2 *
    (Gstar1 d h alpha C F0 F1 + G1 d h alpha C F0 F1))

noncomputable def upsilon (d h : ℕ) (alpha C F0 F1 F2 : ℝ) : ℝ :=
  C * ((d : ℝ) ^ 2 * h * youngK alpha * F2 *
    (Gstar1 d h alpha C F0 F1 + G1 d h alpha C F0 F1) + d * F1)

/-- (Γ_k, Υ_k), with the unused index zero set to (0,0). -/
noncomputable def errorConstants (d h : ℕ) (alpha C F0 F1 F2 : ℝ) : ℕ → ℝ × ℝ
  | 0 => (0, 0)
  | 1 => let g := 2 * Gstar2 d h alpha C F0 F1
         (g, g / (4 * zeta d h alpha C F0 F1 F2))
  | k + 2 =>
      let prev := errorConstants d h alpha C F0 F1 F2 (k + 1)
      let g := 2 * (Gstar2 d h alpha C F0 F1 + upsilon d h alpha C F0 F1 F2 * prev.2)
      (g, g / (4 * zeta d h alpha C F0 F1 F2) + prev.2)

noncomputable def eulerConstant (d h : ℕ) (alpha C F0 F1 F2 : ℝ) : ℝ :=
  (errorConstants d h alpha C F0 F1 F2
    ⌈(4 * zeta d h alpha C F0 F1 F2) ^ (1 / alpha)⌉₊).2 + Gstar1 d h alpha C F0 F1

end FBMStrongSim.RecordBreak.Supplement


