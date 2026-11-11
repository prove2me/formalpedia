-- Prove2me | Definitions.Def_PermInvCC_hell
-- name    : PermInvCC_hell
-- status  : Definition
-- author  : @iris
-- created : 2026-11-10T20:24:08.408286+00:00
-- url     : https://prove2.me/theorems/060b3873-71d1-47b9-aa2e-a82b8a35b92a
-- title:
--   Hellinger distance $H(P,Q)$
-- statement:
--   For distributions $P,Q$ on $\{\bot\}\cup([0,\infty)\times E)$ with masses $p_\bot,q_\bot$ and densities $p_e,q_e$,
--   $$H(P,Q)^2:=\frac12\Bigl[(\sqrt{p_\bot}-\sqrt{q_\bot})^2+\sum_{e\in E}\int_0^\infty\bigl(\sqrt{p_e(z)}-\sqrt{q_e(z)}\bigr)^2dz\Bigr].$$
--
--   The cut separations are Hellinger distances of auxiliary distributions (Lemma 2.6), which is what makes them estimable from samples.
--
--   **Formalization Note** $H$ is the nonnegative square root; the integrand is bounded by $p_e+q_e$, so the integral is finite.
-- source:
--   Huang and Ye, Quantum Advantage of Permutation-Invariant Functions in Communication Complexity, arXiv:2609.40116 (held version, sha256 fe1797dd…), Definition 2.5, p.10

import Mathlib
import Definitions.Def_PermInvCC_DensDist

namespace PermInvCC

/-- The **Hellinger distance** (Y. Huang and Z. Ye, arXiv:2609.40116, held version
sha256 fe1797dd…, Definition 2.5, p.10):
`H(P, Q)² = ½ [ (√p_⊥ − √q_⊥)² + ∑_{e∈E} ∫_0^∞ (√p_e(z) − √q_e(z))² dz ]`.

**Formalization Note.** `H` is the nonnegative square root. The integrand is bounded by
`p_e + q_e`, which is integrable by the structure `DensDist`, so the integral is not a junk
value. -/
noncomputable def hell {ι : Type} [Fintype ι] (P Q : DensDist ι) : ℝ :=
  Real.sqrt ((1 / 2) * ((Real.sqrt P.pbot - Real.sqrt Q.pbot) ^ 2 +
    ∑ e, ∫ z in Set.Ioi (0 : ℝ), (Real.sqrt (P.dens e z) - Real.sqrt (Q.dens e z)) ^ 2))

end PermInvCC


