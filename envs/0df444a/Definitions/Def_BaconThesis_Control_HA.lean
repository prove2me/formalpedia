-- Prove2me | Definitions.Def_BaconThesis_Control_HA
-- name    : BaconThesis_Control_HA
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T15:58:10.520906+00:00
-- url     : https://prove2.me/theorems/e8f8e6f6-14e7-469d-89f7-3473ebf3f1a0
-- title:
--   Apparatus Hamiltonian $H_A = \mathrm{Tr}_S[H]/d$
-- statement:
--   For an operator $H$ on $\mathcal H_S\otimes\mathcal H_A$ with $d = \dim\mathcal H_S$, the **apparatus Hamiltonian** is
--   $$
--   H_A = \frac1d\,\mathrm{Tr}_S[H].
--   $$
--   In the expansion (3.3), $H = \sum_\alpha F_\alpha\otimes A_\alpha = I_S\otimes H_A + \sum_{\alpha\neq0}F_\alpha\otimes A_\alpha$, the identity component is $F_0\otimes A_0$ with $F_0 = I/\sqrt d$, so $H_A = A_0/\sqrt d = \mathrm{Tr}_S[H]/d$. In particular $H_A$ does not depend on the choice of fixed basis.
--
--   **Formalization Note** The partial trace is the published `WildeQIT.partialTraceLeft`.
-- source:
--   Bacon, Decoherence, Control, and Symmetry in Quantum Computers, arXiv:quant-ph/0305025v1, §3.2.1, eq. (3.3), p.32 (PDF p.49)

import Mathlib
import Definitions.Def_WildeQIT_partialTrace

namespace BaconThesis.Control

/-- Bacon, *Decoherence, Control, and Symmetry in Quantum Computers*, arXiv:quant-ph/0305025v1,
§3.2.1, eq. (3.3), p.32 (PDF p.49): the **apparatus Hamiltonian** `H_A` of the identity component
in `H = Σ_α F_α ⊗ A_α = I_S ⊗ H_A + Σ_{α≠0} F_α ⊗ A_α`, computed from `H` as `H_A = Tr_S[H]/d`,
`d = dim S`.

**Formalization Note.** `Tr_S` is the published `WildeQIT.partialTraceLeft` (system first). Since
`F_0 = I/√d`, `I_S ⊗ H_A = F_0 ⊗ A_0` gives `H_A = A_0/√d = Tr_S[H]/d`, so `H_A` does not depend
on the choice of the fixed basis. -/
noncomputable def HA {s a : Type} [Fintype s] (H : Matrix (s × a) (s × a) ℂ) : Matrix a a ℂ :=
  ((Fintype.card s : ℂ))⁻¹ • WildeQIT.partialTraceLeft H

end BaconThesis.Control


