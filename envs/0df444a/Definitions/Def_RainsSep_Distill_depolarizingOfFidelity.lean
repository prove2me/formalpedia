-- Prove2me | Definitions.Def_RainsSep_Distill_depolarizingOfFidelity
-- name    : RainsSep_Distill_depolarizingOfFidelity
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T15:56:52.715612+00:00
-- url     : https://prove2.me/theorems/c79514b0-66ef-4ec4-b172-fd6908666459
-- title:
--   The depolarizing state with fidelity $f$, $\Delta\big(\tfrac43(1-f)\big)$
-- statement:
--   For a real number $f$, the depolarizing state with fidelity $f$ is
--
--   $$
--   \Delta_f=\Delta\big(\tfrac43(1-f)\big),
--   $$
--
--   the depolarizing state of Eq. (19) whose entanglement fidelity equals $f$ (since $f=1-\tfrac34\epsilon$). Theorems 1 and 2 of the paper are stated in terms of $f$: $F_{\mathcal P}(f)$ denotes the output fidelity of $\mathcal P$ on $n$ copies of $\Delta_f$.
--
--   **Formalization Note** Defined for every real $f$; it is a density matrix exactly for $f\in[0,1]$.
-- source:
--   Rains, Entanglement purification via separable superoperators, arXiv:quant-ph/9707002v3, Theorem 1, Eq. (36), p. 3; Theorem 2, p. 3; Eq. (20), p. 2

import Mathlib
import Definitions.Def_RainsSep_Distill_depolarizing

namespace RainsSep.Distill

/-- **The depolarizing state with fidelity `f`, `Δ((4/3)(1 − f))`.**
Rains, *Entanglement purification via separable superoperators*, arXiv:quant-ph/9707002v3, Theorem 1, Eq. (36), p. 3: "F_P(f) := F_P(∆((4/3)(1 − f)))"; Theorem 2, p. 3: "the
depolarizing state ∆(ǫ) with fidelity f"; Eq. (20), p. 2: "f = 1 − (3/4)ǫ = F(∆(ǫ))".

**Formalization Note.** Defined for every real `f`; it is a density matrix exactly for
`f ∈ [0, 1]`. -/
noncomputable def depolarizingOfFidelity (f : ℝ) : Matrix (Bool × Bool) (Bool × Bool) ℂ :=
  depolarizing ((4 / 3) * (1 - f))

end RainsSep.Distill


