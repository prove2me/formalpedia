-- Prove2me | Definitions.Def_DuanEP_Pure_postState
-- name    : DuanEP_Pure_postState
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T15:23:24.959926+00:00
-- url     : https://prove2.me/theorems/a882de25-b949-460a-8618-795de6aa5fe7
-- title:
--   Post-measurement state after QND outcome $j$
-- statement:
--   For a state $\psi$ of the $2m$ modes and an outcome $j$ of positive probability, the **post-measurement state** is the normalized projection
--
--   $$
--   \psi_j=\frac{(P_j\otimes 1_B)\psi}{\big\|(P_j\otimes 1_B)\psi\big\|}=\frac{(P_j\otimes 1_B)\psi}{\sqrt{p_j(\psi)}} .
--   $$
--
--   **Formalization Note** Where $p_j(\psi)=0$ Lean's division by zero makes $\psi_j$ the zero function; every statement of the mission weights $\psi_j$ by $p_j(\psi)$, so this value never matters. This is the actual post-measurement state; its identification with $|j\rangle$ is a milestone.
-- source:
--   Duan, Giedke, Cirac, Zoller, Entanglement purification of Gaussian continuous variable quantum states, arXiv:quant-ph/9912017v2, p. 2

import Mathlib
import Definitions.Def_DuanEP_Pure_bornProb

namespace DuanEP.Pure

/-- The normalized post-measurement state `(P_j ⊗ 1_B) ψ / ‖(P_j ⊗ 1_B) ψ‖` after outcome `j` of the
QND measurement of the total excitation number on the `A` side (Duan, Giedke, Cirac, Zoller, *Entanglement purification of Gaussian continuous variable quantum states*, arXiv:quant-ph/9912017v2, p. 2: "the QND measurement
projects the state onto …").

**Formalization Note** The norm is `√(bornProb ψ j)`. The state is meaningful only where
`bornProb ψ j ≠ 0`; elsewhere Lean's `x / 0 = 0` makes it the zero function, and every statement
of the mission weights it by `bornProb ψ j`. It is the actual post-measurement state, not the
paper's `|j⟩` (that identity is the milestone `qnd_outcome_law`). -/
noncomputable def postState {m : ℕ} (ψ : (Fin m → ℕ) × (Fin m → ℕ) → ℂ) (j : ℕ) :
    (Fin m → ℕ) × (Fin m → ℕ) → ℂ :=
  fun p => numberProj j ψ p / ((Real.sqrt (bornProb ψ j).toReal : ℝ) : ℂ)

end DuanEP.Pure


