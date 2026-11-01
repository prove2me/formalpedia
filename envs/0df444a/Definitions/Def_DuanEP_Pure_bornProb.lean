-- Prove2me | Definitions.Def_DuanEP_Pure_bornProb
-- name    : DuanEP_Pure_bornProb
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T15:22:23.973887+00:00
-- url     : https://prove2.me/theorems/cb0f0e9d-7cb3-48b9-b75b-077de4a4227b
-- title:
--   Born probability of QND outcome $j$
-- statement:
--   For a state $\psi$ of the $2m$ modes and an outcome $j\in\mathbb N$, the **probability of outcome $j$** of the QND measurement of the total excitation number on side A is the Born probability
--
--   $$
--   p_j(\psi)=\big\|(P_j\otimes 1_B)\psi\big\|^2=\sum_{(a,b):\ a_1+\dots+a_m=j}|\psi(a,b)|^2 .
--   $$
--
--   **Formalization Note** The sum is taken in $[0,\infty]$, so it has no default value for a non-summable family. This is the actual Born probability; its closed form for the squeezed state is a milestone.
-- source:
--   Duan, Giedke, Cirac, Zoller, Entanglement purification of Gaussian continuous variable quantum states, arXiv:quant-ph/9912017v2, p. 2

import Mathlib
import Definitions.Def_DuanEP_Pure_numberProj

open scoped ENNReal

namespace DuanEP.Pure

/-- The Born probability `‖(P_j ⊗ 1_B) ψ‖²` of outcome `j` of the QND measurement of the total
excitation number on the `A` side (Duan, Giedke, Cirac, Zoller, *Entanglement purification of Gaussian continuous variable quantum states*, arXiv:quant-ph/9912017v2, p. 2: "with probability `p_j`").

**Formalization Note** The sum is taken in `ℝ≥0∞`, so it has no junk value for a non-summable
family. It is the actual Born probability, not the paper's closed form (that identity is the
milestone `qnd_outcome_law`). -/
noncomputable def bornProb {m : ℕ} (ψ : (Fin m → ℕ) × (Fin m → ℕ) → ℂ) (j : ℕ) : ℝ≥0∞ :=
  ∑' p, (‖numberProj j ψ p‖₊ : ℝ≥0∞) ^ 2

end DuanEP.Pure


