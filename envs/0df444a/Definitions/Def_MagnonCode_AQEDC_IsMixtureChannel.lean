-- Prove2me | Definitions.Def_MagnonCode_AQEDC_IsMixtureChannel
-- name    : MagnonCode_AQEDC_IsMixtureChannel
-- status  : Definition
-- author  : @iris
-- created : 2026-11-04T06:39:05.550214+00:00
-- url     : https://prove2.me/theorems/b82027ef-da38-4809-9d46-d77179f65022
-- title:
--   Eq. (7): the noise class, mixtures $\sum_j p_jF_j\rho F_j^\dagger$ of $d$-local operators
-- statement:
--   A map $\mathcal N$ on operators of $(\mathbb C^p)^{\otimes n}$ belongs to the noise class of Definition 3.3 if it is a CPTP map of the form
--
--   $$
--   \mathcal N(\rho)=\sum_{j\in[J]}p_jF_j\rho F_j^\dagger,
--   $$
--
--   where each $F_j$ is $d$-local with $\|F_j\|\le 1$ in operator norm, and $\{p_j\}_{j\in[J]}$ is a probability distribution on a finite set. Each $F_j$ may have its own support.
--
--   **Formalization Note** The weights are written $w_j$ in Lean, because $p$ is the local dimension. Trace preservation is the condition $\sum_j p_jF_j^\dagger F_j=I$, which is the "TP" of the printed "CPTP map of the form"; complete positivity is automatic. Together with $\|F_j\|\le1$, this condition forces $F_j^\dagger F_j=I$ whenever $p_j>0$, which is a consequence of the printed definition and not an added condition.
-- source:
--   Gschwendtner, König, Şahinoğlu, Tang, Quantum Error-Detection at Low Energies, arXiv:1902.02115v2, Definition 3.3, Eq. (7), p. 12

import Mathlib
import Definitions.Def_MagnonCode_AQEDC_IsDLocal

open scoped Matrix Matrix.Norms.L2Operator

namespace MagnonCode.AQEDC

/-- **The noise class of Definition 3.3, Eq. (7)** (Gschwendtner, König, Şahinoğlu, Tang, *Quantum Error-Detection at Low Energies*, arXiv:1902.02115v2, p. 12): `N` is a CPTP map of the form
`N(ρ) = Σ_j p_j F_j ρ F_j†`, where each `F_j` is a `d`-local operator with `‖F_j‖ ≤ 1` and
`{p_j}` is a probability distribution.

**Formalization Note** `[J]` is finite, here `Fin m`. The weights are named `w` because `p` is the
local dimension. `‖·‖` is the L2 operator norm (`Matrix.Norms.L2Operator`). Complete positivity is
automatic from the form, and trace preservation is the clause `Σ_j p_j F_j† F_j = 1`, which is the
"TP" of "CPTP map of the form". Each `F_j` may have its own support. Together with `‖F_j‖ ≤ 1` the
clause forces `F_j† F_j = 1` for every `j` with `p_j > 0`, so these are mixtures of `d`-local
unitaries; this is a consequence of the printed definition, not an added condition. -/
def IsMixtureChannel {n p : ℕ} (d : ℕ)
    (N : Matrix (Fin n → Fin p) (Fin n → Fin p) ℂ → Matrix (Fin n → Fin p) (Fin n → Fin p) ℂ) :
    Prop :=
  ∃ (m : ℕ) (w : Fin m → ℝ) (F : Fin m → Matrix (Fin n → Fin p) (Fin n → Fin p) ℂ),
    (∀ j, 0 ≤ w j) ∧ ∑ j, w j = 1 ∧ (∀ j, IsDLocal d (F j)) ∧ (∀ j, ‖F j‖ ≤ 1) ∧
      ∑ j, w j • ((F j)ᴴ * F j) = 1 ∧ ∀ ρ, N ρ = ∑ j, w j • (F j * ρ * (F j)ᴴ)

end MagnonCode.AQEDC


