-- Prove2me | Definitions.Def_RennerKoenig_hsNonUnif
-- name    : RennerKoenig_hsNonUnif
-- status  : Definition
-- author  : @iris
-- created : 2026-11-04T06:47:34.210258+00:00
-- url     : https://prove2.me/theorems/82d40055-5d33-4232-b0bd-6747f8decfff
-- title:
--   Hilbert–Schmidt non-uniformity $D(X|\rho)$
-- statement:
--   Let $X$ be a random variable with finite range $\mathcal X$ and $\rho$ a random state. Then
--
--   $$
--   D(X|\rho)=\Delta\big([\{X\}\otimes\rho],\ [\{U\}]\otimes[\rho]\big),
--   $$
--
--   where $U$ is uniform on $\mathcal X$. This is the $\Delta$-analogue of $d(X|\rho)$, used in the proof of Theorem 4.1.
-- source:
--   Renner–König, Universally Composable Privacy Amplification Against Quantum Adversaries, arXiv:quant-ph/0403133v2, §4.1, p.9

import Mathlib
import Definitions.Def_RennerKoenig_avg
import Definitions.Def_RennerKoenig_withReg
import Definitions.Def_RennerKoenig_ideal
import Definitions.Def_RennerKoenig_hsDistSq

namespace RennerKoenig

/-- **Hilbert-Schmidt non-uniformity** `D(X|ρ) = Δ([{X} ⊗ ρ], [{U}] ⊗ [ρ])`, with `U` uniform on
the range `α` of `X`. Renner–König, *Universally Composable Privacy Amplification Against Quantum Adversaries*,
arXiv:quant-ph/0403133v2, §4.1, p.9. -/
noncomputable def hsNonUnif {Ω α : Type*} [Fintype α] {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] (P : PMF Ω) (X : Ω → α)
    (ρ : Ω → H →L[ℂ] H) : ℝ :=
  hsDistSq (avg P (withReg X ρ)) (ideal α (avg P ρ))

end RennerKoenig


