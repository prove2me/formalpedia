-- Prove2me | Definitions.Def_RennerKoenig_nonUnif
-- name    : RennerKoenig_nonUnif
-- status  : Definition
-- author  : @iris
-- created : 2026-11-04T06:47:33.241061+00:00
-- url     : https://prove2.me/theorems/3379b7a4-67c0-4501-a10d-a66f1c045894
-- title:
--   Non-uniformity $d(X|\rho)$
-- statement:
--   Let $X$ be a random variable with finite range $\mathcal X$ and $\rho$ a random state. The non-uniformity of $X$ given $\rho$ is
--
--   $$
--   d(X|\rho)=\delta\big([\{X\}\otimes\rho],\ [\{U\}]\otimes[\rho]\big),
--   $$
--
--   where $U$ is uniform on $\mathcal X$. It is the paper's security measure: $X$ is an $\varepsilon$-secure key with respect to $\rho$ when $d(X|\rho)\le\varepsilon$.
-- source:
--   Renner–König, Universally Composable Privacy Amplification Against Quantum Adversaries, arXiv:quant-ph/0403133v2, Definition 2.3, p.6

import Mathlib
import Definitions.Def_RennerKoenig_avg
import Definitions.Def_RennerKoenig_withReg
import Definitions.Def_RennerKoenig_ideal
import Definitions.Def_RennerKoenig_traceDist

namespace RennerKoenig

/-- **Non-uniformity** `d(X|ρ) = δ([{X} ⊗ ρ], [{U}] ⊗ [ρ])`, with `U` uniform on the range `α` of
`X`. Renner–König, *Universally Composable Privacy Amplification Against Quantum Adversaries*,
arXiv:quant-ph/0403133v2, Definition 2.3, p.6. -/
noncomputable def nonUnif {Ω α : Type*} [Fintype α] {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] (P : PMF Ω) (X : Ω → α)
    (ρ : Ω → H →L[ℂ] H) : ℝ :=
  traceDist (avg P (withReg X ρ)) (ideal α (avg P ρ))

end RennerKoenig


