-- Prove2me | Definitions.Def_DuanEP_Pure_totalNumber
-- name    : DuanEP_Pure_totalNumber
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T15:20:48.05107+00:00
-- url     : https://prove2.me/theorems/1fce5e65-10d0-4c61-9865-2d2365753b5a
-- title:
--   Total excitation number $n_{A_1}+\dots+n_{A_m}$
-- statement:
--   For an occupation vector $a\in\mathbb N^m$ of the modes $A_1,\dots,A_m$, the **total excitation number** is
--
--   $$
--   N(a)=a_1+a_2+\dots+a_m,
--   $$
--
--   the eigenvalue of $n_{A_1}+n_{A_2}+\dots+n_{A_m}$ on the Fock basis vector $|a_1,\dots,a_m\rangle$.
-- source:
--   Duan, Giedke, Cirac, Zoller, Entanglement purification of Gaussian continuous variable quantum states, arXiv:quant-ph/9912017v2, p. 2

import Mathlib

namespace DuanEP.Pure

/-- The total excitation number `n_{A₁} + n_{A₂} + ⋯ + n_{A_m}` of the `A` side on the Fock basis
vector with occupations `a` (Duan, Giedke, Cirac, Zoller, *Entanglement purification of Gaussian continuous variable quantum states*, arXiv:quant-ph/9912017v2, p. 2): the eigenvalue `∑ᵢ a i`. -/
def totalNumber {m : ℕ} (a : Fin m → ℕ) : ℕ := ∑ i, a i

end DuanEP.Pure


