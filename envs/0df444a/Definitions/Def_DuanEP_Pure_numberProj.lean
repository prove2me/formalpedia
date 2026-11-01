-- Prove2me | Definitions.Def_DuanEP_Pure_numberProj
-- name    : DuanEP_Pure_numberProj
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T15:21:31.930778+00:00
-- url     : https://prove2.me/theorems/00fadbb3-0c44-4e20-9d83-ffca4b6027da
-- title:
--   Projection $P_j\otimes 1_B$ onto total number $j$ on side A
-- statement:
--   Let $P_j$ be the projection onto the eigenspace with eigenvalue $j$ of the total excitation number $n_{A_1}+\dots+n_{A_m}$ of side A. For a state $\psi$ of the $2m$ modes, $(P_j\otimes 1_B)\psi$ keeps the coefficients of the labels $(a,b)$ with $a_1+\dots+a_m=j$ and sets all others to zero:
--
--   $$
--   \big((P_j\otimes 1_B)\psi\big)(a,b)=\begin{cases}\psi(a,b), & a_1+\dots+a_m=j,\\ 0, & \text{otherwise.}\end{cases}
--   $$
--
--   The QND measurement of the total excitation number on side A is the projective measurement $\{P_j\otimes 1_B\}_{j\in\mathbb N}$.
-- source:
--   Duan, Giedke, Cirac, Zoller, Entanglement purification of Gaussian continuous variable quantum states, arXiv:quant-ph/9912017v2, p. 2

import Mathlib
import Definitions.Def_DuanEP_Pure_totalNumber

namespace DuanEP.Pure

/-- `(P_j ⊗ 1_B) ψ`, where `P_j` is the projection onto the eigenspace with eigenvalue `j` of the
total excitation number `n_{A₁} + ⋯ + n_{A_m}` on the `A` side (Duan, Giedke, Cirac, Zoller, *Entanglement purification of Gaussian continuous variable quantum states*, arXiv:quant-ph/9912017v2, p. 2: "we perform a QND
measurement of the total excitation number `n_{A₁} + n_{A₂} + ⋯ + n_{A_m}` on the A side").

**Formalization Note** The QND measurement is the projective measurement `{P_j ⊗ 1_B}_{j ∈ ℕ}`;
in the Fock basis `P_j ⊗ 1_B` keeps exactly the coefficients whose `A`-occupations sum to `j`. -/
def numberProj {m : ℕ} (j : ℕ) (ψ : (Fin m → ℕ) × (Fin m → ℕ) → ℂ) :
    (Fin m → ℕ) × (Fin m → ℕ) → ℂ :=
  fun p => if totalNumber p.1 = j then ψ p else 0

end DuanEP.Pure


