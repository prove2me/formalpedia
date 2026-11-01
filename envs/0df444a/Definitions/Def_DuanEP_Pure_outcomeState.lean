-- Prove2me | Definitions.Def_DuanEP_Pure_outcomeState
-- name    : DuanEP_Pure_outcomeState
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T15:21:32.126423+00:00
-- url     : https://prove2.me/theorems/a8169775-37f2-4424-b7a1-70f34edd90c2
-- title:
--   Outcome state $|j\rangle_{(A_iB_i)}$, Eq. (3)
-- statement:
--   For $m\ge 1$ and $j\in\mathbb N$, the normalized state of Eq. (3) is
--
--   $$
--   |j\rangle_{(A_iB_i)}=\frac{1}{\sqrt{f_j^{(m)}}}\sum_{i_1+i_2+\dots+i_m=j}|i_1,i_2,\dots,i_m\rangle_{(A_i)}\otimes|i_1,i_2,\dots,i_m\rangle_{(B_i)} ,
--   $$
--
--   with coefficient function $(a,b)\mapsto 1/\sqrt{f_j^{(m)}}$ if $a=b$ and $a_1+\dots+a_m=j$, and $0$ otherwise.
--
--   It is the state onto which the QND measurement of the total excitation number projects the joint squeezed state when the outcome is $j$.
-- source:
--   Duan, Giedke, Cirac, Zoller, Entanglement purification of Gaussian continuous variable quantum states, arXiv:quant-ph/9912017v2, p. 1, Eq. (3)

import Mathlib
import Definitions.Def_DuanEP_Pure_totalNumber
import Definitions.Def_DuanEP_Pure_fCount

namespace DuanEP.Pure

/-- The normalized state `|j⟩_{(AᵢBᵢ)} = (f_j^{(m)})^{-1/2} ∑_{i₁+⋯+i_m = j} |i₁,…,i_m⟩_{(Aᵢ)} ⊗
|i₁,…,i_m⟩_{(Bᵢ)}` of Eq. (3) (Duan, Giedke, Cirac, Zoller, *Entanglement purification of Gaussian continuous variable quantum states*, arXiv:quant-ph/9912017v2, p. 1), as a coefficient function on the Fock labels
`(a, b)` of the `A` and `B` sides: it is `(f_j^{(m)})^{-1/2}` when `a = b` and `∑ᵢ aᵢ = j`, and `0`
otherwise. -/
noncomputable def outcomeState (m j : ℕ) : (Fin m → ℕ) × (Fin m → ℕ) → ℂ := fun p =>
  if p.1 = p.2 ∧ totalNumber p.1 = j then (((Real.sqrt (fCount m j))⁻¹ : ℝ) : ℂ) else 0

end DuanEP.Pure


