-- Prove2me | Definitions.Def_KempeCloning_occ
-- name    : KempeCloning_occ
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T15:22:34.257484+00:00
-- url     : https://prove2.me/theorems/0694c372-f38c-448a-9d69-5e067bc31e54
-- title:
--   The Fock index $|x_1, x_2, y_1, y_2, z\rangle$
-- statement:
--   For natural numbers $x_1, x_2, y_1, y_2, z$, $\mathrm{occ}(x_1,x_2,y_1,y_2,z)$ is the Fock index with $x_1$ quanta in $a_1$, $x_2$ in $a_2$, $y_1$ in $b_1$, $y_2$ in $b_2$ and $z$ in $c$; it labels the ket
--
--   $$|x_1, x_2, y_1, y_2, z\rangle = |(x_1)_{a_1}, (x_2)_{a_2}, (y_1)_{b_1}, (y_2)_{b_2}, z_c\rangle .$$
--
--   This is the paper's notation for number states, e.g. $|m,0,0,0,N\rangle$ in (13).
-- source:
--   Kempe, Simon, Weihs, Λ's, V's, and optimal cloning with stimulated emission, arXiv:quant-ph/0003025v1, Sec. II B, (13), p.4

import Definitions.Def_KempeCloning_FockIndex

namespace KempeCloning

/-- **The occupation pattern `|n_{a1}, n_{a2}, n_{b1}, n_{b2}, n_c⟩`.**
Kempe, Simon, Weihs, arXiv:quant-ph/0003025v1, Sec. II B, (13), p.4: the ket
"|m_{a1}, 0_{a2}, 0_{b1}, 0_{b2}, N_c⟩ ≡ |m, 0, 0, 0, N⟩" lists the occupation numbers in the
order `a1, a2, b1, b2, c`.

`occ x₁ x₂ y₁ y₂ z` is the Fock index with `x₁` quanta in `a1`, `x₂` in `a2`, `y₁` in `b1`,
`y₂` in `b2` and `z` in `c`. -/
def occ (na1 na2 nb1 nb2 nc : ℕ) : FockIndex
  | .a1 => na1
  | .a2 => na2
  | .b1 => nb1
  | .b2 => nb2
  | .c => nc

end KempeCloning


