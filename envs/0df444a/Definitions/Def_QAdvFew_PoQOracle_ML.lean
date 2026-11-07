-- Prove2me | Definitions.Def_QAdvFew_PoQOracle_ML
-- name    : QAdvFew_PoQOracle_ML
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T10:48:54.841339+00:00
-- url     : https://prove2.me/theorems/c841facd-89af-4898-b356-182d4e0a9dbf
-- title:
--   Multilinear extension
-- statement:
--   For $f:\{0,1\}^t\to\{0,1\}$, the **multilinear extension** of $f$ over $\mathbb F_{2^d}^t$ is
--   $$
--   \mathrm{ML}_{2^d}[f](x)=\sum_{u\in\{0,1\}^t}f(u)\chi_u(x),\qquad \chi_u(x)=\prod_{i=1}^t\bigl(u_ix_i+(1-u_i)(1-x_i)\bigr),
--   $$
--   computed in $\mathbb F_2[X]$ and reduced modulo $q_d$.
--
--   **Formalization Note** The factor is written $x_i$ for $u_i=1$ and $1-x_i$ for $u_i=0$, the same value.
-- source:
--   Goldin, Lombardi, Morimae, Quantum Advantage has Few Complexity Implications, arXiv:2611.05303v1, §3.2.5, Eq. (2), p. 14 (PDF p. 16)

import Mathlib
import Definitions.Def_QAlgorithms_Defs_Complexity
import Definitions.Def_QAdvFew_PoQOracle_qPoly

open Polynomial QAlgorithms.Complexity

namespace QAdvFew.PoQOracle

/-- The field element of `F_{2^d}` with bit representation `bs` (its first `d` bits are the
coefficients of `1, X, …, X^{d−1}`), as a polynomial of degree `< d`. -/
noncomputable def fieldElt (d : ℕ) (bs : Str) : (ZMod 2)[X] :=
  ∑ i ∈ Finset.range d, C (if bs.getD i false then (1 : ZMod 2) else 0) * X ^ i

/-- The **multilinear extension** `ML_{2^d}[f]` of `f : {0,1}^t → {0,1}` over `F_{2^d}^t` (Goldin,
Lombardi, Morimae, *Quantum Advantage has Few Complexity Implications*, arXiv:2611.05303v1,
§3.2.5, Eq. (2), p. 14 (PDF p. 16)):
`ML_{2^d}[f](x) = Σ_{u ∈ {0,1}^t} f(u) χ_u(x)`, `χ_u(x) = ∏_i (u_i x_i + (1 − u_i)(1 − x_i))`,
computed in `F₂[X]` and reduced modulo `qPoly d`, which is computing in `F₂[X]/(qPoly d) = F_{2^d}`
and returning the reduced representative.

**Formalization Note** `u_i x_i + (1 − u_i)(1 − x_i)` is written `x_i` for `u_i = 1` and `1 − x_i`
for `u_i = 0`, the same value. -/
noncomputable def mlValue (d t : ℕ) (f : (Fin t → Bool) → Bool) (x : Fin t → (ZMod 2)[X]) :
    (ZMod 2)[X] :=
  (∑ u : Fin t → Bool, C (if f u then (1 : ZMod 2) else 0) *
      ∏ i : Fin t, (if u i then x i else 1 - x i)) %ₘ qPoly d

end QAdvFew.PoQOracle


