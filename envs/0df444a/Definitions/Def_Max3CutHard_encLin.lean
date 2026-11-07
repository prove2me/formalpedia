-- Prove2me | Definitions.Def_Max3CutHard_encLin
-- name    : Max3CutHard_encLin
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T06:45:19.509572+00:00
-- url     : https://prove2.me/theorems/e6cd0827-0f6b-40e9-b89d-68ef9f855578
-- title:
--   Encoding of an encodable 3Lin($\mathbb Z_3$) instance
-- statement:
--   An encodable instance is written as a word over the alphabet $\{\mathtt{one},\mathtt{sep},\mathtt t_0,\mathtt t_1,\mathtt t_2\}$: first $n_U$ and $n_W$ in unary, then for every listed equation $u_e+w_e+w'_e=t_e$ the indices $u_e$, $w_e$, $w'_e$ in unary followed by the symbol $\mathtt t_{t_e}$. A number $a$ is written $\mathtt{one}^a\,\mathtt{sep}$.
--
--   The encoding is injective, so it is the input format of the gap problem in Theorem 2.1. Its length is polynomial in the number of variables and equations.
-- source:
--   Ni, Improved NP-Hardness of Approximation for Max-3-Cut and for Max-k-Cut with Small k, arXiv:2611.01402, Theorem 2.1, p.4

import Mathlib
import Definitions.Def_Max3CutHard_LinSym
import Definitions.Def_Max3CutHard_LinInst

namespace Max3CutHard

/-- **Encoding of an encodable 3Lin(ℤ₃) instance.** Ni, *Improved NP-Hardness of Approximation for Max-3-Cut and for Max-k-Cut with Small k*, arXiv:2611.01402, Theorem 2.1, p.4 (the input of the
problem): `nU` and `nW` in unary, then for every listed equation `u_e`, `w_e`, `w′_e` in unary and
its type `t_e` as one symbol.

**Formalization Note.** Every number `a` is written `one^a sep`; the encoding is injective
(checked in the mission's sanity file), so the gap problem of Theorem 2.1 is not trivialised by
a lossy encoding. -/
def encLin (Φ : LinInst) : List LinSym :=
  (List.replicate Φ.nU LinSym.one ++ [LinSym.sep]) ++
    (List.replicate Φ.nW LinSym.one ++ [LinSym.sep]) ++
    Φ.eqs.flatMap fun e =>
      (List.replicate (e.u : ℕ) LinSym.one ++ [LinSym.sep]) ++
      (List.replicate (e.w : ℕ) LinSym.one ++ [LinSym.sep]) ++
      (List.replicate (e.w' : ℕ) LinSym.one ++ [LinSym.sep]) ++
      [if e.t = 0 then LinSym.t0 else if e.t = 1 then LinSym.t1 else LinSym.t2]

end Max3CutHard


