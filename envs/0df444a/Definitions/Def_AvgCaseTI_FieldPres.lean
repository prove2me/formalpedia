-- Prove2me | Definitions.Def_AvgCaseTI_FieldPres
-- name    : AvgCaseTI_FieldPres
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T06:41:24.913951+00:00
-- url     : https://prove2.me/theorems/fcf19a3d-6806-447e-93f0-dda236ebec1d
-- title:
--   Presented finite field $\mathbb F_q=\mathbb F_p[x]/(f)$
-- statement:
--   A **presentation of a finite field** is a pair $(p,f)$ where $p$ is a prime and $f\in\mathbb F_p[x]$ is a monic irreducible polynomial. Its field is
--   $$
--   \mathbb F_q=\mathbb F_p[x]/(f),\qquad q=p^{\deg f}.
--   $$
--   An element of $\mathbb F_q$ is represented by its $\deg f$ coordinates in the basis $1,x,\dots,x^{\deg f-1}$, i.e. by the coefficients of its reduced representative $g \bmod f$.
--
--   Every finite field has such a presentation. An algorithm that works over an arbitrary finite field $\mathbb F_q$ (as in Theorem 1.1, whose running time is $\mathrm{poly}(n,\log q)$) receives the field in this explicit form as part of its input.
--
--   **Formalization Note** The field is Mathlib's `AdjoinRoot f` over `ZMod p`; irreducibility of $f$ already forces $\deg f\ge1$. `P.q` is $p^{\deg f}$, and `P.coords a` lists the coordinates of $a$.
-- source:
--   Li, Li, Qiao, Tao, Wang, On the average-case complexity landscape for Tensor-Isomorphism-complete problems over finite fields, arXiv:2604.00591 (held version sha256 baf552e1…), §1.3, Theorem 1.1, p.5 (PDF p.7)

import Mathlib

set_option autoImplicit false

namespace AvgCaseTI

/-- **An explicit presentation of a finite field** `F_q = F_p[x]/(f)`.

Li, Li, Qiao, Tao, Wang, *On the average-case complexity landscape for Tensor-Isomorphism-complete
problems over finite fields*, arXiv:2604.00591 (held version sha256 baf552e1…), §1.3, p.5 (PDF p.7):
"Fix a prime power q … There is a randomized poly(n, log q)-time algorithm".

A presentation consists of a prime `p` and a monic irreducible polynomial `f ∈ F_p[x]`. Its field is
`F_p[x]/(f)` (`AdjoinRoot f`), of order `q = p ^ deg f`.

**Formalization Note.** An algorithm over `F_q` needs the field as part of its input; every finite
field has such a presentation. Irreducibility already forces `deg f ≥ 1`. -/
structure FieldPres where
  /-- the characteristic -/
  p : ℕ
  hp : p.Prime
  /-- the defining polynomial over `F_p` -/
  f : Polynomial (ZMod p)
  hmonic : f.Monic
  hirr : Irreducible f

namespace FieldPres

instance instFactPrime (P : FieldPres) : Fact P.p.Prime := ⟨P.hp⟩

instance instFactIrr (P : FieldPres) : Fact (Irreducible P.f) := ⟨P.hirr⟩

/-- The field `F_p[x]/(f)` of the presentation. -/
abbrev F (P : FieldPres) : Type := AdjoinRoot P.f

noncomputable instance instField (P : FieldPres) : Field P.F := AdjoinRoot.instField

/-- The order `q = p ^ deg f` of the presented field. -/
def q (P : FieldPres) : ℕ := P.p ^ P.f.natDegree

/-- The power-basis coordinates of a field element: the coefficients of `1, x, …, x^{d−1}` of its
reduced representative `g mod f` (`d = deg f`). -/
noncomputable def coords (P : FieldPres) (a : P.F) : Fin P.f.natDegree → ZMod P.p :=
  fun i => (AdjoinRoot.modByMonicHom P.hmonic a).coeff i

end FieldPres

end AvgCaseTI


