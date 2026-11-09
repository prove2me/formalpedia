-- Prove2me | Definitions.Def_AgnosticTNS_embedOp
-- name    : AgnosticTNS_embedOp
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T16:33:15.773195+00:00
-- url     : https://prove2.me/theorems/7e775290-ba39-450f-ad6f-31fed1fe3950
-- title:
--   Local operator tensored with the identity
-- statement:
--   For an operator $U$ on the qudits of $A\subseteq[n]$, $U\otimes I_{[n]\setminus A}$ is the $n$-qudit operator with entries $U_{x|_A,\,y|_A}$ when $x$ and $y$ agree outside $A$, and $0$ otherwise (Algorithm 1 line 13: $U_{c+1}=\tilde U_i\otimes I_{M_i^c}$).
-- source:
--   Caro–McHugh–Strelchuk, Efficient Agnostic Learning of Tensor Network States, STOC 2027 submission (manuscript sha256 d69077bb…abec0), Algorithm 1 line 13, p.19

import Mathlib

namespace AgnosticTNS

/-- **An operator on a subsystem tensored with the identity**, `Ũ ⊗ I_{M^c}`, Algorithm 1 line 13,
p.19 (Caro–McHugh–Strelchuk, *Efficient Agnostic Learning of Tensor Network States*, STOC 2027 submission manuscript (sha256 d69077bb…abec0)): for `U` acting on the qudits of `A`, the `n`-qudit operator
`(U ⊗ I)_{xy} = U_{x|_A, y|_A}` if `x` and `y` agree outside `A`, and `0` otherwise. -/
def embedOp {n d : ℕ} (A : Finset (Fin n)) (U : Matrix (↥A → Fin d) (↥A → Fin d) ℂ) :
    Matrix (Fin n → Fin d) (Fin n → Fin d) ℂ :=
  Matrix.of fun x y => if ∀ i, i ∉ A → x i = y i then U (fun a => x a.1) (fun a => y a.1) else 0

end AgnosticTNS


