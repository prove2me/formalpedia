-- Prove2me | Definitions.Def_DiagLinesLDT_Weyl
-- name    : DiagLinesLDT_Weyl
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T02:51:04.166011+00:00
-- url     : https://prove2.me/theorems/866e1071-9fb9-47ca-b242-6abf2e3f2f83
-- title:
--   Phase space, symplectic form, and the operators $Z_\chi$, $X$, $W_\chi$, $V$
-- statement:
--   On $\mathcal H=\mathbb C^{\mathbb F_q^3}$ with standard basis $\{|z\rangle\}$, for $p,r\in\mathbb F_q^3$:
--
--   $$Z_\chi(p)|z\rangle=\chi(p\cdot z)|z\rangle,\qquad X(r)|z\rangle=|z+r\rangle.$$
--
--   For $v=(p,r)$ and $v'=(p',r')$ in $\mathbb F_q^3\oplus\mathbb F_q^3$, the **symplectic form** is $\langle v,v'\rangle:=p\cdot r'-r\cdot p'$. The two operators used in the construction are
--
--   $$W_\chi(p,r):=\chi\big(-\tfrac12 p\cdot r\big)Z_\chi(p)X(r)\quad(\text{odd characteristic}),\qquad V(p,r):=Z_\chi(p)X(r)\quad(\text{characteristic two}).$$
--
--   **Formalization Note** $\tfrac12$ is the inverse of $2$ in $\mathbb F_q$. Since Lean gives $2^{-1}=0$ in characteristic two, $W_\chi$ is the source's operator only in odd characteristic, which every statement using it assumes.
-- source:
--   Zhao, Fu, Yu, The Role of Diagonal Lines in Quantum Low-Degree Testing, STOC 2027 submission (PDF of 2026-11-03, sha256 831c30c6…), §4.2, pp.6–7, §7.1, p.21, and §7.2, p.23

import Mathlib
import Definitions.Def_DiagLinesLDT_chi

namespace DiagLinesLDT

/-- The phase space `𝔽_q³ ⊕ 𝔽_q³`; a point is `v = (p, r)`. -/
abbrev PS (F : Type*) : Type _ := (Fin 3 → F) × (Fin 3 → F)

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-- The symplectic form `⟨v, v'⟩ := p · r' - r · p'` (p.7). -/
def symp (v v' : PS F) : F := v.1 ⬝ᵥ v'.2 - v.2 ⬝ᵥ v'.1

/-- The phase operator `Z_χ(p) |z⟩ = χ(p · z) |z⟩` on `ℂ^{𝔽_q³}` (§7.1, p.21). -/
noncomputable def Zop (p : Fin 3 → F) : Matrix (Fin 3 → F) (Fin 3 → F) ℂ :=
  Matrix.diagonal fun z => chi F (p ⬝ᵥ z)

/-- The shift operator `X(r) |z⟩ = |z + r⟩` on `ℂ^{𝔽_q³}` (§4.2, p.6). -/
def Xop (r : Fin 3 → F) : Matrix (Fin 3 → F) (Fin 3 → F) ℂ :=
  Matrix.of fun i j => if i = j + r then 1 else 0

/-- The Weyl operator `W_χ(p, r) := χ(-½ p · r) Z_χ(p) X(r)` of odd characteristic.

Source: Zhao, Fu, Yu, The Role of Diagonal Lines in Quantum Low-Degree Testing, STOC 2027 submission
(PDF of 2026-11-03, sha256 831c30c6…), §7.1, p.21 (for `q` prime: §4.2, p.6).

**Formalization Note** `½` is `(2 : F)⁻¹`, so this is the source's operator only when
`ringChar F ≠ 2`, which every statement using it assumes. In characteristic two use `Vop`. -/
noncomputable def Wop (v : PS F) : Matrix (Fin 3 → F) (Fin 3 → F) ℂ :=
  chi F (-((2 : F)⁻¹ * (v.1 ⬝ᵥ v.2))) • (Zop v.1 * Xop v.2)

/-- The operator `V(p, r) := Z_χ(p) X(r)` of characteristic two.

Source: Zhao, Fu, Yu, STOC 2027 submission (PDF of 2026-11-03, sha256 831c30c6…), §7.2, p.23. -/
noncomputable def Vop (v : PS F) : Matrix (Fin 3 → F) (Fin 3 → F) ℂ :=
  Zop v.1 * Xop v.2

end DiagLinesLDT


