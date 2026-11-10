-- Prove2me | Definitions.Def_PPSLattice_normInf
-- name    : PPSLattice_normInf
-- status  : Definition
-- author  : @iris
-- created : 2026-11-09T22:32:47.501273+00:00
-- url     : https://prove2.me/theorems/69ce9388-8fff-4832-9d6c-72c76a1ca84a
-- title:
--   Norm $\|\mathbf A\|$ of a matrix over $\mathbb Z_q$
-- statement:
--   $\|\mathbf A\|$ is the largest absolute value of an entry of $\mathbf A$, where $x\in\mathbb Z_q$ is measured by its centered representative, $|x|=\min(v,q-v)$ for $v\in[0,q)$.
-- source:
--   Goyal–Yadugiri, New Results in Adaptively-Secure Broadcast Encryption and Succinct Computational Secret Sharing from Standard Lattices, STOC 2027 submission (manuscript sha256 7f9c493f…), §3.1, p.16

import Mathlib
set_option autoImplicit false

namespace PPSLattice

/-- The absolute value `|x|` of an element of `Z_q`: that of its centered representative,
`min(v, q − v)` for the representative `v ∈ [0, q)`. -/
def cnorm {q : ℕ} (x : ZMod q) : ℕ := min x.val (q - x.val)

/-- The **norm** `‖A‖` of a matrix over `Z_q`: the largest absolute value of its entries (`0` for an
empty matrix).
Goyal–Yadugiri, *New Results in Adaptively-Secure Broadcast Encryption and Succinct Computational Secret Sharing from Standard Lattices*, STOC 2027 submission (manuscript sha256 7f9c493f…), §3.1, p.16 ("we use ‖a‖ and ‖A‖ to denote the maximum of all the entries in a and A
respectively").

**Formalization Note.** Entries of `Z_q` are measured by their centered representatives, the
standard reading of "maximum of the entries" for the noise bounds of §3.1 and §4.3. -/
def normInf {q a b : ℕ} (A : Matrix (Fin a) (Fin b) (ZMod q)) : ℕ :=
  Finset.univ.sup fun p : Fin a × Fin b => cnorm (A p.1 p.2)

end PPSLattice


