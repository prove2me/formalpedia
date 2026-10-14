-- Prove2me | Definitions.Def_Zeta5_SourceOuter
-- name    : Zeta5_SourceOuter
-- status  : Definition
-- author  : @tomasz
-- created : 2026-10-12T21:33:11.89422+00:00
-- url     : https://prove2.me/theorems/3f0549ba-73c4-4755-b54a-d417f5816a88
-- title:
--   Zeta5: the outer-range basis rows, residues and moments
-- statement:
--   The outer-range basis of the Apery proof of $\zeta(5)$: the row roots `rootsO` (tail poles of the other classes plus the multiples of the class representative), the row residue `γO c = -c²`, the entry roots `entryO = 6·[1..3n] + two rows`, and the high moments `μGe` collecting `μ(t^e)` for `e ≥ 2p - 3`.
-- source:
--   https://github.com/mo271/Zeta5/blob/7fe736760f4b96bfdb4334b68e3b3124ecbe10b0/Apery/Arith/OuterBasis.lean, Apery/Arith/OuterEntries.lean, Apery/Arith/OuterFrame.lean (definitions)

import Mathlib
import Definitions.Def_Zeta5_SourceConstruction
import Definitions.Def_Zeta5_SourceArith
import Definitions.Def_Zeta5_SourceInner

/-!
# The outer-range basis and moment definitions of the Apery proof

* `rootsO hm n c i` — the roots of the outer row `(c, i)`:
  the tail poles `3n < j ≤ 40n` of the other classes plus `i` (or `nb c + (i - nb c)`) copies of
  `c` (`Apery/Arith/OuterBasis.lean`);
* `γO c = -c²` in `𝔽_p` — the residue class of the row `(c, i)` (`Apery/Arith/OuterBasis.lean`);
* `entryO hm n cs is ct it` — the entry roots `6·[1..3n] + row cs is + row ct it`
  (`Apery/Arith/OuterEntries.lean`);
* `μGe p Q` — the moments `μ(t^e)` with `e ≥ 2p - 3`, the part of `μ` that may have `v_p = -1`
  (`Apery/Arith/OuterFrame.lean`).

Nothing is proved here; reproduced verbatim from mo271/Zeta5 @
7fe736760f4b96bfdb4334b68e3b3124ecbe10b0.
-/

set_option autoImplicit false

open Finset Polynomial

namespace Apery

section OuterFrame

variable {p : ℕ} [hp : Fact p.Prime]

/-- The moments `e ≥ 2p - 3` of a polynomial. -/
noncomputable def μGe (p : ℕ) (Q : ℚ[X]) : ℚ :=
  ∑ e ∈ range (Q.natDegree + 1), if 2 * p ≤ e + 3 then Q.coeff e * μmono e else 0

end OuterFrame

section OuterBasis

variable {p : ℕ} [hp : Fact p.Prime] {m : ℕ}
variable (hm : 2 * m + 1 = p) (n : ℕ)

/-- The roots of the outer row `(c, i)`. -/
def rootsO (c : Fin (m + 1)) (i : ℕ) : Multiset ℤ :=
  ((tailO n).filter fun j => jc hm j ≠ c).val.map (fun j : ℕ => (j : ℤ)) +
    (if i < nbC hm n c then Multiset.replicate i ((c : ℕ) : ℤ)
      else (bigC hm n c).val.map (fun j : ℕ => (j : ℤ)) + Multiset.replicate (i - nbC hm n c) ((c : ℕ) : ℤ))

/-- `γ_c = -c²` in `𝔽_p`. -/
def γO (c : Fin (m + 1)) : ZMod p := -((((c : ℕ) : ℤ) : ZMod p)) ^ 2

end OuterBasis

section OuterEntries

variable {p : ℕ} [hp : Fact p.Prime] {m : ℕ}

/-- The entry roots `6·[1..N] + rows`. -/
def entryO (hm : 2 * m + 1 = p) (n : ℕ) (cs : Fin (m + 1)) (is : ℕ) (ct : Fin (m + 1)) (it : ℕ) :
    Multiset ℤ :=
  6 • ((Icc 1 (3 * n)).val.map fun j : ℕ => (j : ℤ)) + rootsO hm n cs is + rootsO hm n ct it

end OuterEntries

end Apery


