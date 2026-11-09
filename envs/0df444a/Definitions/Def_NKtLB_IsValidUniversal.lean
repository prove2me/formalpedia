-- Prove2me | Definitions.Def_NKtLB_IsValidUniversal
-- name    : NKtLB_IsValidUniversal
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T06:07:22.565063+00:00
-- url     : https://prove2.me/theorems/1e8b266c-dc3c-4cbf-94b0-f5dd3602bbff
-- title:
--   The fixed universal machine $U$
-- statement:
--   A pair $(U,\langle\cdot\rangle)$ of a machine and a machine code is a **valid universal machine** if $U$ is time-efficient and simulates every machine through the program format $s_\alpha01\langle M\rangle\alpha$. The paper fixes one such machine and defines every Kolmogorov measure with respect to it. Every statement of this mission is made for every valid universal machine.
-- source:
--   Goldberg, Hu, Lu, Lyu, Oliveira, Asymmetry and Complexity of Nondeterministic Computations, arXiv:2610.20188 (version of October 13, 2026), §3.2–3.3, pp.21–22

import Mathlib
import Definitions.Def_NKtLB_IsTimeEfficient
import Definitions.Def_NKtLB_Simulates

namespace NKtLB

/-- **The fixed universal machine** (Goldberg, Hu, Lu, Lyu, Oliveira, *Asymmetry and Complexity of Nondeterministic Computations*, arXiv:2610.20188 (version of October 13, 2026), §3.2–3.3, pp.21–22): "We fix such a machine `U` when
specifying Kolmogorov complexity", where `U` is time-efficient and simulates every machine through
the program format `s_α 01 ⟨M⟩ α`. `IsValidUniversal U code` is the conjunction of the two
conditions; every statement of this mission is made for every such pair `(U, code)`. -/
def IsValidUniversal (U : Machine) (code : Machine → List Bool) : Prop :=
  IsTimeEfficient U ∧ Simulates U code

end NKtLB


