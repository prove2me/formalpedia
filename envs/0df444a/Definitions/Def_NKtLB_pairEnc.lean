-- Prove2me | Definitions.Def_NKtLB_pairEnc
-- name    : NKtLB_pairEnc
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T06:01:25.847548+00:00
-- url     : https://prove2.me/theorems/36efa339-c94f-4aa6-a0bd-d76a723a7c04
-- title:
--   The instance $(x,1^s)$ as a string
-- statement:
--   The pair $(x,1^s)$ is encoded as $\mathrm{dbl}(x)\,01\,1^s$, a string of length $2|x|+2+s$. The encoding is injective.
--
--   **Formalization Note** The paper does not fix the pairing. This one follows its own program format $s_\alpha01\cdots$.
-- source:
--   Goldberg, Hu, Lu, Lyu, Oliveira, Asymmetry and Complexity of Nondeterministic Computations, arXiv:2610.20188 (version of October 13, 2026), §1.2.4, p.12

import Mathlib
import Definitions.Def_NKtLB_dbl

namespace NKtLB

/-- **The instance `(x, 1^s)` of MnKtP as a string** (Goldberg, Hu, Lu, Lyu, Oliveira, *Asymmetry and Complexity of Nondeterministic Computations*, arXiv:2610.20188 (version of October 13, 2026), p.12): `x` bit-doubled, then `01`, then
`1^s`.

**Formalization Note.** The paper does not fix the pairing; this one follows its own program format
(`s_α 01 …`, p.21), is injective and has length `2|x| + 2 + s`. -/
def pairEnc (x : List Bool) (s : ℕ) : List Bool := dbl x ++ [false, true] ++ List.replicate s true

end NKtLB


