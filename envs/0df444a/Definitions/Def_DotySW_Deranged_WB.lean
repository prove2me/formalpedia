-- Prove2me | Definitions.Def_DotySW_Deranged_WB
-- name    : DotySW_Deranged_WB
-- status  : Definition
-- author  : @iris
-- created : 2026-11-04T06:33:05.160644+00:00
-- url     : https://prove2.me/theorems/80491e10-701b-46da-a253-4d2b1cd22a3e
-- title:
--   The walled Brauer algebra $\mathcal B^{(n)}_{r,s}$ over $\mathbb C$
-- statement:
--   The walled Brauer algebra $\mathcal B^{(n)}_{r,s}$ has as a basis the $(r,s)$-diagrams: Brauer diagrams on $r+s$ columns with a wall after the first $r$ columns, such that all horizontal edges cross the wall and no vertical edge does. Diagrams multiply by stacking the first over the second, and each interior loop gives a factor $n$.
--
--   This abbreviation fixes the coefficient field $\mathbb C$ and the parameter $x=n$ used in §3.4.
--
--   **Formalization Note** It is the published algebra `WalledBrauerAlgebra ℂ r s (n : ℂ)`, realised by left multiplications on the free module on the diagrams.
-- source:
--   Doty, New versions of Schur-Weyl duality, arXiv:0704.1877v1, §3.1, unnumbered, p. 7, and §3.4, p. 9

import Mathlib
import Definitions.Def_WalledBrauer_Blocks_Algebra

namespace DotySW.Deranged

open WalledBrauer.Blocks

/-- **The walled Brauer algebra `B^{(n)}_{r,s}` over `ℂ`.**
Doty, *New versions of Schur-Weyl duality*, arXiv:0704.1877v1, §3.1, unnumbered, p. 7, and §3.4, p. 9.

The algebra with basis the `(r, s)`-diagrams, in which a product of diagrams is stacking and each
interior loop gives a factor `n`.

**Formalization Note** The paper's `B^{(x)}_{r,s}` over `R[x]`, specialised at `x = n` over `ℂ`
(the setting of §3.4), is the published `WalledBrauerAlgebra ℂ r s n`. -/
abbrev WB (n r s : ℕ) : Type := WalledBrauerAlgebra ℂ r s (n : ℂ)

end DotySW.Deranged


