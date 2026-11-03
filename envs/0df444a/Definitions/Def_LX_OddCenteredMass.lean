-- Prove2me | Definitions.Def_LX_OddCenteredMass
-- name    : LX_OddCenteredMass
-- status  : Definition
-- author  : @chaos-ghost
-- created : 2026-11-02T18:07:38.362817+00:00
-- url     : https://prove2.me/theorems/446f6270-162c-403a-b45d-101e83f06c0a
-- title:
--   Centered reflection and perturbed displacement boards
-- statement:
--   For positive $n$, a natural center parameter $m$, and integer phase $C$, use the centered representative $\operatorname{ctr}_m(z)=((z+m)\bmod n)-m$. Define the reflection board at $i$ as $\operatorname{ctr}_m(C-2i)$. For a permutation $\rho$, its perturbed board is $\operatorname{ctr}_m(C-\rho(i)-i)$. Also define the cyclic reflection residue as $C+m-2i$ modulo $n$. These constructions are defined without an odd dimension hypothesis or a balancing assertion. They provide explicit representatives for reflection based lift families.
-- source:
--   https://github.com/snow-ghost/glushkov-lx-lean/blob/8cddcd222b591673dc63475d9d45b9ed5c6eb92c/LX/OddCenteredMass.lean#L9-L12

/-
Adapted from https://github.com/snow-ghost/glushkov-lx-lean at 8cddcd222b591673dc63475d9d45b9ed5c6eb92c.
MIT License

Copyright (c) 2026 S. Uskov

Permission is hereby granted, free of charge, to any person obtaining a copy
of this software and associated documentation files (the "Software"), to deal
in the Software without restriction, including without limitation the rights
to use, copy, modify, merge, publish, distribute, sublicense, and/or sell
copies of the Software, and to permit persons to whom the Software is
furnished to do so, subject to the following conditions:

The above copyright notice and this permission notice shall be included in all
copies or substantial portions of the Software.

THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,
OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE
SOFTWARE.

-/
import Mathlib
import Definitions.Def_LX_AffineCrossings
import Definitions.Def_LX_AffineLift
import Definitions.Def_LX_CenteredLiftSelection
import Definitions.Def_LX_Connected
import Definitions.Def_LX_Graph
import Definitions.Def_LX_LiftedModel
import Definitions.Def_LX_PhysicalModel
import Definitions.Def_LX_SymmetricWordMetric
import Definitions.Def_LX_WordMetric

namespace Int
end Int
namespace LX
end LX
namespace LX.CenteredLift
end LX.CenteredLift
namespace LX.Core
end LX.Core
namespace LX.Core.AffineLift
end LX.Core.AffineLift
namespace LX.Core.LiftedModel
end LX.Core.LiftedModel
namespace LX.Core.PhysicalModel
end LX.Core.PhysicalModel
namespace LX.Core.RotationWords
end LX.Core.RotationWords
namespace List
end List

namespace LX.CenteredLift
open scoped BigOperators Fin.IntCast Fin.NatCast Fin.CommRing
variable {n : ℕ} [NeZero n]

def reflectionResidue (m : ℕ) (C : ℤ) (i : Fin n) : Fin n := (C+m : ℤ)-2*i
def reflectionBoard (m : ℕ) (C : ℤ) (i : Fin n) : ℤ := center (n := n) m (C-2*(i : ℤ))
def perturbedBoard (m : ℕ) (C : ℤ) (ρ : State n) (i : Fin n) : ℤ :=
  center (n := n) m (C-(ρ i : ℤ)-(i : ℤ))












end LX.CenteredLift


