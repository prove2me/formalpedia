-- Prove2me | Definitions.Def_ConstrSOSP_Evals
-- name    : ConstrSOSP_Evals
-- status  : Definition
-- author  : @iris
-- created : 2026-11-05T21:01:44.87194+00:00
-- url     : https://prove2.me/theorems/fc6c4499-bdb4-4da0-aac2-a73d5abae20b
-- title:
--   White-box evaluation at a rational point
-- statement:
--   At a rational point $x\in\mathbb Q^2$, the three machines of a white-box instance are run on the binary code of $x$ within the clock. They **return** $(v,g,H)$ when the first outputs the code of the rational $v$, the second the code of the rational vector $g$, and the third the code of the rational $2\times2$ matrix $H$. Then $f(x)=v$, $\nabla f(x)=g$ and $\nabla^2f(x)=H$ (p.17: "$f(x)$, $\nabla f(x)$, and $\nabla^2f(x)$ at rational inputs denote the rational outputs of the supplied polynomial-time Turing machines").
-- source:
--   Kontogiannis, Panageas & Pollatos, The Computational Complexity of Avoiding Strict Saddle Points in Constrained Optimization, arXiv:2604.02285 (2 Nov 2026), §4.1, p.17

import Mathlib
import Definitions.Def_QAlgorithms_ClassicalRationalEncoding
import Definitions.Def_CardinalMatching_encRatMatrix
import Definitions.Def_ConstrSOSP_RunOut

namespace ConstrSOSP

open QAlgorithms.LocalHamiltonian CardinalMatching

/-- **White-box evaluation at a rational point of the plane** (arXiv:2604.02285, 2 Nov 2026, §4.1,
p.17: "Throughout the white-box formulation, f(x), ∇f(x), and ∇²f(x) at rational inputs denote
the rational outputs of the supplied polynomial-time Turing machines").

`Evals K T cf cg cH x v g H` holds iff, on the input `encRatVec 2 x`, the machine coded by `cf`
outputs `encRat v`, the machine coded by `cg` outputs `encRatVec 2 g`, and the machine coded by
`cH` outputs `encRatMatrix 2 H`, each within the clock `T · (|w| + 1)^K` (`RunOut`). Then `v`,
`g`, `H` are the values `f(x)`, `∇f(x)`, `∇²f(x)` of the white-box instance. -/
def Evals (K T : ℕ) (cf cg cH : List Bool) (x : Fin 2 → ℚ) (v : ℚ) (g : Fin 2 → ℚ)
    (H : Fin 2 → Fin 2 → ℚ) : Prop :=
  RunOut K T cf (encRatVec 2 x) (encRat v) ∧
    RunOut K T cg (encRatVec 2 x) (encRatVec 2 g) ∧
    RunOut K T cH (encRatVec 2 x) (encRatMatrix 2 H)

end ConstrSOSP


