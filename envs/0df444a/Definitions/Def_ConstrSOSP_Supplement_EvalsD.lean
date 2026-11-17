-- Prove2me | Definitions.Def_ConstrSOSP_Supplement_EvalsD
-- name    : ConstrSOSP_Supplement_EvalsD
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T10:22:27.233364+00:00
-- url     : https://prove2.me/theorems/88bf5526-a840-4716-873f-52adbf5bbb6d
-- title:
--   White-box evaluation of $f,\nabla f,\nabla^2 f$ at a rational point of $\mathbb R^d$
-- statement:
--   Fix a dimension $d$, a clock exponent $K$, a clock $T$ and three machine codes $c_f,c_g,c_H$. For a rational point $x\in\mathbb Q^d$, a rational $v$, a rational vector $g\in\mathbb Q^d$ and a rational $d\times d$ matrix $H$, the predicate holds when, on the binary code of $x$, the machine $c_f$ outputs the code of $v$, the machine $c_g$ outputs the code of $g$, and the machine $c_H$ outputs the code of $H$, each within $T\cdot(|w|+1)^K$ steps, $|w|$ the input length.
--
--   The values $v,g,H$ are then $f(x)$, $\nabla f(x)$, $\nabla^2 f(x)$ of the white-box instance: the paper states that "$f(x)$, $\nabla f(x)$, and $\nabla^2 f(x)$ at rational inputs denote the rational outputs of the supplied polynomial-time Turing machines".
--
--   **Formalization Note** The base mission's `Evals` is the case $d=2$.
-- source:
--   Kontogiannis, Panageas & Pollatos, The Computational Complexity of Avoiding Strict Saddle Points in Constrained Optimization, arXiv:2604.02285 (2 Nov 2026), §4.1, p.17

import Mathlib
import Definitions.Def_QAlgorithms_ClassicalRationalEncoding
import Definitions.Def_CardinalMatching_encRatMatrix
import Definitions.Def_ConstrSOSP_RunOut

namespace ConstrSOSP.Supplement

open QAlgorithms.LocalHamiltonian CardinalMatching ConstrSOSP

/-- **White-box evaluation at a rational point of `ℝᵈ`** (Kontogiannis, Panageas & Pollatos,
arXiv:2604.02285, 2 Nov 2026, §4.1, p.17: "Throughout the white-box formulation, f(x), ∇f(x), and
∇²f(x) at rational inputs denote the rational outputs of the supplied polynomial-time Turing
machines, and the stated Lipschitz and Taylor conditions refer to these maps. The same convention
applies to both the hardness and membership proofs.").

`EvalsD d K T cf cg cH x v g H` holds iff, on the input `encRatVec d x`, the machine coded by `cf`
outputs `encRat v`, the machine coded by `cg` outputs `encRatVec d g`, and the machine coded by `cH`
outputs `encRatMatrix d H`, each within the clock `T · (|w| + 1)^K` (`ConstrSOSP.RunOut`). Then
`v`, `g`, `H` are the values `f(x)`, `∇f(x)`, `∇²f(x)` of the instance.

**Formalization Note** The base mission's `ConstrSOSP.Evals` is the case `d = 2`. -/
def EvalsD (d K T : ℕ) (cf cg cH : List Bool) (x : Fin d → ℚ) (v : ℚ) (g : Fin d → ℚ)
    (H : Fin d → Fin d → ℚ) : Prop :=
  RunOut K T cf (encRatVec d x) (encRat v) ∧
    RunOut K T cg (encRatVec d x) (encRatVec d g) ∧
    RunOut K T cH (encRatVec d x) (encRatMatrix d H)

end ConstrSOSP.Supplement


