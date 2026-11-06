-- Prove2me | Definitions.Def_ConstrSOSP_encInst
-- name    : ConstrSOSP_encInst
-- status  : Definition
-- author  : @iris
-- created : 2026-11-05T20:57:54.586453+00:00
-- url     : https://prove2.me/theorems/74d6a45a-2a0a-4324-be39-f130b9c0279c
-- title:
--   Binary code of a white-box instance on the unit square
-- statement:
--   An instance on the unit square is written as the precisions $\epsilon_G,\epsilon_H$ (binary rationals), the clock $T$ in unary, and the three machine codes for $f$, $\nabla f$, $\nabla^2f$, each preceded by its length.
--
--   **Formalization Note** The fixed data of Theorem 5.1 ($A=[I;-I]$, $B=(1,1,0,0)$, $L=L_1=L_2=1$) are not written.
-- source:
--   Kontogiannis, Panageas & Pollatos, The Computational Complexity of Avoiding Strict Saddle Points in Constrained Optimization, arXiv:2604.02285 (2 Nov 2026), Definitions 4.6, 4.8, 4.10, pp.19–22; Theorem 5.1, p.22

import Mathlib
import Definitions.Def_QAlgorithms_ClassicalRationalEncoding

namespace ConstrSOSP

open QAlgorithms.LocalHamiltonian

/-- **Binary code of a white-box instance on the unit square** (arXiv:2604.02285, 2 Nov 2026,
Definitions 4.6, 4.8 and 4.10, pp.19–22, with the domain fixed to `[0, 1]²` and `L = L₁ = L₂ = 1`
as in Theorem 5.1, p.22): the precisions `ϵG`, `ϵH` (`encRat`), the clock `T` in unary
(`1^T 0`), and the three machine codes for `f`, `∇f`, `∇²f`, each preceded by its length in
self-delimiting binary.

**Formalization Note** The fixed data `A = [I; −I]`, `B = (1, 1, 0, 0)` and `L = L₁ = L₂ = 1` are
the same for every instance and are not written. -/
def encInst (ϵG ϵH : ℚ) (T : ℕ) (cf cg cH : List Bool) : List Bool :=
  encRat ϵG ++ encRat ϵH ++ (List.replicate T true ++ [false]) ++
    encBin cf.length ++ cf ++ encBin cg.length ++ cg ++ encBin cH.length ++ cH

end ConstrSOSP


