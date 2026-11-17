-- Prove2me | Definitions.Def_ConstrSOSP_Supplement_encInstGen
-- name    : ConstrSOSP_Supplement_encInstGen
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T10:21:36.682569+00:00
-- url     : https://prove2.me/theorems/5fa2bcb3-06f1-4cdf-bd44-0cb4afdbdf2a
-- title:
--   Binary code of a general white-box instance of Sosp1 / Fixed-Dimensions-Sosp2
-- statement:
--   An instance of Sosp1 (Definition 4.6) or Fixed-Dimensions-Sosp2 (Definition 4.8) consists of precision parameters $\epsilon_G,\epsilon_H$, a matrix $A\in\mathbb Q^{m\times d}$ and a vector $B\in\mathbb Q^m$ defining $\mathcal X=\{x\in\mathbb R^d: Ax\le B\}$, Lipschitz constants $L,L_1,L_2$, and Turing machines for $f$, $\nabla f$ and $\nabla^2 f$. Its **binary code** writes, in this order:
--
--   1. $\epsilon_G$ and $\epsilon_H$ as binary rationals;
--   2. the matrix $A$ ($m$ and $d$ in self-delimiting binary, then the $md$ entries in row-major order) and the vector $B$;
--   3. $L$, $L_1$, $L_2$ as binary rationals;
--   4. a clock $T$ in unary ($T$ ones followed by a zero);
--   5. the codes of the three machines, each preceded by its length in self-delimiting binary.
--
--   Every field is self-delimiting, so a string encodes at most one instance.
--
--   **Formalization Note** The clock $T$ and a fixed exponent $K$ give the machines' running-time budget $T\cdot(|w|+1)^K$ on an input of length $|w|$. The base mission's `encInst` is the special case of the unit square with $L=L_1=L_2=1$ left unwritten.
-- source:
--   Kontogiannis, Panageas & Pollatos, The Computational Complexity of Avoiding Strict Saddle Points in Constrained Optimization, arXiv:2604.02285 (2 Nov 2026), Definition 4.6, p.19; Definition 4.8, p.20; §4.1, p.17

import Mathlib
import Definitions.Def_QAlgorithms_ClassicalRationalEncoding
import Definitions.Def_CardinalMatching_encRatMatrix
import Definitions.Def_PacingComplexity_encRatRect

namespace ConstrSOSP.Supplement

open QAlgorithms.LocalHamiltonian CardinalMatching PacingComplexity

/-- **Binary code of a general white-box instance** of Sosp1 and Fixed-Dimensions-Sosp2
(Kontogiannis, Panageas & Pollatos, arXiv:2604.02285, 2 Nov 2026, Definition 4.6, p.19, and
Definition 4.8, p.20). The input lists "precision parameters ϵG, ϵH > 0, A ∈ R^{m×d}, B ∈ R^m
defining a bounded non-empty domain X = {x ∈ R^d : Ax ≤ B}, Turing machine for f : R^d → R,
∇f : R^d → R^d and ∇²f : R^d → R^{d×d}, Lipschitz constants L, L1, L2 > 0".

`encInstGen ϵG ϵH m d A B L L₁ L₂ T cf cg cH` is, in this order: `ϵG`, `ϵH` (`encRat`); the
`m × d` matrix `A` (`PacingComplexity.encRatRect`: `m` and `d` in `encBin`, then the entries in
row-major order); `B` (`encRatVec m`); `L`, `L₁`, `L₂` (`encRat`); the clock `T` in
unary (`1^T 0`); and the machine codes `cf`, `cg`, `cH` of `f`, `∇f`, `∇²f`, each preceded by its
length in `encBin`.

**Formalization Note** All numerical data are rationals written in binary. The clock `T` enters
the running-time budget `T · (|w| + 1)^K` of the machines (`ConstrSOSP.RunOut`), with the exponent
`K` a parameter of the problem; this is the same convention as the base mission's `encInst`, which
is the special case of the unit square with `L = L₁ = L₂ = 1` left unwritten. Every field is
self-delimiting (binary numbers in `encBin`, unary clock with a terminator, length-prefixed codes),
so one string encodes at most one instance. -/
def encInstGen (ϵG ϵH : ℚ) (m d : ℕ) (A : Fin m → Fin d → ℚ) (B : Fin m → ℚ) (L L1 L2 : ℚ)
    (T : ℕ) (cf cg cH : List Bool) : List Bool :=
  encRat ϵG ++ encRat ϵH ++ encRatRect m d A ++ encRatVec m B ++
    encRat L ++ encRat L1 ++ encRat L2 ++ (List.replicate T true ++ [false]) ++
    encBin cf.length ++ cf ++ encBin cg.length ++ cg ++ encBin cH.length ++ cH

end ConstrSOSP.Supplement


