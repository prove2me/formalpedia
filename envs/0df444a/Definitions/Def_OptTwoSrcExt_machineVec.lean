-- Prove2me | Definitions.Def_OptTwoSrcExt_machineVec
-- name    : OptTwoSrcExt_machineVec
-- status  : Definition
-- author  : @iris
-- created : 2026-11-10T20:24:57.516584+00:00
-- url     : https://prove2.me/theorems/5ab4bbed-31e2-4059-a7c6-adce81f5e1a6
-- title:
--   Explicit maps on $\mathbb F_2^n$: a machine's output read as a vector of $\mathbb F_2^q$
-- statement:
--   A vector $z\in\mathbb F_2^n$ is written to a machine as the bit string $(z_1,\dots,z_n)$ with $1\mapsto$ true and $0\mapsto$ false. For a function $F$ on tuples of bit strings, $\mathrm{machineVec}(F,q,w)$ runs $F$ on the tuple $w$ and reads the first $q$ output bits as a vector of $\mathbb F_2^q$.
--
--   This encodes "explicit" (Definition 1.1: computable by a polynomial-time algorithm) for the maps $G_n:\mathbb F_2^n\to\mathbb F_2^{q_n}$ of Theorem 3.33 and $L_u:\mathbb F_2^n\to\mathbb F_2^M$ of Theorem 3.17: one polynomial-time machine computes the whole family.
--
--   **Formalization Note** Output bits past the end of the machine's output read as $0$; every statement that uses this map also asserts that the output has exactly $q$ bits.
-- source:
--   X. Li, Asymptotically Optimal Two Source Extractors for Arbitrary Constant Entropy Rate, STOC 2027 submission (manuscript sha256 2edb00b2…), Definition 1.1, p.1 (PDF p.3); Theorem 3.33, p.48; Theorem 3.17, p.38

import Mathlib
import Definitions.Def_LowErrExt_IsPolyTime

namespace OptTwoSrcExt

/-- **A vector of `𝔽₂ⁿ` written as a bit string** (`1 ↦ true`, `0 ↦ false`), the input encoding
of explicit maps on `𝔽₂ⁿ`. -/
def bitsOfVec {n : ℕ} (z : Fin n → ZMod 2) : List Bool :=
  List.ofFn fun i => decide (z i = 1)

/-- **The output of a machine read as a vector of `𝔽₂^q`.**
Li, *Asymptotically Optimal Two Source Extractors for Arbitrary Constant Entropy Rate*, STOC 2027
submission (manuscript sha256 2edb00b2…), Definition 1.1, printed p.1 (PDF p.3): "We say Ext is
explicit if it is computable by a polynomial-time algorithm"; used for the maps
`G_n : F_2^n → F_2^{q_n}` (Theorem 3.33, p.48) and `L_u : F_2^n → F_2^M` (Theorem 3.17, p.38).

`machineVec F q ws` runs `F` on the tuple of bit strings `ws` and reads the first `q` output bits
(`true ↦ 1`) as a vector of `𝔽₂^q`.

**Formalization Note.** Bits past the end of the output read as `0` (`LowErrExt.listOut`); every
statement using this map also asserts that the output has exactly `q` bits. -/
def machineVec (F : List (List Bool) → List Bool) (q : ℕ) (ws : List (List Bool)) :
    Fin q → ZMod 2 :=
  fun i => if LowErrExt.listOut q (F ws) i then 1 else 0

end OptTwoSrcExt


