-- Prove2me | Definitions.Def_LowErrExt_Supplement_machineBits
-- name    : LowErrExt_Supplement_machineBits
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T05:32:13.009584+00:00
-- url     : https://prove2.me/theorems/22c2a754-6c83-452d-a2d7-6f4d4142ae32
-- title:
--   The $m$ output bits of a machine on an input $x\in\mathbb F_2^n$
-- statement:
--   For a function $F$ on lists of bit strings and an input $x\in\mathbb F_2^n$, the **machine output** $\mathrm{Ext}(x)\in\{0,1\}^m$ is the first $m$ entries of $F$ applied to the single word formed by the bits of $x$; as a vector of $\mathbb F_2^m$ it is read with $1\mapsto 1$ and $0\mapsto 0$.
--
--   This is how an explicit construction $\mathrm{Ext}:\{0,1\}^n\to\{0,1\}^m$, computed by one polynomial-time machine for every input length, is read as a function on $\mathbb F_2^n$ (Theorems 3.20 and 4.1).
--
--   **Formalization Note** The bits of $x$ are the published `LowErrExt.bitsOf`, the output reading is the published `listOut`. Statements using these maps also require the output list to have length exactly $m$.
-- source:
--   D. Doron, J. Goodman, Low-Error Extractors, STOC 2027 submission (manuscript sha256 43c922d6…), Theorem 3.20, p.26; Theorem 4.1, p.29 (explicit Ext)

import Mathlib
import Definitions.Def_LowErrExt_IsPolyTime
import Definitions.Def_LowErrExt_seededOfMachine

namespace LowErrExt.Supplement

open LowErrExt

/-- **The `m` output bits of a machine on input `x ∈ 𝔽₂ⁿ`.**
`machineBits F m x` runs `F` on the single word `bitsOf x` (the bits of `x`) and reads the first
`m` entries of the output list (published `listOut`).
Doron, Goodman, *Low-Error Extractors*, STOC 2027 submission (manuscript sha256 43c922d6…): the
function `Ext : {0,1}ⁿ → {0,1}ᵐ` computed by an explicit construction (Theorems 3.20, 4.1, pp.26, 29).

**Formalization Note.** Statements using it also assert that the output list has length exactly
`m`, so no bit is padded. -/
def machineBits (F : List (List Bool) → List Bool) {n : ℕ} (m : ℕ) (x : Fin n → ZMod 2) :
    Fin m → Bool :=
  listOut m (F [bitsOf x])

/-- **The same output as a vector of `𝔽₂ᵐ`** (`true ↦ 1`, `false ↦ 0`). -/
def machineVec (F : List (List Bool) → List Bool) {n : ℕ} (m : ℕ) (x : Fin n → ZMod 2) :
    Fin m → ZMod 2 :=
  fun i => if machineBits F m x i then 1 else 0

end LowErrExt.Supplement


