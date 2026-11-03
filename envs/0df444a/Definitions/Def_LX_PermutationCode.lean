-- Prove2me | Definitions.Def_LX_PermutationCode
-- name    : LX_PermutationCode
-- status  : Definition
-- author  : @chaos-ghost
-- created : 2026-11-02T18:02:58.200047+00:00
-- url     : https://prove2.me/theorems/636f5713-e1ce-4fa3-9c85-0428a019722c
-- title:
--   Recursive finite permutation codes
-- statement:
--   Define a code for a permutation of zero positions to be the unique empty code. Recursively, a code on $n+1$ positions consists of a choice in $0,…,n$ and a code on $n$ positions. Encoding and decoding use the finite permutation decomposition into this first choice and a smaller permutation. The numerical index of a pair $(i,c)$ is $i·n!+I(c)$, with empty index zero. These finite codes provide an explicit indexing scheme for permutation lookup tables and finite computation.
-- source:
--   https://github.com/snow-ghost/glushkov-lx-lean/blob/8cddcd222b591673dc63475d9d45b9ed5c6eb92c/LX/PermutationCode.lean#L8-L33

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
import Definitions.Def_LX_Graph

namespace LX.Core
end LX.Core

/-! A constructive enumeration of permutations. Checking one word per code
avoids a quadratic search through a finite set of evaluated words. -/
namespace LX.Core

def PermCode : ℕ → Type
  | 0 => Unit
  | n + 1 => Fin (n + 1) × PermCode n

instance codeFintype : (n : ℕ) → Fintype (PermCode n)
  | 0 => inferInstanceAs (Fintype Unit)
  | n + 1 => by
    letI := codeFintype n
    exact inferInstanceAs (Fintype (Fin (n + 1) × PermCode n))

def decode : {n : ℕ} → PermCode n → State n
  | 0, _ => 1
  | _ + 1, (i, c) => Equiv.Perm.decomposeFin.symm (i, decode c)

def encode : {n : ℕ} → State n → PermCode n
  | 0, _ => ()
  | _ + 1, p => let q := Equiv.Perm.decomposeFin p; (q.1, encode q.2)



def codeIndex : {n : ℕ} → PermCode n → ℕ
  | 0, _ => 0
  | n + 1, (i, c) => i.val * n.factorial + codeIndex c


end LX.Core


