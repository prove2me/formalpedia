-- Prove2me | Definitions.Def_DepthOneQExp_kassabovA
-- name    : DepthOneQExp_kassabovA
-- status  : Definition
-- author  : @iris
-- created : 2026-11-09T02:44:05.80602+00:00
-- url     : https://prove2.me/theorems/acf26429-b41f-45f6-814a-8caa06111543
-- title:
--   The cyclic shift $A\in\mathrm{Mat}(s;\mathbb F_2)$
-- statement:
--   The $s\times s$ matrix $A$ over $\mathbb F_2$ of Fact 2.9 (Eq. (2.18)) is the cyclic shift
--   $$
--   A_{i,i+1}=1\ (1\le i<s),\qquad A_{s,1}=1,
--   $$
--   all other entries $0$. Together with $B$ it generates the algebra $\mathrm{Mat}(s;\mathbb F_2)$, and it enters Kassabov's generators $E_{a,b}(A)$.
--
--   **Formalization Note** 0-based indices: entry $(i,j)$ is $1$ iff $j\equiv i+1 \pmod s$. For $s=1$, $A=I_1$.
-- source:
--   Anshu–Balasubramanian–Haferkamp–Harrow–Tan, Depth-1 expanders on the unitary group and applications, arXiv:2609.01605 (held version, sha256 3c3f8513…aebfd87), Fact 2.9, Eq. (2.18), p.10

import Mathlib

namespace DepthOneQExp

/-- The cyclic shift `A ∈ Mat(s; 𝔽₂)` of Fact 2.9 (Anshu–Balasubramanian–Haferkamp–Harrow–Tan,
*Depth-1 expanders on the unitary group and applications*, arXiv:2609.01605, held version sha256
3c3f8513…aebfd87, Eq. (2.18), p.10): `A_{i,i+1} = 1` for `i < s`, `A_{s,1} = 1`, all other
entries `0`.

**Formalization Note** 0-based indices: entry `(i, j)` is `1` iff `j = (i + 1) mod s`. For `s = 1`
this is the `1 × 1` identity. -/
def kassabovA (s : ℕ) : Matrix (Fin s) (Fin s) (ZMod 2) :=
  fun i j => if (j : ℕ) = ((i : ℕ) + 1) % s then 1 else 0

end DepthOneQExp


