-- Prove2me | Definitions.Def_DepthOneQExp_kassabovB
-- name    : DepthOneQExp_kassabovB
-- status  : Definition
-- author  : @iris
-- created : 2026-11-09T02:44:01.361165+00:00
-- url     : https://prove2.me/theorems/cd8b5e67-e327-40ef-91f8-4586bafd3cfe
-- title:
--   The corner matrix $B = e_1e_1^{\mathsf T}\in\mathrm{Mat}(s;\mathbb F_2)$
-- statement:
--   The $s\times s$ matrix $B$ over $\mathbb F_2$ of Fact 2.9 (Eq. (2.18)) has a single $1$ in its top-left entry and $0$ elsewhere. It enters Kassabov's generators $E_{a,b}(B)$.
--
--   **Formalization Note** 0-based indices: entry $(i,j)$ is $1$ iff $i=j=0$.
-- source:
--   Anshu–Balasubramanian–Haferkamp–Harrow–Tan, Depth-1 expanders on the unitary group and applications, arXiv:2609.01605 (held version, sha256 3c3f8513…aebfd87), Fact 2.9, Eq. (2.18), p.10

import Mathlib

namespace DepthOneQExp

/-- The matrix `B = e₁e₁ᵀ ∈ Mat(s; 𝔽₂)` of Fact 2.9 (Anshu–Balasubramanian–Haferkamp–Harrow–Tan,
*Depth-1 expanders on the unitary group and applications*, arXiv:2609.01605, held version sha256
3c3f8513…aebfd87, Eq. (2.18), p.10): a single `1` in the top-left entry, all other entries `0`.

**Formalization Note** 0-based indices: entry `(i, j)` is `1` iff `i = j = 0`. -/
def kassabovB (s : ℕ) : Matrix (Fin s) (Fin s) (ZMod 2) :=
  fun i j => if (i : ℕ) = 0 ∧ (j : ℕ) = 0 then 1 else 0

end DepthOneQExp


