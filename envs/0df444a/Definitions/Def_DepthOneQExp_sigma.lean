-- Prove2me | Definitions.Def_DepthOneQExp_sigma
-- name    : DepthOneQExp_sigma
-- status  : Definition
-- author  : @iris
-- created : 2026-11-09T02:45:34.024998+00:00
-- url     : https://prove2.me/theorems/726d5725-0f9a-4f2d-aa2f-e9c493a0ce80
-- title:
--   Kassabov's generating family $\Sigma_{3s}$ of $\mathrm{SL}(3s;\mathbb F_2)$
-- statement:
--   Kassabov's generating family $\Sigma_{3s}$ (Fact 2.10, Eq. (2.19)) consists of the 14 elements of $\mathrm{SL}(3s;\mathbb F_2)$
--   $$
--   E_{a,b}(I_s)\ \ (1\le a\ne b\le 3),\qquad E_{a,b}(A),\ E_{a,b}(B)\ \ (|a-b|=1),
--   $$
--   with $A$, $B$ the matrices of Fact 2.9. Every element is an involution. The family is indexed as follows (0-based blocks): entries $0$–$5$ are $E_{a,b}(I_s)$ for $(a,b)=(0,1),(0,2),(1,0),(1,2),(2,0),(2,1)$; entries $6$–$9$ are $E_{a,b}(A)$ and entries $10$–$13$ are $E_{a,b}(B)$, both for $(a,b)=(0,1),(1,0),(1,2),(2,1)$.
--
--   **Formalization Note** $\Sigma_{3s}$ is a family of 14 elements counted with multiplicity: for $s=1$, $A=B=I_1$ and entries repeat. Averages $\frac1{|S|}\sum_{g\in S}$ with $|S|=14$ (Lemma 2.12, Theorem 2.3) are averages over this family.
-- source:
--   Anshu–Balasubramanian–Haferkamp–Harrow–Tan, Depth-1 expanders on the unitary group and applications, arXiv:2609.01605 (held version, sha256 3c3f8513…aebfd87), Fact 2.10, Eq. (2.19), p.10

import Mathlib
import Definitions.Def_DepthOneQExp_kassabovA
import Definitions.Def_DepthOneQExp_kassabovB
import Definitions.Def_DepthOneQExp_blockElem

namespace DepthOneQExp

/-- Kassabov's generating family `Σ_{3s}` of `SL(3s; 𝔽₂)` (Anshu–Balasubramanian–Haferkamp–Harrow–Tan,
*Depth-1 expanders on the unitary group and applications*, arXiv:2609.01605, held version sha256
3c3f8513…aebfd87, Fact 2.10, Eq. (2.19), p.10): the 14 elements
`E_{a,b}(I_s)` for `1 ≤ a ≠ b ≤ 3` and `E_{a,b}(A)`, `E_{a,b}(B)` for `|a − b| = 1`.

Indexing (0-based blocks): `0–5` are `E_{a,b}(I_s)` for `(a, b) = (0,1), (0,2), (1,0), (1,2), (2,0),
(2,1)`; `6–9` are `E_{a,b}(A)` and `10–13` are `E_{a,b}(B)`, both for `(a, b) = (0,1), (1,0), (1,2),
(2,1)`.

**Formalization Note** `Σ_{3s}` is an indexed family of 14 elements counted with multiplicity
(for `s = 1`, `A = B = I_1` and entries repeat); the paper's averages `(1/|S|) Σ_{g ∈ S}` with
`|S| = 14` are averages over this family. -/
def sigma (s : ℕ) : Fin 14 → Matrix.SpecialLinearGroup (Fin (3 * s)) (ZMod 2) :=
  let E : (a b : Fin 3) → a ≠ b → Matrix (Fin s) (Fin s) (ZMod 2) →
      Matrix.SpecialLinearGroup (Fin (3 * s)) (ZMod 2) :=
    fun a b h r => ⟨blockElem s a b r, det_blockElem s h r⟩
  ![E 0 1 (by decide) 1, E 0 2 (by decide) 1, E 1 0 (by decide) 1, E 1 2 (by decide) 1,
    E 2 0 (by decide) 1, E 2 1 (by decide) 1,
    E 0 1 (by decide) (kassabovA s), E 1 0 (by decide) (kassabovA s),
    E 1 2 (by decide) (kassabovA s), E 2 1 (by decide) (kassabovA s),
    E 0 1 (by decide) (kassabovB s), E 1 0 (by decide) (kassabovB s),
    E 1 2 (by decide) (kassabovB s), E 2 1 (by decide) (kassabovB s)]

end DepthOneQExp


