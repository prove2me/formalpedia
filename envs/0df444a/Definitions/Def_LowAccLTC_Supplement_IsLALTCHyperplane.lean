-- Prove2me | Definitions.Def_LowAccLTC_Supplement_IsLALTCHyperplane
-- name    : LowAccLTC_Supplement_IsLALTCHyperplane
-- status  : Definition
-- author  : @iris
-- created : 2026-11-17T02:24:37.265629+00:00
-- url     : https://prove2.me/theorems/78ba839c-e5d8-4d08-85d4-c18bff233c2a
-- title:
--   Low-acceptance local testability under the axis-parallel hyperplane test
-- statement:
--   Let $B \subseteq F^{[n]}$ be a linear code and let $B^{\otimes k}$ be its $k$-fold tensor power. The **axis-parallel hyperplane test** samples a direction $i \in [k]$ and a value $a \in [n]$ uniformly, then compares the restriction of a word $f : [n]^k \to F$ to the local tensor code on the hyperplane $x_i=a$. Write
--
--   $$
--   \operatorname{dist}_{\mathrm{hyp}}(f)
--     = \mathbb E_{i,a}\!\left[\operatorname{dist}\!\left(f|_{x_i=a},B^{\otimes(k-1)}\right)\right].
--   $$
--
--   For nonempty coordinate and direction sets, the tensor code is an **$(\varepsilon,\varphi)$-low-acceptance locally testable code** under this test if $0<\varepsilon<1$, the function $\varphi$ is nonnegative and monotone nondecreasing on $[0,1]$, and every word $f$ satisfies
--
--   $$
--   x:=1-\operatorname{dist}_{\mathrm{hyp}}(f) \ge \varepsilon
--   \quad\Longrightarrow\quad
--   1-\operatorname{dist}(f,B^{\otimes k}) \ge \varphi(x).
--   $$
--
--   This specializes Definition 2.3 to the vertex test used for tensor codes in Section 5.1.
--
--   **Formalization Note** Directions and coordinates are zero-based `Fin` types, and both choices are uniform. The source type $\varphi:[0,1]\to\mathbb R_+$ is represented by a real-valued function together with nonnegativity and monotonicity on the closed unit interval.
-- source:
--   Ben Yaacov, Dikstein, Liu, Randomness-Efficient Robust LTCs in the Low-Acceptance Regime from HDXs (manuscript, sha256 04242e17…), Definition 2.3, p.14 (PDF p.17), and Section 5.1, p.43 (PDF p.46)

import Definitions.Def_LowAccLTC_tensorCode

namespace LowAccLTC

namespace Supplement

/-! Ben Yaacov, Dikstein, Liu, *Randomness-Efficient Robust LTCs in the Low-Acceptance Regime
from HDXs*, unpublished manuscript (sha256 04242e17…); page references are printed pages
(PDF page − 3). -/

variable {F : Type*} [Field F] {n : ℕ}

/-- `B^{⊗k}` is an `(ε, φ)`-LA LTC (low-acceptance locally testable code) with respect to
the axis-parallel hyperplane test (Definition 2.3, p.14 = PDF p.17, specialized as in §5.1,
p.43 = PDF p.46): for every word `f`, if
`x := 1 - E_{i,a}[dist(f|_{x_i=a}, B^{⊗(k-1)})] ≥ ε`, then
`1 - dist(f, B^{⊗k}) ≥ φ(x)`.

**Formalization Note.** The test samples `i : Fin k` and `a : Fin n` uniformly, so the coordinate
and direction types are required to be nonempty. The source's function `φ : [0,1] → ℝ+` is encoded
as a real-valued function that is nonnegative and monotone on `Set.Icc 0 1`. -/
def IsLALTCHyperplane (B : Submodule F (Fin n → F)) (k : ℕ) (ε : ℝ) (φ : ℝ → ℝ) : Prop :=
  0 < n ∧ 0 < k ∧ 0 < ε ∧ ε < 1 ∧
    (∀ x ∈ Set.Icc (0 : ℝ) 1, 0 ≤ φ x) ∧ MonotoneOn φ (Set.Icc 0 1) ∧
      ∀ f : (Fin k → Fin n) → F, ε ≤ 1 - hyperplaneTestDist B f →
        φ (1 - hyperplaneTestDist B f) ≤ 1 - relDistTo Finset.univ f (tensorCode B k)

end Supplement

end LowAccLTC


