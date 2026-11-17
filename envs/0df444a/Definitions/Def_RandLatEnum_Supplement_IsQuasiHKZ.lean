-- Prove2me | Definitions.Def_RandLatEnum_Supplement_IsQuasiHKZ
-- name    : RandLatEnum_Supplement_IsQuasiHKZ
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T07:58:25.096339+00:00
-- url     : https://prove2.me/theorems/09f52a48-b1cc-4a82-9c87-393cf8c54d3b
-- title:
--   Quasi-HKZ-reduced basis
-- statement:
--   Let $B=(b_1,\dots,b_n)$, $n\ge 2$, be an ordered basis with Gram–Schmidt vectors $b_i^*$, lengths $a_i=\|b_i^*\|$ and coefficients $\mu_{j,i}$, so that $b_j=b_j^*+\sum_{i<j}\mu_{j,i}b_i^*$. Write $\pi_2$ for the orthogonal projection onto $b_1^\perp$. The basis is **quasi-HKZ-reduced** if
--
--   1. it is size-reduced: $|\mu_{j,i}|\le 1/2$ for all $i<j$;
--   2. its tail $(\pi_2(b_2),\dots,\pi_2(b_n))$ is HKZ-reduced;
--   3. the first pair satisfies the LLL condition
--   $$\tfrac34\,a_1^2\le a_2^2+\mu_{2,1}^2a_1^2 .$$
--
--   Every HKZ basis is quasi-HKZ. This is the class of bases whose enumeration trees Theorem 1.1 determines.
--
--   **Formalization Note** Indices are 0-based; with the published Kannan convention $\mathtt{gsCoeff}\ b\ j\ i=\mu_{j,i}a_i$, size reduction reads $|\mathtt{gsCoeff}\ b\ j\ i|\le a_i/2$, and HKZ is the published `KannanLattice.Core.IsReduced`. The predicate is false for $n<2$, where the page does not define it.
-- source:
--   Laarhoven, Asymptotics of Random-Lattice Enumeration: Beyond HKZ via Dense Sublattices, arXiv:2610.15265 (held version, sha256 8fa7a08adef70deb2f23a9a830e01c5a5b031ddaf5e0d4f88ce5174d67214b37), §2.1, (2.4), p.14

import Mathlib
import Definitions.Def_KannanLattice_Core_Lattice
import Definitions.Def_KannanLattice_Core_IsReduced

namespace RandLatEnum.Supplement

open KannanLattice.Core

/-- A **quasi-HKZ-reduced** basis (Laarhoven, *Asymptotics of Random-Lattice Enumeration: Beyond HKZ via Dense Sublattices*, arXiv:2610.15265 (held version, sha256 8fa7a08a…), §2.1, (2.4), p.14, after Hanrot–Stehlé
[28, Definition 2.4]): for `n ≥ 2`, an ordered basis `b = (b_1, …, b_n)` is quasi-HKZ-reduced if
1. it is size-reduced, `|µ_{j,i}| ≤ 1/2` for all `i < j`;
2. its tail `(π_2(b_2), …, π_2(b_n))` is HKZ-reduced, `π_2` the projection orthogonal to `b_1`;
3. `(3/4) a_1² ≤ a_2² + µ_{2,1}² a_1²` (the LLL condition on the first pair), `a_i = ‖b*_i‖`.

**Formalization Note.** Indices are 0-based. With `gsCoeff b j i = µ_{j,i} a_i` (the published
Kannan convention), size reduction reads `|gsCoeff b j i| ≤ gsLen b i / 2` and `µ_{2,1}² a_1²` is
`(gsCoeff b 1 0)²`. The tail is the family `i ↦ projOrth b 1 (b (i+1))` of `n − 1` vectors, and
"HKZ-reduced" is the published `KannanLattice.Core.IsReduced` (size-reduced and `a_i = λ₁(π_i(L))`).
The page defines the notion only for `n ≥ 2`; for `n < 2` the predicate is false. Every HKZ basis
is quasi-HKZ, so this is weaker than `IsReduced`. -/
def IsQuasiHKZ {n k : ℕ} (b : Fin n → EuclideanSpace ℝ (Fin k)) : Prop :=
  ∃ h : 2 ≤ n,
    (∀ i j : Fin n, j < i → |gsCoeff b i j| ≤ gsLen b j / 2) ∧
    IsReduced (fun i : Fin (n - 1) =>
      projOrth b ⟨1, by omega⟩ (b ⟨i.val + 1, by have := i.isLt; omega⟩)) ∧
    (3 / 4 : ℝ) * gsLen b ⟨0, by omega⟩ ^ 2 ≤
      gsLen b ⟨1, by omega⟩ ^ 2 + gsCoeff b ⟨1, by omega⟩ ⟨0, by omega⟩ ^ 2

end RandLatEnum.Supplement


