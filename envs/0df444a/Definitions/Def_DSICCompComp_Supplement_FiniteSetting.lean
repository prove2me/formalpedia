-- Prove2me | Definitions.Def_DSICCompComp_Supplement_FiniteSetting
-- name    : DSICCompComp_Supplement_FiniteSetting
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T14:23:08.289401+00:00
-- url     : https://prove2.me/theorems/8f2bbd83-ff12-45f4-bd4d-27e028c78fcd
-- title:
--   Finite-support setting of the DSIC duality framework
-- statement:
--   The duality framework of Appendix C considers $n$ bidders and $m$ items, where bidder $i$ draws her value vector $v_i = (v_{i1}, \dots, v_{im})$ from a distribution $D_i$ with finite support $\mathrm{supp}(D_i) = S_i$ and probability mass function $f_i$, positive on $S_i$ with $\sum_{v_i \in S_i} f_i(v_i) = 1$. Bidders are independent (not necessarily identical), so the value profile has law $D = \times_i D_i$ with support $\mathrm{supp}(D) = \times_i S_i$.
--
--   **Formalization Note** Bidders are `Fin n` and items `Fin m`. Each $S_i$ is a finite set of real vectors and $f_i$ is an arbitrary positive PMF on it: the page's $D_i = \times_j D_{ij}$ (independent items within a bidder) and nonnegativity of values are not imposed, since nothing in the framework uses them.
-- source:
--   Ryu–Weinberg–Xue, The DSIC Competition Complexity of Additive Buyers over Independent Items, STOC 2027 submission (manuscript of Nov. 3, 2026, sha256 bf61bfdb…), Appendix C, pp.34–35 (pdf pp.35–36) and footnote 15

import Mathlib

namespace DSICCompComp

namespace Supplement

/-- The finite-support setting of the DSIC duality framework (Ryu–Weinberg–Xue, *The DSIC Competition Complexity of Additive Buyers over Independent Items*, STOC 2027
submission, manuscript of Nov. 3, 2026, sha256 bf61bfdb…,
Appendix C, pp.34–35 (pdf pp.35–36) and footnote 15): `n` bidders and `m` items; bidder `i`'s value
vector `v_i = (v_i1, …, v_im)` is drawn from a distribution `D_i` with finite support
`supp(D_i) = S i` and PMF `f_i = f i`, positive on `S i` and summing to `1`; bidders are
independent, so the value profile has law `D = ×_i D_i` (see `jointPMF`).

**Formalization Note** Bidders are `Fin n` and items `Fin m` (0-based). Values are real vectors and
`f_i` is an arbitrary positive PMF on the finite set `S i`; the page's `D_i = ×_j D_ij`
(independent items within a bidder) and nonnegative values are not imposed. -/
structure FiniteSetting (n m : ℕ) where
  /-- `supp(D_i)`, the finite set of bidder `i`'s possible value vectors. -/
  S : Fin n → Finset (Fin m → ℝ)
  /-- `f_i`, the PMF of `D_i` on `supp(D_i)`. -/
  f : (i : Fin n) → S i → ℝ
  f_pos : ∀ i v, 0 < f i v
  f_sum : ∀ i, ∑ v, f i v = 1

end Supplement

end DSICCompComp


