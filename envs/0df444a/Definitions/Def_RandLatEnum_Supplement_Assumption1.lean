-- Prove2me | Definitions.Def_RandLatEnum_Supplement_Assumption1
-- name    : RandLatEnum_Supplement_Assumption1
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T08:01:28.110982+00:00
-- url     : https://prove2.me/theorems/fb504053-56fd-4d48-b782-a3dacf7bff64
-- title:
--   Assumption 1 (first-moment sufficiency), precise form
-- statement:
--   Fix $r\ge 2$, rank fractions $0=x_0<x_1<\dots<x_r=1$ and determinant exponents $h_0=h_r=0,h_1,\dots,h_{r-1}$, independently of $n$. **Assumption 1** asserts: if some fixed $\delta>0$ satisfies
--   $$\min_{\emptyset\ne J\subseteq\{1,\dots,r-1\}}\mathbb E_{\mu_n}\big[C_{J,n}(L)\big]\ \ge\ n^{\delta n^2}$$
--   for all sufficiently large $n$, then $\Pr_{L\sim\mu_n}\{C_n(L)>0\}=1-o(1)$.
--
--   It is the heuristic hypothesis of Theorem 1.4. The condition is imposed on every nonempty subchain, since a large full-chain average alone may hide a rank at which suitable partial chains are unlikely to exist.
--
--   **Formalization Note** A proposition about the family of measures $\mu=(\mu_n)$, used as a hypothesis. Expectations are lower Lebesgue integrals of the $\mathbb N\cup\{\infty\}$-valued counts, as in the published Eq. (7.3); "$\Pr\{C_n>0\}=1-o(1)$" is written $\mu_n\{C_n(L)=0\}\to0$.
-- source:
--   Laarhoven, Asymptotics of Random-Lattice Enumeration: Beyond HKZ via Dense Sublattices, arXiv:2610.15265 (held version, sha256 8fa7a08adef70deb2f23a9a830e01c5a5b031ddaf5e0d4f88ce5174d67214b37), §6, (6.2)–(6.3), p.26

import Mathlib
import Definitions.Def_RandLatEnum_X
import Definitions.Def_RandLatEnum_latticeOf
import Definitions.Def_RandLatEnum_Supplement_prescribedChainCount
import Definitions.Def_RandLatEnum_Supplement_partialChainCount

namespace RandLatEnum.Supplement

open MeasureTheory Filter Topology RandLatEnum
open scoped ENNReal

/-- **Assumption 1 (first-moment sufficiency), precise form** (Laarhoven, *Asymptotics of Random-Lattice Enumeration: Beyond HKZ via Dense Sublattices*, arXiv:2610.15265 (held version, sha256 8fa7a08a…), §6, (6.2)–(6.3), p.26).
Fix `r ≥ 2`, rank fractions `0 = x_0 < ⋯ < x_r = 1` and determinant exponents
`h_0 = h_r = 0, h_1, …, h_{r−1}`, independently of `n`. If some fixed `δ > 0` satisfies
`min_{∅ ≠ J ⊆ {1,…,r−1}} E_{µ_n}[C_{J,n}(L)] ≥ n^{δ n²}` for all sufficiently large `n`, then
`P{C_n(L) > 0} = 1 − o(1)`.

**Formalization Note.** A `Prop` about the family `μ` (meant: the Haar measures `µ_n`), passed to
Theorem 1.4 as a hypothesis. `J` ranges over nonempty finsets of `Fin (r+1)` avoiding `0` and `r`;
the minimum is "for every such `J`". Expectations are lower Lebesgue integrals `∫⁻` of the
`ℕ∞`-valued counts, as in the published `eq_7_3`; `n^{δn²}` enters through `ENNReal.ofReal`.
"`P{C_n > 0} = 1 − o(1)`" is written as `µ_n{C_n(L) = 0} → 0` (equivalent for a measurable count). -/
def Assumption1 (μ : ∀ n : ℕ, Measure (X n)) : Prop :=
  ∀ (r : ℕ) (xs hs : Fin (r + 1) → ℝ), 2 ≤ r → xs 0 = 0 → xs (Fin.last r) = 1 → StrictMono xs →
    hs 0 = 0 → hs (Fin.last r) = 0 →
    (∃ δ : ℝ, 0 < δ ∧ ∀ᶠ n : ℕ in atTop, ∀ J : Finset (Fin (r + 1)), J.Nonempty → 0 ∉ J →
      Fin.last r ∉ J →
        ENNReal.ofReal ((n : ℝ) ^ (δ * (n : ℝ) ^ 2)) ≤
          ∫⁻ x, ((partialChainCount n r xs hs J (latticeOf x) : ℕ∞) : ℝ≥0∞) ∂μ n) →
    Tendsto (fun n : ℕ => μ n {x : X n | prescribedChainCount n r xs hs (latticeOf x) = 0})
      atTop (𝓝 0)

end RandLatEnum.Supplement


