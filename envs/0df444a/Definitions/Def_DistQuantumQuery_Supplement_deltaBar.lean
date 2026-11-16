-- Prove2me | Definitions.Def_DistQuantumQuery_Supplement_deltaBar
-- name    : DistQuantumQuery_Supplement_deltaBar
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T00:46:19.790206+00:00
-- url     : https://prove2.me/theorems/4611ae5d-1ef6-490d-bb8e-e1cd25627f88
-- title:
--   Filtered $\delta_2$ measure $\bar\delta^\mu_2(A,B\mid\{S_i\})$
-- statement:
--   Let $\Sigma\subseteq\{0,1\}^n$ with sign filters $\{S_i\}$, let $A,B$ be positive semidefinite on $\Sigma$, and let $\mu$ be a distribution on $\Sigma$. The **filtered $\delta_2$ measure** is
--   $$
--   \bar\delta^\mu_2(A,B\mid\{S_i\}):=\sup_{c>1}\frac{-2\log F_c\big(A\circ|\mu\rangle\langle\mu|,\,B\circ|\mu\rangle\langle\mu|\mid\{S_i\}\big)}{\log c},
--   $$
--   with the convention that its value is $+\infty$ if the filtered fidelity vanishes for some $c>1$.
--
--   It measures the ratio of log-distinguishability to log per-query cost and is the multiplicative analogue of $\bar\gamma^\mu_2$; it tensorizes exactly, which drives the XOR lemma and the direct-product theorem.
--
--   **Formalization Note** The value lies in the extended reals: the footnote's $+\infty$ is $\top$, and the supremum over real $c>1$ is taken in the extended reals. The base of the logarithm cancels in the ratio; the natural logarithm is used.
-- source:
--   Ben-David, Ebtehaj, Distributional Quantum Query Complexity, arXiv:2610.06835 (held version, sha256 6334ffaf…), Definition 8.4 and footnote 9, p.71

import Mathlib
import Definitions.Def_DistQuantumQuery_muMat
import Definitions.Def_DistQuantumQuery_Supplement_filteredFidelity

open scoped Matrix ComplexOrder

namespace DistQuantumQuery.Supplement

open DistQuantumQuery

open Classical in
/-- The **filtered δ₂ measure** (Ben-David, Ebtehaj, *Distributional Quantum Query Complexity*,
arXiv:2610.06835, held version, sha256 6334ffaf…, Definition 8.4 with footnote 9, p.71): for
`Σ ⊆ {0,1}^n` with sign filters `{S_i}`, PSD `A, B` and a distribution `μ`,
`δ̄^μ₂(A, B | {S_i}) := sup_{c > 1} −2 log F_c(A ∘ |μ⟩⟨μ|, B ∘ |μ⟩⟨μ| | {S_i}) / log c`,
and `+∞` if the filtered fidelity vanishes for some `c > 1` (footnote 9).

**Formalization Note** Value in `EReal`: the footnote's `+∞` is `⊤`, otherwise the supremum over
real `c > 1` is taken in `EReal` (so an unbounded supremum is `⊤`). The sign filters of `Σ`
(`signFilters S`) are built in, as in Definition 8.4. The logarithm is `Real.log`; the paper's
`log = log₂` cancels in the ratio. `|μ⟩⟨μ|` is the base mission's `muMat`. -/
noncomputable def deltaBar {ι : Type*} (S : Finset (ι → Bool)) (μ : S → ℝ)
    (A B : Matrix S S ℂ) : EReal :=
  if ∃ c : ℝ, 1 < c ∧ filteredFidelity c (A ⊙ muMat μ) (B ⊙ muMat μ) (signFilters S) = 0 then ⊤
  else ⨆ c : {c : ℝ // 1 < c},
    (((-2 * Real.log (filteredFidelity c.1 (A ⊙ muMat μ) (B ⊙ muMat μ) (signFilters S))) /
      Real.log c.1 : ℝ) : EReal)

end DistQuantumQuery.Supplement


