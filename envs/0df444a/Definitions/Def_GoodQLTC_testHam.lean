-- Prove2me | Definitions.Def_GoodQLTC_testHam
-- name    : GoodQLTC_testHam
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T07:40:41.459779+00:00
-- url     : https://prove2.me/theorems/3330aee1-3382-451c-8eaf-4b23ec4699e0
-- title:
--   Testing Hamiltonian $H=\frac1m\sum_j\frac{I-g_j}{2}$
-- statement:
--   For the full list $\{g_j\}_{j\in[m]}$ of CSS checks ($m_X$ checks $X^{h^X_a}$ and $m_Z$ checks $Z^{h^Z_b}$, $m=m_X+m_Z\ge1$), the **testing Hamiltonian** is
--   $$
--   H=\frac1m\sum_{j=1}^m\frac{I-g_j}{2}. \tag{3.1}
--   $$
--   For a state $\varrho$, $\mathrm{Tr}(\varrho H)$ is the rejection probability of the test that samples a listed check uniformly.
--
--   **Formalization Note** Every row of $H_X$ and $H_Z$ contributes one check, including zero and repeated rows (p.18). At $m=0$ the matrix is $0$; the paper assumes $m\ge1$.
-- source:
--   Gay, Jeronimo, Asymptotically Good Quantum Locally Testable Codes, arXiv:2609.20780 (held version, sha256 04ad03ca…), §3.3, Equation (3.1), p.14 (PDF p.17)

import Mathlib
import Definitions.Def_GoodQLTC_pauliX

namespace GoodQLTC

/-- The **testing Hamiltonian** `H := (1/m) ∑_{j=1}^m (I − g_j)/2` of a CSS code with its full
check list, Gay–Jeronimo, arXiv:2609.20780 (held version), §3.3, Equation (3.1), p.14. The list
`{g_j}` consists of the `m_X` checks `X^{h^X_a}` and the `m_Z` checks `Z^{h^Z_b}`, one per row,
and `m = m_X + m_Z`.

**Formalization Note.** Every row of `H_X` and `H_Z` contributes one check, including zero and
repeated rows (p.18). The paper assumes `m ≥ 1`; at `m = 0` this definition is `0`. -/
noncomputable def testHam {ι κX κZ : Type} [Fintype ι] [DecidableEq ι] [Fintype κX] [Fintype κZ]
    (HX : Matrix κX ι (ZMod 2)) (HZ : Matrix κZ ι (ZMod 2)) :
    Matrix (ι → ZMod 2) (ι → ZMod 2) ℂ :=
  ((1 : ℂ) / ((Fintype.card κX + Fintype.card κZ : ℕ) : ℂ)) •
    ((∑ a : κX, ((1 : ℂ) / 2) • (1 - pauliX (HX a))) +
      ∑ b : κZ, ((1 : ℂ) / 2) • (1 - pauliZ (HZ b)))

end GoodQLTC


