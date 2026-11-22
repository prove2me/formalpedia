-- Prove2me | Definitions.Def_AvgPHETH_Supplement_PiPO
-- name    : AvgPHETH_Supplement_PiPO
-- status  : Definition
-- author  : @iris
-- created : 2026-11-22T04:25:23.024867+00:00
-- url     : https://prove2.me/theorems/a3d70f6a-df53-4286-9fd6-88d3cd2a2de6
-- title:
--   The class $\Pi_k^{p,O}$
-- statement:
--   For an oracle $O$ and $k\ge0$, $\Pi_k^{p,O}$ is the class of languages $L$ whose complement $\overline L$ belongs to $\Sigma_k^{p,O}$. Equivalently, $x\in L$ iff $\forall y_1\,\exists y_2\cdots Q_ky_k\;V(x,y_1,\dots,y_k)$ for a verifier $V$ running in polynomial time with oracle $O$ and moves of polynomial length.
--
--   $$\Pi_k^{p,O}=\{L:\overline L\in\Sigma_k^{p,O}\}.$$
--
--   This is the class of the hard languages $L_k^O$ in the oracle barrier (Theorems 1.5 and 8.7).
--
--   **Formalization Note** $\Sigma_k^{p,O}$ is the published `AvgPHETH.SigmaPO`.
-- source:
--   Hirahara–Juvekar–Nanashima, Average-Case Hardness of PH from ETH-Type Hypotheses, manuscript of November 3, 2026 (STOC 2027 submission; held version sha256 ea5fd472…), Theorem 1.5, p.4 (PDF 6); §8.1, p.38 (PDF 40)

import Mathlib
import Definitions.Def_AvgPHETH_SigmaPO

namespace AvgPHETH.Supplement

open AvgPHETH

/-- The class `Π_k^{p,O}`: languages whose complement is in `Σ_k^{p,O}`, i.e. languages with
`x ∈ L ⟺ ∀y₁ ∃y₂ ⋯ Q_k y_k V(x, y₁, …, y_k)` for a polynomial-time verifier `V` with oracle `O`
(Hirahara–Juvekar–Nanashima, *Average-Case Hardness of PH from ETH-Type Hypotheses*, manuscript of November 3, 2026 (STOC 2027 submission; held version sha256 ea5fd472…), Theorem 1.5, p.4 (PDF 6); §8.1, p.38 (PDF 40)).

**Formalization Note** `Σ_k^{p,O}` is the published `AvgPHETH.SigmaPO`; a polynomial-time verifier
can be negated, so complementing the language is the same as starting the quantifiers with `∀`. -/
def PiPO (O : Set (List Bool)) (k : ℕ) : Set (Set (List Bool)) :=
  {L | Lᶜ ∈ SigmaPO O k}

end AvgPHETH.Supplement


