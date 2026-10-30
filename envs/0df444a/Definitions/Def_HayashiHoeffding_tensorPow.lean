-- Prove2me | Definitions.Def_HayashiHoeffding_tensorPow
-- name    : HayashiHoeffding_tensorPow
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T03:16:12.432654+00:00
-- url     : https://prove2.me/theorems/a3988d62-e3cb-4b9a-bb4f-528b33ccf544
-- title:
--   Hilbert-space tensor power $\mathcal H^{\otimes (k+1)}$
-- statement:
--   For a complex Hilbert space $\mathcal H$ and $k \in \mathbb N$, $\mathcal H^{\otimes (k+1)}$ denotes the Hilbert-space tensor power of $\mathcal H$ with $k+1$ factors (the completed tensor product). It is a complex Hilbert space; $\mathcal H^{\otimes 1} = \mathcal H$ and $\mathcal H^{\otimes (k+2)}$ is the completion of $\mathcal H^{\otimes (k+1)} \otimes \mathcal H$.
--
--   This is the space $\mathcal H^{\otimes n}$, $n = k+1$, of the $n$-copy hypothesis testing problem.
--
--   **Formalization Note** `tensorPow H k` is the carrier of `tensorPowBundle H k`; the paper's number of copies $n$ is $k + 1$.
-- source:
--   Hayashi, Error Exponent in Asymmetric Quantum Hypothesis Testing and Its Application to Classical-Quantum Channel coding, arXiv:quant-ph/0611013v2, "Formulation and main results", p.2

import Mathlib
import Definitions.Def_HayashiHoeffding_tensorPowBundle

namespace HayashiHoeffding

universe u

/-- The Hilbert-space tensor power `H^{⊗(k+1)}` of a complex Hilbert space `H` (the carrier of
`HayashiHoeffding.tensorPowBundle H k`); it is a complex Hilbert space.

Hayashi, arXiv:quant-ph/0611013v2, "Formulation and main results", p.2 (the space `H⊗n`).

**Formalization Note.** `tensorPow H k` is `H^{⊗(k+1)}`: the paper's number of copies `n` is
`k + 1`. `tensorPow H 0 = H` and `tensorPow H (k+1)` is the completion of
`tensorPow H k ⊗[ℂ] H`, both definitionally. -/
abbrev tensorPow (H : Type u) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (k : ℕ) : Type u :=
  (tensorPowBundle H k).carrier

end HayashiHoeffding


