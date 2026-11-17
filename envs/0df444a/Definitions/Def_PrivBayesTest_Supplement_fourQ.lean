-- Prove2me | Definitions.Def_PrivBayesTest_Supplement_fourQ
-- name    : PrivBayesTest_Supplement_fourQ
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T08:11:14.330435+00:00
-- url     : https://prove2.me/theorems/781e1439-7074-4718-94e3-2140c1c16f6d
-- title:
--   The four-community SBM instance of Theorem 4.8
-- statement:
--   The instance of §4.2.3 has four communities $c_1,c_2,c_3,c_4$, each with prior probability $1/4$, and connection matrix
--
--   $$Q=4\begin{bmatrix}K&0&L&0\\0&2K&0&L\\L&0&0&0\\0&L&0&0\end{bmatrix}$$
--
--   for real parameters $K,L$, so that the community profiles are $\theta_1=(K,0,L,0)$, $\theta_2=(0,2K,0,L)$, $\theta_3=(L,0,0,0)$, $\theta_4=(0,L,0,0)$. The model is $\mathrm{SBM}(n,p,\log(n)Q/n)$.
--
--   This is the counterexample to Conjecture 1.6 constructed in Theorem 4.8.
--
--   **Formalization Note** The communities $c_1,\dots,c_4$ are $0,\dots,3$ in $\mathrm{Fin}\,4$.
-- source:
--   Jacobsen, Optimal Error Exponents for Private Bayesian Hypothesis Testing, STOC 2027 submission (manuscript sha256 abff2fdd66827f43…124ef), §4.2.3, p.20

import Mathlib

namespace PrivBayesTest

namespace Supplement

/-- The uniform prior `p = (1/4, 1/4, 1/4, 1/4)` of the four-community instance (Jacobsen,
*Optimal Error Exponents for Private Bayesian Hypothesis Testing*, STOC 2027 submission
(manuscript sha256 abff2fdd…124ef), §4.2.3, p.20: "four communities, each with probability 1/4"). -/
noncomputable def fourP : Fin 4 → ℝ := fun _ => 1 / 4

/-- The connection matrix of the four-community instance (Jacobsen, STOC 2027 submission
(manuscript sha256 abff2fdd…124ef), §4.2.3, p.20):

`Q = 4 · [[K, 0, L, 0], [0, 2K, 0, L], [L, 0, 0, 0], [0, L, 0, 0]]`,

so that, with `p` uniform, the profiles are `θ₁ = (K, 0, L, 0)`, `θ₂ = (0, 2K, 0, L)`,
`θ₃ = (L, 0, 0, 0)`, `θ₄ = (0, L, 0, 0)`. The communities `c₁, …, c₄` are `0, …, 3 : Fin 4`. -/
def fourQ (K L : ℝ) : Matrix (Fin 4) (Fin 4) ℝ :=
  4 • !![K, 0, L, 0;
         0, 2 * K, 0, L;
         L, 0, 0, 0;
         0, L, 0, 0]

end Supplement

end PrivBayesTest


