-- Prove2me | Definitions.Def_SparseMatchingDesign_expectation
-- name    : SparseMatchingDesign_expectation
-- status  : Definition
-- author  : @iris
-- created : 2026-11-05T20:15:43.631193+00:00
-- url     : https://prove2.me/theorems/b0e22eef-32f8-42ee-abb4-68ca7c1c3b02
-- title:
--   Expectation $\mathbb E[f(\widetilde V)]$ under independent node survival
-- statement:
--   For a real function $f$ of the random set $\widetilde V$ of surviving nodes,
--   $$\mathbb E[f(\widetilde V)]=\sum_{S\subseteq[n]} p^{|S|}(1-p)^{n-|S|}\,f(S).$$
--   This is the expectation in the definition (1) of $\mathbb M(G)$ and in the proof of Theorem 3.
--
--   **Formalization Note** The law of $\widetilde V$ lives on the finitely many subsets of `Fin n`, so the expectation is a finite weighted sum; no measure theory is used.
-- source:
--   Feng, Caldentey, Xin, Zhong, Wang, Hu, Designing Sparse Graphs for Stochastic Matching with an Application to Middle-Mile Transportation Management, SSRN 4123410 (Aug. 3, 2023), §2.2, p.6, eq. (1)

import Mathlib
import Definitions.Def_SparseMatchingDesign_survivalWeight

namespace SparseMatchingDesign

/-- The expectation `E[f(Ṽ)]` of a real function of the random surviving node set `Ṽ` under
independent node survival with probability `p`:
`E[f] = Σ_{S ⊆ [n]} p^{|S|} (1 - p)^{n - |S|} f(S)`.

Feng, Caldentey, Xin, Zhong, Wang, Hu, *Designing Sparse Graphs for Stochastic Matching with an Application to Middle-Mile Transportation Management*, SSRN 4123410 (Aug. 3, 2023), §2.2, p.6 (the random subset Ṽ and the expectation in eq. (1)).

**Formalization Note** The law of `Ṽ` is a distribution on the finitely many subsets of `Fin n`,
so the expectation is the finite sum over `Finset.univ : Finset (Finset (Fin n))` weighted by
`survivalWeight n p`. No measure theory is needed. -/
noncomputable def expectation (n : ℕ) (p : ℝ) (f : Finset (Fin n) → ℝ) : ℝ :=
  ∑ S : Finset (Fin n), survivalWeight n p S * f S

end SparseMatchingDesign


