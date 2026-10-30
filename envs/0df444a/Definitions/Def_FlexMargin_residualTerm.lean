-- Prove2me | Definitions.Def_FlexMargin_residualTerm
-- name    : FlexMargin_residualTerm
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-30T03:39:36.995814+00:00
-- url     : https://prove2.me/theorems/dbc6eb26-1e8f-4a93-9329-35217fa3fce8
-- title:
--   The residual term of (7)
-- statement:
--   For a parameter set $K$, let $H_{tr}=\sum_{j=0}^{r}k_{tj}$. For a residual vector $\varepsilon\in\mathbb R^n$ write $\varepsilon_{s_t,1},\varepsilon_{s_t,2},\dots$ for its entries on the category $S_t$. The **residual term** of (7) is
--
--   $$
--   \sum_{t=1}^T\sum_{r=0}^{t-1}\beta_{tr}\sum_{i=H_{tr}-k_{tr}+1}^{H_{tr}}\varepsilon_{s_t,i}.
--   $$
--
--   It is the change in the dual objective when the demand moves from $\mu$ to $\mu+\varepsilon$ and the products at price level $\beta_{tr}$ are those in the given positions.
--
--   **Formalization Note** The entries of $\varepsilon$ on $S_t$ are listed in increasing order of the product index; the paper does not fix this order, and for part-wise symmetric sets it does not affect (7).
-- source:
--   Wang, Wang and Zhang, Robust Optimization Approach to Process Flexibility Designs with Contribution Margin Differentials, SSRN 3233721 (version of 2020-05-22), §3.2, p. 18, and Appendix A, Proposition 3, display (7), p. 41

import Mathlib
import Definitions.Def_FlexMargin_betaCoef

open Finset

namespace FlexMargin

/-- **The residual term `Σ_t Σ_{r<t} β_{tr} Σ_{i=H_{tr}−k_{tr}+1}^{H_{tr}} ε_{s_t,i}` of (7) and Theorem 1.**
Wang, Wang and Zhang, *Robust Optimization Approach to Process Flexibility Designs with
Contribution Margin Differentials*, SSRN 3233721 (version of 2020-05-22), §3.2, p. 18: "let Htr := Σ_{j=0}^r ktj for all 1 ≤ t ≤ T, 0 ≤ r ≤ t − 1", and Proposition 3,
display (7), p. 41: "Σ_{t=1}^T ( Σ_{r=0}^{t−1} βtr ( Σ_{i=Htr−ktr+1}^{Htr} ϵst,i ) ), where ϵst := dst − µst
denotes the vector of demand residuals for each product category St."

For a residual vector `ε : Fin n → ℝ`, the subvector `ε_{s_t}` lists the entries of `ε` on the
category `S_t = {i | cat i = t}` in increasing order of the product index (`Finset.orderEmbOfFin`).
For each category `t` and level `r ≤ t` (0-based, see `FlexMargin.InQ`), the term adds
`β_{t r}` (`FlexMargin.betaCoef`) times the sum of the entries of `ε_{s_t}` at the 0-based positions
`q` with `Σ_{j<r} K t j ≤ q < Σ_{j≤r} K t j` (the paper's 1-based positions `H_{tr} − k_{tr} + 1, …,
H_{tr}`).

**Formalization Note.** The paper writes `ε_{s_t,i}` without fixing the order of `s_t` (for
part-wise symmetric sets the order does not change the infimum in (7)); the increasing order of
product indices is fixed here. For `K ∈ Q` all positions are `< |S_t|`. -/
noncomputable def residualTerm {n T : ℕ} (P : Fin T → ℝ) (cat : Fin n → Fin T)
    (K : (t : Fin T) → Fin (t.val + 1) → ℕ) (ε : Fin n → ℝ) : ℝ :=
  ∑ t : Fin T, ∑ r : Fin (t.val + 1), betaCoef P t r.val *
    ∑ q : Fin (univ.filter (fun i => cat i = t)).card,
      if (∑ j ∈ univ.filter (fun j : Fin (t.val + 1) => j.val < r.val), K t j) ≤ q.val ∧
          q.val < ∑ j ∈ univ.filter (fun j : Fin (t.val + 1) => j.val ≤ r.val), K t j
      then ε ((univ.filter (fun i => cat i = t)).orderEmbOfFin rfl q) else 0

end FlexMargin


