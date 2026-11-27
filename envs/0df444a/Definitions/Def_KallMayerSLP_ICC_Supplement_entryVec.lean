-- Prove2me | Definitions.Def_KallMayerSLP_ICC_Supplement_entryVec
-- name    : KallMayerSLP_ICC_Supplement_entryVec
-- status  : Definition
-- author  : @iris
-- created : 2026-11-27T02:38:45.983496+00:00
-- url     : https://prove2.me/theorems/33c18f64-84fc-541a-98b5-15289a67f81b
-- title:
--   The vector $\zeta$ of all random entries of $(T(\xi),h(\xi))$ in column major order
-- statement:
--   With the columns $\zeta^{(1)},\dots,\zeta^{(n+1)}\in\mathbb R^s$ of the augmented matrix $(T(\xi),h(\xi))$, the vector of all random entries in column major order is
--   $$
--   \zeta=\big(\zeta^{(1)\mathrm T},\dots,\zeta^{(n+1)\mathrm T}\big)^{\mathrm T}\in\mathbb R^{(n+1)s}.
--   $$
--   Joint normality in Prékopa's theorem is an assumption on the law of this one vector, not on its columns or rows separately.
--
--   **Formalization Note** The entry in row $i$ and column $j$ (both $0$-based) is coordinate $i+sj$ of the vector, via `finProdFinEquiv`.
-- source:
--   Kall & Mayer, Stochastic Linear Programming (2005), Chapter 2, §2.6, p.137 (PDF 147)

import Mathlib
import Definitions.Def_KallMayerSLP_ICC_Supplement_augMatrix

open Matrix

namespace KallMayerSLP.ICC.Supplement

/-- **The vector `ζ` of all random entries of `(T(ξ), h(ξ))`, in column major order.**
Kall & Mayer, *Stochastic Linear Programming* (2005), Chapter 2, §2.6, p.137 (PDF 147):
"Let `ζᵀ = (ζ^(1)ᵀ, …, ζ^(n+1)ᵀ)` be the random vector consisting of all random entries in
columns major order."

**Formalization Note.** The entry in row `i : Fin s` and column `j : Fin (n + 1)` of
`augMatrix T h ξ` sits at position `finProdFinEquiv (j, i) = i + s * j` of a vector in
`ℝ^{(n+1)s}` (index base `0`). -/
def entryVec {Ξ : Type*} {s n : ℕ} (T : Ξ → Matrix (Fin s) (Fin n) ℝ) (h : Ξ → Fin s → ℝ)
    (ξ : Ξ) : Fin ((n + 1) * s) → ℝ :=
  fun k => augMatrix T h ξ (finProdFinEquiv.symm k).2 (finProdFinEquiv.symm k).1

end KallMayerSLP.ICC.Supplement


