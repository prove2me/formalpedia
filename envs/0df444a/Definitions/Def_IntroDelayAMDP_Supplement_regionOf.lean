-- Prove2me | Definitions.Def_IntroDelayAMDP_Supplement_regionOf
-- name    : IntroDelayAMDP_Supplement_regionOf
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T07:47:04.525881+00:00
-- url     : https://prove2.me/theorems/7d094ef8-aa67-45be-a561-b826bd9f04f1
-- title:
--   The region containing a feature
-- statement:
--   Given the regions $C_1,C_2,\dots$ of a layer, where
--   $$C_j=\{\phi\in\mathbb R^d:\|\phi\|^2_{\Lambda_j^{-1}}\le 2d\log(1+1/\lambda)\}\setminus(C_1\cup\dots\cup C_{j-1}),$$
--   this returns the index $j$ with $\phi\in C_j$, or nothing if $\phi$ lies in no region. Since each region removes the earlier ones, $\phi\in C_j$ exactly when the $j$-th ellipsoid is the first one containing $\phi$. Here $\|x\|^2_M=x^\top Mx$.
--
--
--   **Formalization Note** Indices are $0$-based.
-- source:
--   Kulkarni–Nguyen–Chang–Dai, Introducing Feedback Delays to Non-Delayed Adversarial MDPs, STOC 2027 submission (manuscript sha256 a639c54c…5e3530), Algorithm 2, line 6, p.17

import Mathlib
import Definitions.Def_IntroDelayAMDP_Supplement_Region

namespace IntroDelayAMDP.Supplement

open Matrix

open Classical in
/-- **The region containing a feature** (Algorithm 2, line 6, printed p.17, PDF p.19, of
Kulkarni–Nguyen–Chang–Dai, *Introducing Feedback Delays to Non-Delayed Adversarial MDPs*, STOC 2027 submission (manuscript sha256 a639c54c…5e3530): "Let `C_j ← {ϕ ∈ ℝ^d : ‖ϕ‖²_{Λ_j^{-1}} ≤ 2d log(1 + 1/λ)} \ (C₁ ∪ ⋯ ∪ C_{j−1})` be the `j`-th region").
For the list of regions `regs` of a layer and `r = 2d log(1 + 1/λ)`, `regionOf regs r ϕ = some j` iff
`ϕ ∈ C_j` (0-based `j`), and `none` iff `ϕ` lies in no region. As the `C_j` are the ellipsoids minus all
earlier ones, `ϕ ∈ C_j` iff the `j`-th ellipsoid is the first one containing `ϕ`.
`‖ϕ‖²_{M} = ϕᵀMϕ` (Notation, printed p.12) and `Λ_j^{-1}` is the matrix inverse (`Λ_j ≽ λI`, `λ > 0`). -/
noncomputable def regionOf {d : ℕ} (regs : List (Region d)) (r : ℝ) (ϕ : Fin d → ℝ) : Option ℕ :=
  regs.findIdx? (fun R => decide (ϕ ⬝ᵥ (R.lam⁻¹ *ᵥ ϕ) ≤ r))

end IntroDelayAMDP.Supplement


