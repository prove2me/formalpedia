-- Prove2me | Definitions.Def_MatchedUCLB_objSlope
-- name    : MatchedUCLB_objSlope
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T01:37:45.500719+00:00
-- url     : https://prove2.me/theorems/56722a2b-8841-4c49-8800-3a753abdc854
-- title:
--   The starting slopes $s_j$ of the complete objective
-- statement:
--   The **starting slopes** of the complete objective are
--
--   $$
--   s_j=\Gamma_j+\frac{G_jt^\star_j}{R_j},\qquad \Gamma_j=\frac{\lambda\tau_j^{q-1}}{\sqrt m},
--   $$
--
--   for $0\le j<L$ (and $s_L=0$).
--
--   **Formalization Note** The complete objective depends on $q=p+\nu$, $\mu$, the chain length $m$, the number of phases $L$, the initial scale $\tau_0$ and a phase frame $(v,u)$; the constants $K$ and $\eta$ are fixed as in Lemma 4.5. Phase directions are sequences indexed by $j\in\mathbb N$, of which only $j<L$ enter. The terminal convention $s_L=0$ is built into the phase functions.
-- source:
--   Bai, Tight Lower Bounds under Matched High-Order Hölder Smoothness and Uniform Convexity, arXiv:2611.05527, Definition E.1, p.83; Eq. (4.11), p.8

import Mathlib
import Definitions.Def_MatchedUCLB_objG
import Definitions.Def_MatchedUCLB_objLam
import Definitions.Def_MatchedUCLB_slope

namespace MatchedUCLB

/-- **The starting slopes `s_j` of the complete objective.** Bai, *Tight Lower Bounds under Matched High-Order Hölder Smoothness and Uniform Convexity*, arXiv:2611.05527, Definition E.1, p.83:
"`Γ_j := λτ_j^{q−1}/√m`, `s_j := Γ_j + G_j t⋆_j / R_j`" (Eq. (4.11)).

**Formalization Note.** The formula is used for `j < L`; the terminal convention `s_L = 0` is
built into `objPhase`.

**Formalization Note.** The parameters of the complete objective are `q = p + ν`, `μ`, the chain
length `m`, the number of phases `L`, the initial scale `τ₀` and a phase frame `(v, u)`; `K` and
`η` are fixed as in Lemma 4.5 (`KConst q`, `eta q`). -/
noncomputable def objSlope (q μ : ℝ) {d m : ℕ} (τ₀ : ℝ) (v : ℕ → EuclideanSpace ℝ (Fin d)) (u : ℕ → Fin m → EuclideanSpace ℝ (Fin d)) (j : ℕ) : ℝ :=
  slope q (objLam q μ m) (objTau q τ₀ j) (objG q μ τ₀ v u j) (v j) (u j)

end MatchedUCLB


