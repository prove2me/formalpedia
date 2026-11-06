-- Prove2me | Definitions.Def_MatchedUCLB_objPhase
-- name    : MatchedUCLB_objPhase
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T01:39:32.136765+00:00
-- url     : https://prove2.me/theorems/e1f2ccca-c2e5-4100-97a9-07656354fc81
-- title:
--   The phase functions $A_j$ of the complete objective
-- statement:
--   For $0\le j<L$, the **phase function** $A_j$ of the complete objective is the phase function with coefficient $\lambda=K\mu m^{a_q}$, scale $\tau_j$, base increment norm $G_j$, center $c_j$, directions $v_j,u_{j,1},\dots,u_{j,m}$, and next-phase data $(v_{j+1},s_{j+1})$ when $j<L-1$. For the terminal phase $j=L-1$ the next coordinate is omitted and $s_L=t^\star_L=0$.
--
--   **Formalization Note** The complete objective depends on $q=p+\nu$, $\mu$, the chain length $m$, the number of phases $L$, the initial scale $\tau_0$ and a phase frame $(v,u)$; the constants $K$ and $\eta$ are fixed as in Lemma 4.5. Phase directions are sequences indexed by $j\in\mathbb N$, of which only $j<L$ enter. The terminal phase uses next direction $0$ and next slope $0$.
-- source:
--   Bai, Tight Lower Bounds under Matched High-Order Hölder Smoothness and Uniform Convexity, arXiv:2611.05527, Definition E.8, pp.89–90; Sec. 4.3, p.9

import Mathlib
import Definitions.Def_MatchedUCLB_objSlope
import Definitions.Def_MatchedUCLB_objCenter
import Definitions.Def_MatchedUCLB_phaseA

namespace MatchedUCLB

/-- **The phase functions `A_j` of the complete objective.** Bai, *Tight Lower Bounds under Matched High-Order Hölder Smoothness and Uniform Convexity*, arXiv:2611.05527, Definition E.8, pp.89–90, with
the parameters of Definition E.1: phase `j` is the phase function with `λ`, `τ_j`, `G_j`, center
`c_j`, directions `v_j, u_{j,·}`, and next-phase data `(v_{j+1}, s_{j+1})` for `j < L − 1`. For the
terminal phase `j = L − 1` "we omit `t_L`, `v_L` and set `s_L = t⋆_L = 0`, with `s_L v_L := 0`" (p.9).

**Formalization Note.** The terminal phase is encoded by `vN = 0`, `sN = 0`.

**Formalization Note.** The parameters of the complete objective are `q = p + ν`, `μ`, the chain
length `m`, the number of phases `L`, the initial scale `τ₀` and a phase frame `(v, u)`; `K` and
`η` are fixed as in Lemma 4.5 (`KConst q`, `eta q`). -/
noncomputable def objPhase (q μ : ℝ) {d m : ℕ} (L : ℕ) (τ₀ : ℝ) (v : ℕ → EuclideanSpace ℝ (Fin d)) (u : ℕ → Fin m → EuclideanSpace ℝ (Fin d))
    (j : ℕ) (x : EuclideanSpace ℝ (Fin d)) : ℝ :=
  if j + 1 < L then
    phaseA q (objLam q μ m) (objTau q τ₀ j) (objG q μ τ₀ v u j) (objSlope q μ τ₀ v u (j + 1))
      (objCenter q τ₀ v u j) (v j) (v (j + 1)) (u j) x
  else
    phaseA q (objLam q μ m) (objTau q τ₀ j) (objG q μ τ₀ v u j) 0
      (objCenter q τ₀ v u j) (v j) 0 (u j) x

end MatchedUCLB


