-- Prove2me | Definitions.Def_MatchedUCLB_objective
-- name    : MatchedUCLB_objective
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T01:42:01.60344+00:00
-- url     : https://prove2.me/theorems/b26228a9-108d-40e7-aad8-261754dfd9a6
-- title:
--   The complete objective $F=B+\ell_{\mathrm{init}}+\sum_jA_j$
-- statement:
--   The **complete objective** is
--
--   $$
--   F(x)=B(x)+\ell_{\mathrm{init}}(x)+\sum_{j=0}^{L-1}A_j(x),\qquad \ell_{\mathrm{init}}(x)=-s_0\langle v_0,x\rangle,
--   $$
--
--   where $B=B_L$ is the uniformly convex base built on the displacements $h_j$, and $A_j$ are the phase functions. It is the hard instance of the lower bound: a uniformly convex, Hölder-smooth function whose successive phases each force about $m/16$ oracle calls.
--
--   **Formalization Note** The complete objective depends on $q=p+\nu$, $\mu$, the chain length $m$, the number of phases $L$, the initial scale $\tau_0$ and a phase frame $(v,u)$; the constants $K$ and $\eta$ are fixed as in Lemma 4.5. Phase directions are sequences indexed by $j\in\mathbb N$, of which only $j<L$ enter.
-- source:
--   Bai, Tight Lower Bounds under Matched High-Order Hölder Smoothness and Uniform Convexity, arXiv:2611.05527, Eq. (4.17), p.10; Definition E.8, Eq. (E.11), p.89

import Mathlib
import Definitions.Def_MatchedUCLB_objPhase
import Definitions.Def_MatchedUCLB_baseSeq

namespace MatchedUCLB

/-- **The complete objective `F`.** Bai, *Tight Lower Bounds under Matched High-Order Hölder Smoothness and Uniform Convexity*, arXiv:2611.05527, Eq. (4.17), p.10, and Definition E.8, Eq. (E.11),
p.89: "`ℓ_init(x) := −s_0⟨v_0, x⟩`, `F(x) := B(x) + ℓ_init(x) + ∑_{j=0}^{L−1} A_j(x)`", where
`B = B_L` is the base of (4.4) built on the displacements `h_j` of Definition E.1.

**Formalization Note.** The parameters of the complete objective are `q = p + ν`, `μ`, the chain
length `m`, the number of phases `L`, the initial scale `τ₀` and a phase frame `(v, u)`; `K` and
`η` are fixed as in Lemma 4.5 (`KConst q`, `eta q`). -/
noncomputable def objective (q μ : ℝ) {d m : ℕ} (L : ℕ) (τ₀ : ℝ) (v : ℕ → EuclideanSpace ℝ (Fin d)) (u : ℕ → Fin m → EuclideanSpace ℝ (Fin d))
    (x : EuclideanSpace ℝ (Fin d)) : ℝ :=
  baseSeq q μ (objH q τ₀ v u) L x - objSlope q μ τ₀ v u 0 * inner ℝ (v 0) x +
    ∑ j ∈ Finset.range L, objPhase q μ L τ₀ v u j x

end MatchedUCLB


