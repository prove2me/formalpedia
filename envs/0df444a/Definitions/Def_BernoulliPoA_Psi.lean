-- Prove2me | Definitions.Def_BernoulliPoA_Psi
-- name    : BernoulliPoA_Psi
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T12:43:47.429207+00:00
-- url     : https://prove2.me/theorems/8d43a3df-0835-4098-8508-a614869ab6f0
-- title:
--   The convex function $\Psi$
-- statement:
--   The supremum of the affine functions over the index set:
--   $$
--   \Psi(\omega)=\sup_{(c,k,m)\in\mathcal T}\beta_{c,k,m}(\omega).
--   $$
--
--   **Formalization Note** The supremum lies in $[0,\infty]$, so an unbounded family gives $\infty$. For $\omega\ge 1$ and $\mathcal T\neq\emptyset$ it dominates $\beta_{c,1,0}(\omega)=\omega>0$, so the truncation to nonnegative values loses nothing there.
-- source:
--   Cominetti et al., Ordinary and Prophet Planning under Uncertainty in Bernoulli Congestion Games, arXiv:1903.03309v8, Lemma EC.1, p.ec1

import Mathlib
import Definitions.Def_BernoulliPoA_triples
import Definitions.Def_BernoulliPoA_beta
open scoped ENNReal

namespace BernoulliPoA

/-- **The convex function** `Ψ`. Cominetti et al., *Ordinary and Prophet Planning under Uncertainty in Bernoulli Congestion Games*, arXiv:1903.03309v8, Lemma EC.1, p.ec1: `Ψ(ω) = sup_{(c,k,m) ∈ T} β_{c,k,m}(ω)`.

**Formalization Note** The supremum lies in `ℝ≥0∞`, so an unbounded family gives `⊤` (Lean's real `⨆` would give `0`). For `ω ≥ 1`
and `T ≠ ∅` it dominates `β_{c,1,0}(ω) = ω > 0`, so `ENNReal.ofReal` loses nothing there; for `T = ∅` it is `0`. -/
noncomputable def Psi (C : Set (ℕ → ℝ)) (q ω : ℝ) : ℝ≥0∞ :=
  ⨆ t ∈ triples C, ENNReal.ofReal (beta q t ω)

end BernoulliPoA


