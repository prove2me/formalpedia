-- Prove2me | Definitions.Def_ConstrainedTrading_eaObjective
-- name    : ConstrainedTrading_eaObjective
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T09:20:24.988516+00:00
-- url     : https://prove2.me/theorems/d46691ec-63f5-4d7c-a63d-11b02a2896e5
-- title:
--   Objective of the relaxed efficient-allocation Problem EA
-- statement:
--   Let $(N,E)$ be a trading network: a finite directed multigraph whose vertices are agents and whose arcs are trades, arc $e$ having seller $e^+$ (its source) and buyer $e^-$ (its sink). Write $\delta^+(i)$ and $\delta^-(i)$ for the outgoing and incoming arcs of agent $i$. Each agent has a separable valuation $w_i(y^i)=w_i^+(y^{i+})+w_i^-(y^{i-})$, where $w_i^+:\mathbb Z^{\delta^+(i)}\to\mathbb R\cup\{-\infty\}$ and $w_i^-(y)=\sum_{e\in\delta^-(i)}c_e y_e$ is linear. For a real outcome $x\in\mathbb R^E$, constraint (5) ($y^i_e=x_e=-y^j_e$ for $e\in\delta^+(i)\cap\delta^-(j)$) gives the net flows $y^{i+}=x|_{\delta^+(i)}$ and $y^{i-}=-x|_{\delta^-(i)}$, and the objective of the relaxed Problem EA is
--   $$
--   \Phi(x)=\sum_{i\in N}\Bigl[\hat w_i^+\bigl(x|_{\delta^+(i)}\bigr)+\hat w_i^-\bigl(-x|_{\delta^-(i)}\bigr)\Bigr],
--   $$
--   where hats are concave extensions. Problem EA maximizes $\Phi$ over $x\in P$.
--
--   **Formalization Note** Problem EA (3)–(5) prints $w_i$; it is read as the concave-extension relaxation over real $x$, as set up on p.7 and in Lemma 3.1. Constraint (5) is built in by parametrizing the net flows by $x$. $\delta^+(i)$, $\delta^-(i)$ are subtypes of $E$, and one vector $c\in\mathbb R^E$ encodes every $w_i^-$, since each arc has one buyer. The sum is in `EReal`.
-- source:
--   Kizilkale, Vohra, Constrained Trading Networks, arXiv:2008.09757v1, §3, p.8, Problem EA (3)–(5); §2, pp.2–3 (trading network, net flows)

import Mathlib
import Definitions.Def_ConstrainedTrading_concaveExt
import Definitions.Def_ConstrainedTrading_linearValuation

namespace ConstrainedTrading

/-- The objective of the relaxed **Problem EA** (Kizilkale–Vohra, *Constrained Trading
Networks*, arXiv:2008.09757v1, §3, p.8, (3)–(5)) at a real outcome `x ∈ ℝ^E`:
`Φ(x) = Σ_{i∈N} [ ŵ⁺ᵢ(y^{i+}) + ŵ⁻ᵢ(y^{i−}) ]`, where

* the trading network is a directed multigraph `(N, E)`; arc `e` has seller `e⁺ = seller e`
  (its source) and buyer `e⁻ = buyer e` (its sink) (§2, p.2);
* `y^{i+} = x|_{δ⁺(i)}` are agent `i`'s net flows on its outgoing arcs and
  `y^{i−} = −x|_{δ⁻(i)}` those on its incoming arcs, by constraint (5)
  (`yⁱₑ = xₑ = −yʲₑ` for `e ∈ δ⁺(i) ∩ δ⁻(j)`);
* `w⁺ᵢ = wPlus i` is a valuation of the outgoing arcs of `i`, and
  `w⁻ᵢ(y) = Σ_{e∈δ⁻(i)} c_e y_e` is the linear valuation of the incoming arcs of `i`;
* hats are concave extensions (`concaveExt`).

**Formalization Note** Problem EA is read as the concave-extension relaxation over real
`x` (reading R2: (3) prints `wᵢ` but no integrality constraint, and §3's setup on p.7 and
Lemma 3.1 maximize `ŵ`). Constraint (5) is built in: the net flows are parametrized by the
outcome `x`. `δ⁺(i)` and `δ⁻(i)` are the subtypes `{e // seller e = i}` and
`{e // buyer e = i}`. One coefficient vector `c : E → ℝ` encodes all linear `w⁻ᵢ`, since each
arc has exactly one buyer. The sum is in `EReal` (`⊥ + a = ⊥`). -/
noncomputable def eaObjective {N E : Type*} [Fintype N] [Fintype E] [DecidableEq N]
    (seller buyer : E → N) (wPlus : (i : N) → ({e // seller e = i} → ℤ) → WithBot ℝ)
    (c : E → ℝ) (x : E → ℝ) : EReal :=
  ∑ i, (concaveExt (wPlus i) (fun e : {e // seller e = i} => x e.1) +
    concaveExt (linearValuation (fun e : {e // buyer e = i} => c e.1))
      (fun e : {e // buyer e = i} => -x e.1))

end ConstrainedTrading


