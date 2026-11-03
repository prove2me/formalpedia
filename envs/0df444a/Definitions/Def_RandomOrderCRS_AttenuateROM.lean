-- Prove2me | Definitions.Def_RandomOrderCRS_AttenuateROM
-- name    : RandomOrderCRS_AttenuateROM
-- status  : Definition
-- author  : @iris
-- created : 2026-11-03T05:21:09.722692+00:00
-- url     : https://prove2.me/theorems/bf820006-b105-4245-b55d-372b7bf4f80f
-- title:
--   Algorithm 2 (Attenuate-ROM)
-- statement:
--   Algorithm 2 of the paper takes a graph $G=(V,E)$ and a fractional matching $x$. It starts with $\mathcal M=\emptyset$. For each arriving edge $e$, it draws $A_e\sim\mathrm{Ber}(a(x_e))$ independently, and adds $e$ to $\mathcal M$ if $e$ is active, not blocked and $A_e=1$. It returns $\mathcal M$.
--
--   The definition is generic in the attenuation function $a:[0,1]\to[0,1]$. Theorem 3 instantiates $a=a_1$.
--
--   **Formalization Note** The algorithm is a `Policy` whose seed is the whole vector of coins $(A_e)_{e\in E}$ with product law; each coin is used only at its own edge, so this does not change the joint law. The hypotheses say that $x$ is a fractional matching and that $a$ maps $[0,1]$ to $[0,1]$; they make the product law a probability law.
-- source:
--   MacRury, Ma & Grammel, On (Random-order) Online Contention Resolution Schemes for the Matching Polytope of (Bipartite) Graphs, arXiv:2209.07520v2, Algorithm 2, p.17

import Mathlib
import Definitions.Def_RandomOrderCRS_FractionalMatching
import Definitions.Def_RandomOrderCRS_Policy

open Finset

namespace RandomOrderCRS

variable {V : Type} [Fintype V] [DecidableEq V]

/-- The law of the attenuation coins: independent `A_e ∼ Ber(a(x_e))`. -/
noncomputable def coinWeight (G : SimpleGraph V) [DecidableRel G.Adj] (x : Sym2 V → ℝ)
    (a : ℝ → ℝ) (A : G.edgeSet → Bool) : ℝ :=
  ∏ e : G.edgeSet, if A e = true then a (x e) else 1 - a (x e)

/-- Algorithm 2 (Attenuate-ROM), arXiv:2209.07520v2, p.17, for an attenuation function
`a : [0, 1] → [0, 1]`: "Draw A_e ∼ Ber(a(x_e)) independently", and select `e` "if e is active, not
blocked and A_e = 1".

**Formalization Note.** The seed is the vector of coins `A`, so all coins are drawn up front; this
does not change the joint law, since each coin is used only at its own edge. Activeness and
non-blocking are enforced by `runStep`, so the decision is just `A e`. The hypotheses say that
`x_e ∈ [0, 1]` and that `a` maps `[0, 1]` to `[0, 1]`. They make the coin law a law. -/
noncomputable def attenuateROM (G : SimpleGraph V) [DecidableRel G.Adj] (x : Sym2 V → ℝ)
    (a : ℝ → ℝ) (hx : IsFractionalMatching G x)
    (ha : ∀ t ∈ Set.Icc (0 : ℝ) 1, a t ∈ Set.Icc (0 : ℝ) 1) : Policy G where
  Seed := G.edgeSet → Bool
  seedWeight := coinWeight G x a
  seedWeight_nonneg := by
    intro A
    refine Finset.prod_nonneg fun e _ => ?_
    have h := ha (x e) (hx.1 e)
    split_ifs
    · exact h.1
    · linarith [h.2]
  seedWeight_sum := by
    have h : ∏ e : G.edgeSet, ∑ b : Bool, (if b = true then a (x e) else 1 - a (x e)) =
        ∑ A ∈ Fintype.piFinset (fun _ : G.edgeSet => (Finset.univ : Finset Bool)),
          ∏ e : G.edgeSet, (if A e = true then a (x e) else 1 - a (x e)) :=
      Finset.prod_univ_sum _ _
    rw [Fintype.piFinset_univ] at h
    unfold coinWeight
    rw [← h]
    simp
  decide := fun A _ e _ => A e

end RandomOrderCRS


