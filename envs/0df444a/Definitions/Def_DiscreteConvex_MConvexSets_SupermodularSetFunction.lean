-- Prove2me | Definitions.Def_DiscreteConvex_MConvexSets_SupermodularSetFunction
-- name    : DiscreteConvex_MConvexSets_SupermodularSetFunction
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-09-27T22:16:25.272984+00:00
-- url     : https://prove2.me/theorems/7094707f-f70c-4002-9d84-c2755081554f
-- title:
--   Supermodular set function
-- statement:
--   $\mu : 2^V \to \mathbb R \cup \{-\infty\}$ is a **supermodular set function** with $\mu(\emptyset)=0$, $\mu(V)>-\infty$ (i.e. $-\mu \in S[\mathbb R]$): $\mu(X)+\mu(Y) \le \mu(X\cup Y)+\mu(X\cap Y)$ for all $X,Y \subseteq V$.
--
--   (Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.104.)
-- source:
--   Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.104

import Mathlib

/-!
Murota, *Discrete Convex Analysis*, SIAM 2003, p.104: supermodular set functions, in
`DiscreteConvex.MConvexSets`.
-/

namespace DiscreteConvex.MConvexSets

/-- `μ : 2ⱽ → R ∪ {-∞}` is a **supermodular set function** with `μ(∅) = 0` and `μ(V) > -∞`
(i.e. `-μ ∈ S[R]`): `μ(X) + μ(Y) ≤ μ(X ∪ Y) + μ(X ∩ Y)` for all `X, Y ⊆ V`. -/
def SupermodularSetFunction {V : Type*} [Fintype V] [DecidableEq V] (μ : Finset V → WithBot ℝ) :
    Prop :=
  μ ∅ = 0 ∧ μ Finset.univ ≠ ⊥ ∧
    ∀ X Y : Finset V, μ X + μ Y ≤ μ (X ∪ Y) + μ (X ∩ Y)

end DiscreteConvex.MConvexSets


