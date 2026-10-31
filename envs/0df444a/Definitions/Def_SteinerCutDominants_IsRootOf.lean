-- Prove2me | Definitions.Def_SteinerCutDominants_IsRootOf
-- name    : SteinerCutDominants_IsRootOf
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T03:16:00.041984+00:00
-- url     : https://prove2.me/theorems/1dcc0c33-9bb3-49cc-a129-f37bffdb1357
-- title:
--   Root of a weight vector
-- statement:
--   The $T$-Steiner cuts with $a$-weight equal to $\gamma_a(G,T)$ are the **roots** of $a$ (and of the inequality $ax\ge\gamma_a(G,T)$).
--
--   **Formalization Note** A root is recorded by the set $S$ defining it, which is needed because laminarity (§3) concerns sets, not cuts.
-- source:
--   Conforti, Kaibel, Steiner Cut Dominants, arXiv:2209.14802v2, §2, p.4

import Mathlib
import Definitions.Def_SteinerCutDominants_gammaOf

open Matrix

namespace SteinerCutDominants

/-- `δ(S)` is a root of `a`: a `T`-Steiner cut whose `a`-weight equals `γ_a(G, T)` (Conforti, Kaibel,
*Steiner Cut Dominants*, arXiv:2209.14802v2, §2, p.4). -/
def IsRootOf {V : Type} [DecidableEq V] (G : SimpleGraph V) [Fintype G.edgeSet]
    (T : Finset V) (a : G.edgeSet → ℝ) (S : Finset V) : Prop :=
  IsSteinerCut T S ∧ a ⬝ᵥ cutVec G S = gammaOf G T a

end SteinerCutDominants


