-- Prove2me | Definitions.Def_PorteusGenSS_InCK
-- name    : PorteusGenSS_InCK
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-30T01:13:36.119995+00:00
-- url     : https://prove2.me/theorems/02d93b21-49db-4576-affb-133904639d2c
-- title:
--   The class $C(K)$
-- statement:
--   For $K\ge0$, **$C(K)$** is the class of continuous functions that belong to $C_a(K)$ for some $a\in\mathbb R$: continuous, PF-integrable, coercive functions that decrease up to some point and afterwards never drop by more than $K$.
-- source:
--   Porteus, On the Optimality of Generalized (s, S) Policies, Management Science 17(7):411–426 (1971), Definition 3, p. 414

import Mathlib
import Definitions.Def_PorteusGenSS_InCa

namespace PorteusGenSS

/-- **The class C(K) (Definition 3).**
Porteus, On the Optimality of Generalized (s, S) Policies, Management Science 17(7):411–426 (1971), Definition 3, p. 414: "Let C(K), for K ≥ 0, denote the class of continuous Ca(K)
functions for a ∈ R."

`InCK K f` says `f` is continuous and belongs to `C_a(K)` for some real `a`. -/
def InCK (K : ℝ) (f : ℝ → ℝ) : Prop :=
  Continuous f ∧ ∃ a : ℝ, InCa K a f

end PorteusGenSS


