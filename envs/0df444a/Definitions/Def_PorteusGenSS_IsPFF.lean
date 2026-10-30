-- Prove2me | Definitions.Def_PorteusGenSS_IsPFF
-- name    : PorteusGenSS_IsPFF
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-30T01:08:55.81052+00:00
-- url     : https://prove2.me/theorems/1ad3abf1-c250-45c4-9bd2-b868b99d3cd1
-- title:
--   Pólya frequency function (PFF)
-- statement:
--   A function $\varphi:\mathbb R\to\mathbb R$ is a **Pólya frequency function** (PFF) if it is $PF_n$ for every $n\ge 1$, i.e. all the determinants $\det[\varphi(x_i-t_j)]_{i,j=1}^k$ with increasing $x$'s and $t$'s are nonnegative, for every size $k$.
-- source:
--   Porteus, On the Optimality of Generalized (s, S) Policies, Management Science 17(7):411–426 (1971), Definition 6, p. 421

import Mathlib
import Definitions.Def_PorteusGenSS_IsPFOrder

namespace PorteusGenSS

/-- **Pólya frequency function (Definition 6).**
Porteus, On the Optimality of Generalized (s, S) Policies, Management Science 17(7):411–426 (1971), Definition 6, p. 421: "A function φ is a Pólya frequency function (φ is PFF) if φ is PFₙ
for all n ≥ 1."

`IsPFF φ` says `IsPFOrder n φ` for every `n ≥ 1`. -/
def IsPFF (φ : ℝ → ℝ) : Prop :=
  ∀ n : ℕ, 1 ≤ n → IsPFOrder n φ

end PorteusGenSS


