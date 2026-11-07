-- Prove2me | Definitions.Def_NSWBetter_IsLargeSetFrac
-- name    : NSWBetter_IsLargeSetFrac
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T06:52:15.795315+00:00
-- url     : https://prove2.me/theorems/4b3fe5cc-a746-486c-bbd8-493c060af2f2
-- title:
--   Large goods in a fractional bundle (Definition 4.7)
-- statement:
--   A set $L_i$ is the set of **large goods** of agent $i$ in $x$ when, with $\rho=\dfrac{v_i(x_i)-\sum_{g\in L_i}x_{ig}v_i(g)}{1-\sum_{g\in L_i}x_{ig}}$,
--   1. every $g\in L_i$ has $x_{ig}>0$ and $v_i(g)>\rho$;
--   2. every $g\notin L_i$ has $x_{ig}=0$ or $v_i(g)\le\rho$;
--   3. $\sum_{g\in L_i}x_{ig}<1$.
-- source:
--   Viswanathan, A Better-than-e^{1/e} Approximation Algorithm for Nash Social Welfare under Additive Valuations, arXiv:2607.13340 (held version, sha256 08811cb468c2df39231dca4222c5af94163587c7c83e205e50bbf0b91fc1deb3), Definition 4.7, p.20

import Mathlib
import Definitions.Def_NSWBetter_fracRatio

namespace NSWBetter

/-- **Large goods of a fractional bundle (Definition 4.7).**
Viswanathan, *A Better-than-e^{1/e} Approximation Algorithm for Nash Social Welfare under Additive Valuations*, arXiv:2607.13340 (held version, sha256 08811cb4…), Definition 4.7, p.20: "we define the set of large goods Li for agent i as the set of goods which satisfies (i) for each g ∈ Li, xig > 0 and vi(g) > … , (ii) for each g ∈ G \ Li, xig = 0 or vi(g) ≤ … , and (iii) Σ_(g∈Li) xig < 1." -/
def IsLargeSetFrac {n m : ℕ} (v : Fin n → Fin m → ℝ) (x : Fin n → Fin m → ℝ) (i : Fin n)
    (L : Finset (Fin m)) : Prop :=
  (∀ g ∈ L, 0 < x i g ∧ fracRatio v x i L < v i g) ∧
  (∀ g ∉ L, x i g = 0 ∨ v i g ≤ fracRatio v x i L) ∧ ∑ g ∈ L, x i g < 1

end NSWBetter


