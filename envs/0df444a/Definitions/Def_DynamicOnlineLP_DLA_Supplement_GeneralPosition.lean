-- Prove2me | Definitions.Def_DynamicOnlineLP_DLA_Supplement_GeneralPosition
-- name    : DynamicOnlineLP_DLA_Supplement_GeneralPosition
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-23T03:06:43.635247+00:00
-- url     : https://prove2.me/theorems/097537e0-b35f-447d-a8b2-05530be0d51e
-- title:
--   Multidimensional general position (endnote 4 with Appendix D.1): at most m tied arrivals at every price
-- statement:
--   At a price $p\in\mathbb R^m$, give each arrival $t$ a score for each of $k+1$ alternatives: $0$ for rejection and $f_{tj}-\sum_ip_ig_{itj}$ for option $j$. The arrival is **tied** at $p$ if the largest of these $k+1$ scores is attained by at least two alternatives. A finite set $S$ of arrivals is in **general position** if
--
--   $$\#\{t\in S:\ t\text{ is tied at }p\}\le m\qquad\text{for every }p\in\mathbb R^m .$$
--
--   Endnote 4 states this assumption as "for any $p$, there can be at most $m$ arrivals such that there are ties in $f_{tj}-\sum_ip_ig_{itj}$". Appendix D.1 specifies the relevant equations: equality of the surpluses of two options, or a surplus equal to zero, which is a tie with rejection. The tie with rejection is indispensable: for $k=1$ no two options can tie, yet three identical arrivals with reward and consumption $1$, capacity $2$ and optimal price $1$ violate Lemma 8. Ties below the largest score do not affect the decision and are not counted.
--
--   The paper argues, as after Assumption 3, that a random and arbitrarily small perturbation of the rewards brings an input into general position. The perturbation is not part of this definition.
--
--   **Formalization Note** The price ranges over all of $\mathbb R^m$, as in Assumption 3 and endnote 4.
-- source:
--   Agrawal, Wang, Ye, A Dynamic Near-Optimal Algorithm for Online Linear Programming, Oper. Res. 62(4), 2014, p. 889, endnote 4 and Appendix D.1; p. 881, Assumption 3

import Mathlib
import Definitions.Def_DynamicOnlineLP_DLA_Supplement_SurplusRule

namespace DynamicOnlineLP.DLA.Supplement

/-- The score of each of the `k + 1` alternatives of one arrival: zero for rejection (`none`) and
the surplus for option `j` (`some j`). -/
def score {m k : ℕ} (f : Fin k → ℝ) (g : Fin m → Fin k → ℝ) (p : Fin m → ℝ) :
    Option (Fin k) → ℝ
  | none => 0
  | some j => surplus f g p j

/-- An arrival is tied at price `p` if the largest score among rejection and the `k` options is
attained by two different alternatives. -/
def IsTied {m k : ℕ} (f : Fin k → ℝ) (g : Fin m → Fin k → ℝ) (p : Fin m → ℝ) : Prop :=
  ∃ u v : Option (Fin k), u ≠ v ∧ score f g p u = score f g p v ∧
    ∀ w : Option (Fin k), score f g p w ≤ score f g p u

/-- General position of endnote 4, read with Appendix D.1: for every price vector `p ∈ ℝ^m`,
at most `m` arrivals in `S` are tied at `p`. -/
def BlockGeneralPositionOn {ι : Type} {m k : ℕ} (S : Finset ι) (f : ι → Fin k → ℝ)
    (g : ι → Fin m → Fin k → ℝ) : Prop :=
  ∀ p : Fin m → ℝ,
    by classical exact (S.filter (fun t => IsTied (f t) (g t) p)).card ≤ m

end DynamicOnlineLP.DLA.Supplement


