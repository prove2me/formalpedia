-- Prove2me | Definitions.Def_FirstChoiceDesign_IsStable
-- name    : FirstChoiceDesign_IsStable
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T03:25:50.423212+00:00
-- url     : https://prove2.me/theorems/df6bb3f4-7f61-4338-85ac-260dbc01b4d4
-- title:
--   $(\rho^\varphi,r)$-stable matchings
-- statement:
--   A matching $\mu$ assigns each school $s$ a set of at most $c_s$ students $\mu_s$ and each student a school or $\emptyset$. It is **individually rational** if $\mu_i\succeq_i\emptyset$ for every $i$. It is **$(\rho^\varphi,r)$-blocked** by $(s,i)$ if $s\succ_i\mu_i$ and either $|\mu_s|<c_s$ or there is $\bar i\in\mu_s$ with $i\succ^\varphi_{r_s}\bar i$, that is, $\rho^\varphi_{is}+r_{is}<\rho^\varphi_{\bar i s}+r_{\bar i s}$. It is **$(\rho^\varphi,r)$-stable** if it is individually rational and not blocked.
--
--   **Formalization Note** The source prints "there exists $\bar i\in I$" and $\bar i\in\mu_s$ is plainly meant (Roth–Sotomayor): with $\bar i\in I$ almost nothing is stable. Matchings are `Assignment n m`, so the two-sided description of $\mu$ is one function, and every student holds at most one seat by construction. The published `Market.PrintedStable` is a different notion and is not used.
-- source:
--   Narita, (Non)Randomization: A Theory of Quasi-Experimental Evaluation of School Quality, Cowles Foundation Discussion Paper No. 2056R (rev. Aug. 2017), Proof of Lemma 3, p.41

import Definitions.Def_FirstChoiceDesign_First

namespace FirstChoiceDesign

open GaleShapley1962.Admissions

/-- `(s, i)` `(ρ^φ, r)`-blocks the matching `μ`, p.41: `s ≻_i μ_i` and either `|μ_s| < c_s` or there
is `ī ∈ μ_s` with `i ≻^φ_{r_s} ī`.

**Formalization Note** The printed clause says "there exists `ī ∈ I`", and `ī ∈ μ_s` is plainly
meant (Roth and Sotomayor): with `ī ∈ I` almost nothing is stable. -/
def Blocks {n m : ℕ} (φ : GDA) (X : Problem (φ.K n) n m) (r : Lottery n m) (μ : Assignment n m)
    (s : Fin m) (i : Fin n) : Prop :=
  X.u i (some s) < X.u i (μ i) ∧
    ((seats μ s).card < X.c s ∨
      ∃ ib ∈ seats μ s, φ.score X.toSetting X.ρ r i s < φ.score X.toSetting X.ρ r ib s)

/-- `μ` is a `(ρ^φ, r)`-stable matching, p.41: it seats at most `c_s` students at each school, it is
individually rational (`μ_i ⪰_i ∅`), and no `(s, i)` blocks it. The published `Market.PrintedStable`
is a different notion and is not used. -/
def IsStable {n m : ℕ} (φ : GDA) (X : Problem (φ.K n) n m) (r : Lottery n m)
    (μ : Assignment n m) : Prop :=
  (∀ s, (seats μ s).card ≤ X.c s) ∧ (∀ i, X.u i (μ i) ≤ X.u i none) ∧ ∀ s i, ¬ Blocks φ X r μ s i

end FirstChoiceDesign


