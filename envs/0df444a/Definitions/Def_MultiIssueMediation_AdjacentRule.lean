-- Prove2me | Definitions.Def_MultiIssueMediation_AdjacentRule
-- name    : MultiIssueMediation_AdjacentRule
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T09:19:46.417417+00:00
-- url     : https://prove2.me/theorems/c0e22678-2fcd-48f6-98c0-e16b610f284e
-- title:
--   Adjacent rules: the right side of Theorem 1, with clause (i) corrected
-- statement:
--   A rule $f$ is an **adjacent rule** if there are one $y\in Y\setminus\{o_Y\}$ and one complete, transitive and strict order $\triangleright$ on $\mathbf B$ such that
--
--   1. $f_{\ell,j}=(o_X,y)$ whenever $\ell<j$;
--   2. $f_{\ell,\ell}=(x_\ell,y_{m+1-\ell})$ for all $\ell$;
--   3. whenever $\ell>j$, $f_{\ell,j}\in\{f_{\ell-1,j},f_{\ell,j+1}\}\subset\mathbf B$, and
--
--   $$f_{\ell,j}=\begin{cases} f_{\ell-1,j} & \text{if } f_{\ell-1,j}\triangleright f_{\ell,j+1},\\ f_{\ell,j+1} & \text{otherwise.}\end{cases}$$
--
--   Such a rule picks the $\triangleright$-top bundle among the mutually acceptable logrolling bundles.
--
--   **Formalization Note** The page has "for some $y\in Y$" in clause (i), read cell by cell, and that makes the 'if' direction false; the proof of Part i (p.31) and Theorem 3 (p.21) have one $y\ne o_Y$, as here. The order $\triangleright$ is quantified once, outside the cells, as in Example 2 (p.16) and Step 2 (pp.34–37). It is a relation on the subtype of $\mathbf B$, so the two neighbours are stated to lie in $\mathbf B$.
-- source:
--   Kesten, Özyurt, Efficient and Incentive Compatible Mediation: An Ordinal Market Design Approach, working paper, 4 October 2018, Theorem 1, p.15

import Mathlib
import Definitions.Def_MultiIssueMediation_MediationRule

namespace MultiIssueMediation

/-- Clause (iii) of Theorem 1 for a given order `prec` on `B` (working paper of 4 October 2018,
p.15): for all `ℓ > j`, `f_{ℓ,j} ∈ {f_{ℓ−1,j}, f_{ℓ,j+1}} ⊂ B`, and `f_{ℓ,j} = f_{ℓ−1,j}` if
`f_{ℓ−1,j} ▷ f_{ℓ,j+1}`, and `f_{ℓ,j} = f_{ℓ,j+1}` otherwise.

**Formalization Note.** `p` is row `ℓ−1` and `q` is column `j+1`; both exist because `ℓ > j`. -/
def AdjacencyClause {m : ℕ} (f : MediationRule m)
    (prec : logrollBundles m → logrollBundles m → Prop) : Prop :=
  ∀ ℓ j p q : Fin m, j < ℓ → p.val + 1 = ℓ.val → q.val = j.val + 1 →
    ∃ a b : logrollBundles m, f p j = a ∧ f ℓ q = b ∧
      (f ℓ j = a ∨ f ℓ j = b) ∧ (prec a b → f ℓ j = a) ∧ (¬ prec a b → f ℓ j = b)

/-- The right side of Theorem 1 (working paper of 4 October 2018, p.15), with clause (i) as
corrected: there are one `y ∈ Y ∖ {o_Y}` and one strict total order `▷` on `B` with
(i) `f_{ℓ,j} = (o_X, y)` for all `ℓ < j`;
(ii) `f_{ℓ,ℓ} = (x_ℓ, y_{m+1−ℓ})` for all `ℓ`;
(iii) the adjacency clause.

**Formalization Note.** The page has "for some `y ∈ Y`" inside clause (i), read cell by cell. That
reading makes the 'if' direction false; the proof (Part i, p.31) and Theorem 3 (p.21) have the
single `y ≠ o_Y` used here. The order `▷` is also quantified once, outside the cells, as in Example
2 (p.16) and Step 2 (pp.34–37). -/
def IsAdjacentRule {m : ℕ} (f : MediationRule m) : Prop :=
  ∃ y : Option (Fin m), y ≠ none ∧
    ∃ prec : logrollBundles m → logrollBundles m → Prop,
      IsStrictTotalOrder (logrollBundles m) prec ∧
        (∀ ℓ j : Fin m, ℓ < j → f ℓ j = (none, y)) ∧
        (∀ ℓ : Fin m, f ℓ ℓ = logrollBundle ℓ) ∧
        AdjacencyClause f prec

end MultiIssueMediation


