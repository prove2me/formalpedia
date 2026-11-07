-- Prove2me | Definitions.Def_LiftSAParity_lift
-- name    : LiftSAParity_lift
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T13:07:27.95054+00:00
-- url     : https://prove2.me/theorems/aec046eb-0553-4867-bd00-bf752eef3ebb
-- title:
--   The lifted formula $F\circ g$
-- statement:
--   Let $F$ be a CNF formula over the variables $[n]$ and $g:\{0,1\}^\ell\to\{0,1\}$ a gadget. The lifted formula $F\circ g$ has the $n\ell$ variables $y_{i,k}$, $(i,k)\in[n]\times[\ell]$, arranged in $n$ blocks of $\ell$ variables; block $i$ stands for $x_i=g(y_{i,1},\dots,y_{i,\ell})$.
--
--   For each clause $C$ of $F$ and each assignment $\alpha$ to the blocks of $\mathrm{vars}(C)$ whose gadget values $i\mapsto g(\alpha_i)$ falsify $C$, the formula $F\circ g$ contains the clause
--   $$\bigvee_{i\in\mathrm{vars}(C)}\ \bigvee_{k\in[\ell]} \big(y_{i,k}\neq\alpha_{i,k}\big),$$
--   which is falsified exactly by the assignments that agree with $\alpha$ on those blocks. Hence $y$ falsifies $F\circ g$ iff the block values $i\mapsto g(y_i)$ falsify $F$.
--
--   **Formalization Note** The paper does not spell out the CNF encoding of $F\circ g$; this is the canonical one, in which every lifted clause fixes all variables of all blocks of its source clause (the property used in item (3), p.15).
-- source:
--   de Rezende, Engström, Shekhovtsov, Lifting Sherali-Adams Degree to Unary Sherali-Adams over Parities Size (manuscript, sha256 cab5a032…), Theorem 1.1, p.4; Theorem 4.1, p.13; blocks of §2, p.7

import Mathlib
import Definitions.Def_LiftSAParity_CNF

namespace LiftSAParity

/-- The clause over the block variables of `C` that is falsified exactly by the assignments that
agree with `α` on every variable `(i, k)` with `i ∈ vars(C)`: the clause
`⋁_{i ∈ vars(C), k ∈ [ℓ]} (x_{ik} ≠ α_{ik})`. -/
def liftClause {n ℓ : ℕ} (C : Clause (Fin n)) (α : Fin n × Fin ℓ → Bool) :
    Clause (Fin n × Fin ℓ) :=
  ((clauseVars C) ×ˢ (Finset.univ : Finset (Fin ℓ))).image (fun v => (v, !α v))

/-- **The lifted formula `F ∘ g`** (de Rezende–Engström–Shekhovtsov, *Lifting Sherali-Adams Degree
to Unary Sherali-Adams over Parities Size*, manuscript (sha256 cab5a032…), Theorem 1.1 p.4,
Theorem 4.1 p.13; the variables are the blocks `(x_{ij})_{(i,j) ∈ [n]×[ℓ]}` of §2, p.7). For
each clause `C` of `F` and each assignment `α` to the block variables whose block values
`g(α_i)` falsify `C`, the lifted formula contains the clause on the variables of the blocks of
`C` that excludes exactly `α` on those blocks. So an assignment `y` falsifies `F ∘ g` iff the block
values `i ↦ g(y_{i1}, …, y_{iℓ})` falsify `F`.

**Formalization Note** The paper does not spell out the CNF encoding of `F ∘ g`; this is the
canonical one (every clause of `F ∘ g` fixes all variables of all blocks of its source clause).
Assignments `α` that agree on the blocks of `C` give the same clause, which the `Finset` merges. -/
def lift {n ℓ : ℕ} (F : CNF (Fin n)) (g : (Fin ℓ → Bool) → Bool) : CNF (Fin n × Fin ℓ) :=
  F.biUnion (fun C =>
    (Finset.univ.filter (fun α : Fin n × Fin ℓ → Bool =>
        ∀ l ∈ C, g (fun k => α (l.1, k)) ≠ l.2)).image (liftClause C))

end LiftSAParity


