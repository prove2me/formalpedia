-- Prove2me | Definitions.Def_AcceptSubcube_roundDraws
-- name    : AcceptSubcube_roundDraws
-- status  : Definition
-- author  : @iris
-- created : 2026-11-10T22:03:09.007433+00:00
-- url     : https://prove2.me/theorems/5c771c09-7993-46cc-9e2b-26f305066b78
-- title:
--   Branches and joint draws of one recovery round (Lemma 5.3)
-- statement:
--   One **recovery round** runs the recovery procedure on every star $\mathcal I_{S,a}$, $S\in\binom{[n]}{t}$, $a\in\{0,1\}^S$, for every dyadic budget $b=1,2,4,\dots$ up to the first power of two at least $\binom{n-t}{\ell}$, with radius $r_b=\min\{n,\lceil C_\ell b^{1/\ell}\rceil\}$. A **branch** is a triple $(S,a,b)$.
--
--   A **joint draw** chooses, independently for every branch, a set from the possible draws of the recovery procedure on the star (on $n-t$ variables, budget $b$). The probability of an event of the round is the fraction of joint draws on which it holds.
--
--   **Formalization Note** This is the paper's "ideal model with exact uniform sampling" (p.28): independent uniform draws per branch.
-- source:
--   Cai, Jiang, Liu, Accepting Subcubes and the Approximability of Complete Boolean Min-CSPs, STOC 2027 submission (manuscript sha256 66626baf…), Lemma 5.3, p.26 (the round); §5.4, p.28 (ideal model)

import Mathlib
import Definitions.Def_AcceptSubcube_recoverSet

namespace AcceptSubcube

/-- The dyadic budgets `b = 1, 2, 4, …` "up to the first power of two at least (n−t choose ℓ)"
(Lemma 5.3, p.26). -/
def budgets (n t ℓ : ℕ) : Finset ℕ :=
  (Finset.range (Nat.clog 2 ((n - t).choose ℓ) + 1)).image (fun j => 2 ^ j)

/-- **The branches of one recovery round** (Lemma 5.3, p.26): every `t`-set `S ⊆ [n]`, every pattern
`a ∈ {0,1}^S` (the set `A ⊆ S` of its ones), every dyadic budget `b`.

Cai, Jiang, Liu, *Accepting Subcubes and the Approximability of Complete Boolean Min-CSPs*,
STOC 2027 submission (manuscript sha256 66626baf…), Lemma 5.3, p.26: "One recovery round runs
Lemma 3.3 on every I_{S,a} for all dyadic budgets b = 1, 2, 4, . . . up to the first power of two at
least (n−t choose ℓ)". -/
def branches (n t ℓ : ℕ) : Finset (Finset ℕ × Finset ℕ × ℕ) :=
  ((Finset.range n).powersetCard t).biUnion (fun S =>
    (S.powerset ×ˢ budgets n t ℓ).image (fun p => (S, p.1, p.2)))

/-- The radius `r_b = min{n, ⌈C_ℓ b^{1/ℓ}⌉}` of a budget (Lemma 5.3, p.26). -/
noncomputable def rb (ℓ n b : ℕ) : ℕ :=
  min n ⌈(Cl ℓ : ℝ) * (b : ℝ) ^ ((1 : ℝ) / ℓ)⌉₊

/-- **The joint draws of one round**: an independent uniform draw of the recovery procedure
(an `s`-subset of the star's `n − t` variables, `draws`) for every branch.

**Formalization Note.** The round's probability is the exact fraction of these joint draws (the
uniform product over branches), the paper's "ideal model with exact uniform sampling" (p.28). -/
def roundDraws (n t ℓ : ℕ) : Finset ((br : Finset ℕ × Finset ℕ × ℕ) → br ∈ branches n t ℓ → Finset ℕ) :=
  (branches n t ℓ).pi (fun br => draws ℓ (n - t) br.2.2)

end AcceptSubcube


