-- Prove2me | Definitions.Def_WhitneyMatroid_RankCircuit_IsRankSystem
-- name    : WhitneyMatroid_RankCircuit_IsRankSystem
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-05T12:05:12.699804+00:00
-- url     : https://prove2.me/theorems/7f2b4637-95d8-45f0-a0d9-1324532bffc3
-- title:
--   Whitney's rank postulates (R₁)–(R₃), nullity, dependence on a set, and circuits from rank (§2)
-- statement:
--   Let $M$ be a finite set of elements and let $r$ assign an integer $r(N)$, the **rank** of $N$, to every subset $N \subseteq M$. Whitney calls the system a **matroid** when the three rank postulates hold:
--
--   1. $(\mathrm R_1)$ the rank of the null subset is zero, $r(\emptyset)=0$;
--   2. $(\mathrm R_2)$ for any subset $N$ and any element $e \notin N$, $r(N+e) = r(N) + k$ with $k = 0$ or $1$;
--   3. $(\mathrm R_3)$ for any subset $N$ and elements $e_1, e_2 \notin N$, if $r(N+e_1) = r(N+e_2) = r(N)$, then $r(N+e_1+e_2) = r(N)$.
--
--   Here $N + e$ denotes $N \cup \{e\}$. Writing $\rho(N)$ for the number of elements of $N$, the file also defines
--
--   - the **nullity** $n(N) = \rho(N) - r(N)$;
--   - **dependence on a set**: $e$ is dependent on $N$ if $r(N+e) = r(N)$;
--   - **circuits**: a circuit is a minimal dependent set, i.e. a subset $P$ with
--   $$n(P) > 0 \quad\text{and}\quad n(N) = 0 \ \text{ for every } N \subset P,\ N \ne P.$$
--
--   These are the objects of the rank side of Whitney's equivalence between the rank postulates and the circuit postulates.
--
--   **Formalization Note** The elements form a finite type `α` (Whitney's $M = \{e_1,\dots,e_n\}$ is finite) and subsets are `Finset α`. Ranks and nullities are integers (`ℤ`) so that $\rho(N) - r(N)$ is a true difference. $(\mathrm R_2)$ is written as the disjunction $r(N+e) = r(N)$ or $r(N+e) = r(N)+1$. $(\mathrm R_3)$ is stated for all $e_1, e_2 \notin N$; the case $e_1 = e_2$ is implied by the hypothesis and adds nothing. `circuitsOfRank r` is the predicate "is a circuit of $r$".
-- source:
--   Whitney, On the Abstract Properties of Linear Dependence, Amer. J. Math. 57 (1935), p. 510, §2 (postulates (R₁)–(R₃), ρ, n, dependence on N, circuit)

import Mathlib
import Definitions.Def_WhitneyMatroid_RankIndep_Postulates

namespace WhitneyMatroid.RankCircuit

variable {α : Type*} [Fintype α] [DecidableEq α]

/-- Whitney's rank postulates (§2, p. 510) for an integer-valued function `r` on the subsets of the
finite set of elements `α`:
(R₁) the rank of the null subset is zero;
(R₂) for any subset `N` and any element `e` not in `N`, `r(N + e) = r(N) + k` with `k = 0` or `1`;
(R₃) for any subset `N` and elements `e₁, e₂` not in `N`, if `r(N + e₁) = r(N + e₂) = r(N)`, then
`r(N + e₁ + e₂) = r(N)`. -/
structure IsRankSystem (r : Finset α → ℤ) : Prop where
  R1 : r ∅ = 0
  R2 : ∀ (N : Finset α) (e : α), e ∉ N →
    r (insert e N) = r N ∨ r (insert e N) = r N + 1
  R3 : ∀ (N : Finset α) (e₁ e₂ : α), e₁ ∉ N → e₂ ∉ N →
    r (insert e₁ N) = r N → r (insert e₂ N) = r N → r (insert e₂ (insert e₁ N)) = r N

/-- `e` is dependent on `N` if `r(N + e) = r(N)` (p. 510). -/
def IsDependentOn (r : Finset α → ℤ) (e : α) (N : Finset α) : Prop := r (insert e N) = r N

/-- A circuit of the rank system `r` is a minimal dependent set (p. 510): a subset `P` with
`n(P) > 0` such that every proper subset `N ⊂ P` has `n(N) = 0`. -/
def circuitsOfRank (r : Finset α → ℤ) (P : Finset α) : Prop :=
  0 < WhitneyMatroid.RankIndep.nullity r P ∧ ∀ N : Finset α, N ⊂ P → WhitneyMatroid.RankIndep.nullity r N = 0

end WhitneyMatroid.RankCircuit


