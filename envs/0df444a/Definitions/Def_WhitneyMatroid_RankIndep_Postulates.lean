-- Prove2me | Definitions.Def_WhitneyMatroid_RankIndep_Postulates
-- name    : WhitneyMatroid_RankIndep_Postulates
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-05T03:44:29.72898+00:00
-- url     : https://prove2.me/theorems/19a31ffc-e7ca-4827-8a79-8a4d6df5a14b
-- title:
--   Whitney's rank postulates (R) and independence postulates (I), and the translations between them (§2, §3, §6)
-- statement:
--   Let $M$ be a finite set of elements $e_1, \dots, e_n$. Following Whitney, subsets of $M$ are written additively: $N + e$ is $N \cup \{e\}$ and $M_1 + M_2$ is $M_1 \cup M_2$.
--
--   **Rank postulates.** A function $r$ assigning a number $r(N)$ (the *rank*) to every subset $N \subseteq M$ satisfies the rank postulates (R) when
--
--   1. (R₁) the rank of the null subset is zero: $r(\emptyset) = 0$;
--   2. (R₂) for any subset $N$ and any element $e \notin N$, $r(N + e) = r(N) + k$ with $k = 0$ or $1$;
--   3. (R₃) for any subset $N$ and elements $e_1, e_2 \notin N$, if $r(N + e_1) = r(N + e_2) = r(N)$, then $r(N + e_1 + e_2) = r(N)$.
--
--   Such a system is what Whitney calls a **matroid**. With $\rho(N)$ the number of elements of $N$, the **nullity** of $N$ is $n(N) = \rho(N) - r(N)$, and $N$ is **independent** when $n(N) = 0$, that is, when $\rho(N) = r(N)$. For subsets $M', N$ the increment of (3.1) is
--
--   $$\Delta(M', N) = r(M' + N) - r(M').$$
--
--   **Independence postulates.** A predicate "independent" on the subsets of $M$ satisfies the independence postulates (I) when
--
--   1. (I₁) any subset of an independent set is independent;
--   2. (I₂) if $N = e_1 + \dots + e_p$ and $N' = e'_1 + \dots + e'_{p+1}$ are independent (so $N'$ has exactly one element more than $N$), then for some $i$ with $e'_i \notin N$, the set $N + e'_i$ is independent.
--
--   **Translations.** A rank function $r$ gives the independence predicate "$\rho(N) = r(N)$". An independence predicate gives the rank function
--
--   $$r(N) = \text{the number of elements in a largest independent subset of } N.$$
--
--   These are the two axiom systems and the two dictionaries that Whitney's equivalence theorem (§6, p. 514) compares.
--
--   **Formalization Note** The elements form a type $\alpha$ with decidable equality; subsets are finite sets `Finset α`. Ranks, nullities and increments are integers, so differences are not truncated. Whitney allows $r(N)$ to be any number; (R₁) and (R₂) force it to be a nonnegative integer, so integer values lose nothing. The largest independent subset is the supremum of cardinalities over the independent members of the powerset of $N$; this supremum is $0$ when $N$ has no independent subset, which is why the equivalence theorem assumes the empty set is independent.
-- source:
--   Whitney, On the Abstract Properties of Linear Dependence, Amer. J. Math. 57 (1935), p. 510, §2 (R₁)–(R₃), ρ, n, independence; p. 511, (3.1); p. 513, §6 (I₁)–(I₂); p. 514, §6 definition of r(N)

import Mathlib

namespace WhitneyMatroid.RankIndep

variable {α : Type*} [DecidableEq α]

/-- (R₁), §2, p. 510: the rank of the null subset is zero. -/
def RankR1 (r : Finset α → ℤ) : Prop :=
  r ∅ = 0

/-- (R₂), §2, p. 510: for any subset `N` and any element `e` not in `N`,
`r(N + e) = r(N) + k` with `k = 0` or `1`. -/
def RankR2 (r : Finset α → ℤ) : Prop :=
  ∀ (N : Finset α) (e : α), e ∉ N → r (insert e N) = r N ∨ r (insert e N) = r N + 1

/-- (R₃), §2, p. 510: for any subset `N` and elements `e₁, e₂` not in `N`, if
`r(N + e₁) = r(N + e₂) = r(N)`, then `r(N + e₁ + e₂) = r(N)`. -/
def RankR3 (r : Finset α → ℤ) : Prop :=
  ∀ (N : Finset α) (e₁ e₂ : α), e₁ ∉ N → e₂ ∉ N →
    r (insert e₁ N) = r N → r (insert e₂ N) = r N → r (insert e₁ (insert e₂ N)) = r N

/-- Whitney's rank postulates (R₁), (R₂), (R₃) (§2, p. 510): a function `r` on the subsets
of the finite set of elements satisfying them makes the system a *matroid*. -/
def IsRankSystem (r : Finset α → ℤ) : Prop :=
  RankR1 r ∧ RankR2 r ∧ RankR3 r

/-- §2, p. 510: the nullity `n(N) = ρ(N) − r(N)`, where `ρ(N)` is the number of elements
of `N`. -/
def nullity (r : Finset α → ℤ) (N : Finset α) : ℤ :=
  (N.card : ℤ) - r N

/-- (3.1), p. 511: `Δ(M, N) = r(M + N) − r(M)`, where `M + N` is the union. -/
def Delta (r : Finset α → ℤ) (M N : Finset α) : ℤ :=
  r (M ∪ N) - r M

/-- §2, p. 510: `N` is independent (with respect to the rank `r`) if `n(N) = 0`, i.e. the
number of elements of `N` equals `r(N)`. -/
def indepOfRank (r : Finset α → ℤ) (N : Finset α) : Prop :=
  (N.card : ℤ) = r N

/-- (I₁), §6, p. 513: any subset of an independent set is independent. -/
def IndepI1 (Indep : Finset α → Prop) : Prop :=
  ∀ N N' : Finset α, N ⊆ N' → Indep N' → Indep N

/-- (I₂), §6, p. 513: if `N = e₁ + ⋯ + e_p` and `N' = e'₁ + ⋯ + e'_{p+1}` are independent,
then for some `i` such that `e'ᵢ` is not in `N`, `N + e'ᵢ` is independent. -/
def IndepI2 (Indep : Finset α → Prop) : Prop :=
  ∀ N N' : Finset α, Indep N → Indep N' → N'.card = N.card + 1 →
    ∃ e ∈ N', e ∉ N ∧ Indep (insert e N)

/-- Whitney's independence postulates (I₁), (I₂) (§6, p. 513). -/
def IsIndepSystem (Indep : Finset α → Prop) : Prop :=
  IndepI1 Indep ∧ IndepI2 Indep

open Classical in
/-- §6, p. 514: given the independent sets, `r(N)` is the number of elements in a largest
independent subset of `N`. -/
noncomputable def rankOfIndep (Indep : Finset α → Prop) (N : Finset α) : ℤ :=
  (((N.powerset.filter Indep).sup Finset.card : ℕ) : ℤ)

end WhitneyMatroid.RankIndep


