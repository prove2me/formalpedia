-- Prove2me | Definitions.Def_PrivateUniformGen_Characterization_Profiles
-- name    : PrivateUniformGen_Characterization_Profiles
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-08T09:00:36.022686+00:00
-- url     : https://prove2.me/theorems/29b4feb6-7547-4601-a645-20bfaed4cd15
-- title:
--   Rank cores, profiles and iterated cores
-- statement:
--   For $K\in C^\cap_\infty$, its core is the intersection of all $T\in C^\cap_\infty$ contained in $K$ with the same rank. In Section 5 the dimensions are finite and $\operatorname{CDim}(C)\ge0$. Repeated core operations either preserve rank or strictly lower its positive integer value. The profile records these ranks; the iterated core is the core at the first stationary rank.
--
--   $$\operatorname{profile}(K)=(\rho(K))\mathbin{\frown}\operatorname{profile}(\operatorname{core}(K))$$
--
--   at a strict rank drop, and is the singleton $(\rho(K))$ at equality. Recursion uses initial fuel $\rho(K)$, sufficient for the entire source process. The set $\Xi_d$ consists of decreasing lists in $\{1,\ldots,d\}$, including the empty list. Its order is the recursive order on pp. 12–13, reversing the order of nonempty tails after a shared maximal head. The barred maps extend the original maps to the empty set and $X$: the empty profile is empty, its iterated core is $X$, and $X$ outside the closure gets singleton profile $(\operatorname{NBDim}(C)+1)$ and iterated core $X$. Other outside-domain values are unused.
-- source:
--   Di Wang, Peng Ye, STOC 2027 submission #178 (October 2026), Definitions 5.1, 5.4–5.5 and Xi order, pp. 11–13; barred maps and augmented Xi, pp. 15–16. https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/178.pdf

import Mathlib
import Definitions.Def_PrivateUniformGen_Characterization_Branching

namespace PrivateUniformGen.Characterization

/-- Definition 5.1, p. 11: all subsets having the same rank. -/
def core {X : Type*} (C : LanguageClass X) (K : Set X) : Set X :=
  ⋂₀ {T | T ∈ infiniteClosure C ∧ T ⊆ K ∧ rank C ⊤ T = rank C ⊤ K}

/-- Structural recursion used only with sufficient fuel in the finite-rank regime. -/
noncomputable def profileFuel {X : Type*} (C : LanguageClass X) : ℕ → Set X → List ℕ
  | 0, _ => []
  | f + 1, K => if rank C ⊤ (core C K) = rank C ⊤ K then [(rank C ⊤ K).toNat]
      else (rank C ⊤ K).toNat :: profileFuel C f (core C K)

/-- Definition 5.4, p. 12: rank-many steps suffice because nonterminal ranks strictly fall. -/
noncomputable def profile {X : Type*} (C : LanguageClass X) (K : Set X) : List ℕ :=
  profileFuel C (rank C ⊤ K).toNat K

noncomputable def coreStarFuel {X : Type*} (C : LanguageClass X) : ℕ → Set X → Set X
  | 0, K => K
  | f + 1, K => if rank C ⊤ (core C K) = rank C ⊤ K then core C K
      else coreStarFuel C f (core C K)

/-- Definition 5.5: the terminal set is core(K), not K, at a stationary rank. -/
noncomputable def coreStar {X : Type*} (C : LanguageClass X) (K : Set X) : Set X :=
  coreStarFuel C (rank C ⊤ K).toNat K

/-- Xi_d, p. 12, including the empty list. -/
def Xi (d : ℕ) : Set (List ℕ) :=
  {σ | σ.Pairwise (· > ·) ∧ ∀ r ∈ σ, 1 ≤ r ∧ r ≤ d}

/-- Pages 12-13: reverse the order of nonempty tails after a shared maximal head. -/
def profileLE : ℕ → List ℕ → List ℕ → Prop
  | 0, a, b => a = b
  | d + 1, a, b => a = b ∨
      if a.head? = some (d + 1) then
        if b.head? = some (d + 1) then
          a.tail ≠ [] ∧ (b.tail = [] ∨ profileLE d b.tail a.tail)
        else True
      else if b.head? = some (d + 1) then False else profileLE d a b

/-- Barred maps, pp. 15-16. The remaining outside-domain value is unused. -/
noncomputable def barredProfile {X : Type*} (C : LanguageClass X) (K : Set X) : List ℕ :=
  by
    classical
    exact if K ∈ infiniteClosure C then profile C K
      else if K = ∅ then [] else [(nbDim C ⊤).toNat + 1]

noncomputable def barredCoreStar {X : Type*} (C : LanguageClass X) (K : Set X) : Set X :=
  by classical exact if K ∈ infiniteClosure C then coreStar C K else Set.univ

noncomputable def augmentedXi {X : Type*} (C : LanguageClass X) : Set (List ℕ) :=
  Xi (nbDim C ⊤).toNat ∪ {[(nbDim C ⊤).toNat + 1]}

end PrivateUniformGen.Characterization


