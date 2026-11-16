-- Prove2me | Definitions.Def_ParallelHAC_Supplement_PackableAll
-- name    : ParallelHAC_Supplement_PackableAll
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T00:31:18.610604+00:00
-- url     : https://prove2.me/theorems/b467037d-2e7e-48f2-9b2f-713fb5571050
-- title:
--   $\alpha$-packability for arbitrary families (Definition 1 as printed)
-- statement:
--   Let $P$ be a finite point set, $n=|P|$, $d$ a linkage function on clusters of $P$, $k$ a dimension parameter and $\kappa,a$ constants. The linkage $d$ is **$\alpha$-packable on $P$ for arbitrary families**, with $\alpha=a(\log_2 n+1)^a$ and exponent $\kappa k$, if for every $r>0$ and every family $\mathcal C$ of nonempty clusters of $P$ (not necessarily disjoint) with $d(B,C)\ge r$ for all distinct $B,C\in\mathcal C$, every nonempty centre $A\subseteq P$ and every radius $R\ge r$,
--   $$\bigl|\{C\in\mathcal C : d(A,C)\le R,\ |C|\le|A|\}\bigr|\le a(\log_2 n+1)^a\Bigl(1+\frac Rr\Bigr)^{\kappa k}.$$
--
--   This is Definition 1 for every family, as printed. The base mission's `ParallelHAC.WellBehaved` packs only pairwise disjoint families, which is all Theorem 3 needs as a hypothesis; Theorems 1 and 2 conclude this stronger clause as well.
--
--   **Formalization Note** $\alpha=\tilde O(1)$ and $O(k)$ are pinned exactly as in `ParallelHAC.WellBehaved`.
-- source:
--   Bateni, Dhulipala, Fletcher, Gowda, Hershkowitz, Jayaram, Łącki, Parallel Hierarchical Agglomerative Clustering in Low Dimensions, arXiv:2507.20047 (sha256 a21061c8…), §2.1, Definition 1, p.5 (PDF p.8)

import Mathlib

namespace ParallelHAC.Supplement

/-- **α-packability for arbitrary families** (Definition 1, p.5), on the point set `P`, with
`α = a (log₂ |P| + 1)^a` and exponent `O(k) = κ k`: for every `r > 0` and every family `𝒞` of
clusters (nonempty subsets of `P`, **not necessarily disjoint**) whose distinct members are at
linkage distance at least `r`, every centre `A` and every radius `R ≥ r`, the members `C ∈ 𝒞`
with `d(A, C) ≤ R` and `|C| ≤ |A|` number at most `α (1 + R/r)^{κ k}`.
Source: arXiv:2507.20047 (sha256 a21061c8…), §2.1, Definition 1, printed p.5 (PDF p.8).

**Formalization Note.** The base mission's `ParallelHAC.WellBehaved.packable` packs only pairwise
disjoint families (a weaker hypothesis, enough for Theorem 3). Definition 1 packs every family;
this predicate is that clause, used as an extra conclusion of Theorems 1 and 2. The `α` and the
exponent are pinned exactly as in `ParallelHAC.WellBehaved`. -/
def PackableAll {V : Type*} [DecidableEq V] (P : Finset V) (k : ℕ) (κ a : ℝ)
    (d : Finset V → Finset V → ℝ) : Prop :=
  ∀ r : ℝ, 0 < r → ∀ 𝒞 : Finset (Finset V),
    (∀ C ∈ 𝒞, C.Nonempty ∧ C ⊆ P) →
    (∀ B ∈ 𝒞, ∀ C ∈ 𝒞, B ≠ C → r ≤ d B C) →
    ∀ A : Finset V, A.Nonempty → A ⊆ P → ∀ R : ℝ, r ≤ R →
      ((𝒞.filter (fun C => d A C ≤ R ∧ C.card ≤ A.card)).card : ℝ) ≤
        a * (Real.logb 2 P.card + 1) ^ a * (1 + R / r) ^ (κ * k)

end ParallelHAC.Supplement


