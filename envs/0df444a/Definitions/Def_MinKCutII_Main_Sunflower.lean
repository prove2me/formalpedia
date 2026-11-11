-- Prove2me | Definitions.Def_MinKCutII_Main_Sunflower
-- name    : MinKCutII_Main_Sunflower
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-11T03:37:42.330194+00:00
-- url     : https://prove2.me/theorems/453c324e-25b1-4b19-9166-4bfbd04b33bf
-- title:
--   Sunflowers, the least sunflower number Sun(d, r), and D_k = Sun(k, k+1)(2^k + 1)
-- statement:
--   A **rank-$d$ set system** is a family of sets of size at most $d$. An **$r$-sunflower** is a set of $r$ members of the family whose pairwise intersections are all equal (to the *core*). $\mathrm{Sun}(d,r)$ is the least number $N$ such that every rank-$d$ family with more than $N$ members contains an $r$-sunflower; it exists by the Erdős–Rado sunflower lemma. Lemmas 39 and 41 use
--   $$D_k=\mathrm{Sun}(k,k+1)\,(2^k+1).$$
--
--   **Formalization Note.** Families are finite families of finite subsets of $\mathbb N$ (every finite family over any ground set is a relabelling of one of these). The paper calls $\mathrm{Sun}(d,r)$ "a sunflower number"; the least one is the strongest choice, used in the bounds $|M|\le D_kn$ and $C_k=O(kD_k+2^k)$. `sunNum` is an `sInf` over a nonempty set of naturals, so it is attained.
-- source:
--   Vaughn, Faster Minimum k-Cut II: Improved Randomized and Deterministic Algorithms for Weighted Graphs, arXiv:2609.27797 (version of November 1, 2026, sha256 b01b5a6f…), p. 26, §4.1.2 (sunflower number); p. 27, Lemma 39 (D_k)

import Mathlib

set_option autoImplicit false

namespace MinKCutII.Main

/-!
# Sunflowers, the sunflower number `Sun(d, r)`, and `D_k`

Vaughn, *Faster Minimum k-Cut II*, arXiv:2609.27797 (version of November 1, 2026, sha256
b01b5a6f…), §4.1.2 p. 26 and Lemmas 39, 41 (pp. 27, 29).

* A rank-`d` set system is a family of sets of size at most `d`. An `r`-sunflower is a set of `r`
  members whose pairwise intersections are all equal (the core). Families live over the ground
  set `ℕ`; every finite family over any ground set is a relabelling of one over `ℕ`.
* The paper calls `Sun(d, r)` "a sunflower number": every rank-`d` family with more than
  `Sun(d, r)` members contains an `r`-sunflower. `sunNum d r` is the **least** such number (the
  strongest reading; the set is nonempty by the Erdős–Rado sunflower lemma, so the `sInf` is
  attained and is not the junk value `0` of an empty set, except where `0` is itself valid).
* `Dk k = Sun(k, k + 1) · (2^k + 1)` (Lemmas 39 and 41).
-/

/-- `F` is an `r`-sunflower: `r` members whose pairwise intersections are all equal. -/
def IsSunflower (F : Finset (Finset ℕ)) (r : ℕ) : Prop :=
  F.card = r ∧ ∃ C : Finset ℕ, ∀ X ∈ F, ∀ Y ∈ F, X ≠ Y → X ∩ Y = C

/-- `N` is a sunflower number for rank `d` and `r` petals: every family of sets of size at most `d`
with more than `N` members contains an `r`-sunflower. -/
def IsSunflowerBound (d r N : ℕ) : Prop :=
  ∀ F : Finset (Finset ℕ), (∀ X ∈ F, X.card ≤ d) → N < F.card → ∃ G ⊆ F, IsSunflower G r

/-- `Sun(d, r)`: the least sunflower number. -/
noncomputable def sunNum (d r : ℕ) : ℕ :=
  sInf {N : ℕ | IsSunflowerBound d r N}

/-- `D_k := Sun(k, k + 1) (2^k + 1)`. -/
noncomputable def Dk (k : ℕ) : ℕ :=
  sunNum k (k + 1) * (2 ^ k + 1)

end MinKCutII.Main


