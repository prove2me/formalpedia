-- Prove2me | Definitions.Def_OnlineColoringKYY_Supplement_threeLevel
-- name    : OnlineColoringKYY_Supplement_threeLevel
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T07:08:04.362203+00:00
-- url     : https://prove2.me/theorems/dbfc45d0-41ce-4b99-9365-04343c72a7a4
-- title:
--   The three-level randomized online coloring algorithm with threshold $\theta$
-- statement:
--   The **three-level algorithm** of Section 5.3 has an integer threshold $\theta \ge 1$. For each arriving vertex $v$, with $E_i(v)$ the set of eligible level-$i$ colors:
--
--   1. if $E_2(v) \neq \emptyset$, assign a color of $E_2(v)$ (chosen by a rule $\mathrm{sel}$ that may depend on the current coloring);
--   2. otherwise, if $|E_1(v)| \ge \theta$, choose a color of $E_1(v)$ uniformly at random and assign it;
--   3. otherwise, assign a fresh color.
--
--   The **run** of the algorithm on a fixed input graph $G$ with vertices $0, \dots, n-1$ is the probability distribution of the list $(c(0), \dots, c(n-1))$ of colors, over the algorithm's random choices only; it is built vertex by vertex, each step drawing the color of $v$ from the distribution above given the earlier colors. The graph and the arrival order are fixed in advance (oblivious adversary). The coloring is proper by construction, since only eligible colors are reused.
--
--   This is the algorithm of Theorem 5.5.
--
--   **Formalization Note** The paper does not say which eligible level-2 color step 1 takes; the rule $\mathrm{sel}$ is a parameter, and Theorem 5.5 holds for every rule that returns an element of $E_2(v)$. Step 2 is tested as "$E_1(v)$ nonempty and $\theta \le |E_1(v)|$", which is the same test when $\theta \ge 1$.
-- source:
--   Kawarabayashi–Yoneda–Yoneda, Online Graph Coloring: Competitive Ratios Separating Randomized and Deterministic Algorithms, STOC 2027 submission (manuscript sha256 3d1eeea6…), Section 5.3 "Three-Level Algorithm", printed p.15 (PDF p.17)

import Mathlib
import Definitions.Def_OnlineColoringKYY_prefixGraph
import Definitions.Def_OnlineColoringKYY_Supplement_Common

set_option autoImplicit false

namespace OnlineColoringKYY.Supplement

open Classical

/-- One step of the **three-level algorithm** (Kawarabayashi–Yoneda–Yoneda, *Online Graph
Coloring: Competitive Ratios Separating Randomized and Deterministic Algorithms*, STOC 2027
submission (manuscript sha256 3d1eeea6…), Section 5.3, printed p.15 = PDF p.17), with integer
threshold `θ ≥ 1`: the distribution of the color of the arriving vertex `v`, given the colors `c`
of `0, …, v − 1`.

1. If some level-2 color is eligible for `v`, assign the one chosen by `sel c` among them.
2. Otherwise, if at least `θ` level-1 colors are eligible, choose one of them uniformly at random.
3. Otherwise, assign a fresh color.

**Formalization Note** The paper does not say which eligible level-2 color step 1 takes; `sel`
is an arbitrary rule (it may depend on the current coloring), and the theorems quantify over every
rule that returns an element of the offered set. Step 2 tests `E₁` nonempty together with
`θ ≤ |E₁|`; for `θ ≥ 1` the first test is implied by the second. -/
noncomputable def threeLevelStep (θ : ℕ) (sel : List ℕ → Finset ℕ → ℕ) {n : ℕ}
    (G : SimpleGraph (Fin n)) (v : Fin n) (c : List ℕ) : PMF ℕ :=
  if (eligibleLevel G v c 2).Nonempty then PMF.pure (sel c (eligibleLevel G v c 2))
  else if h : (eligibleLevel G v c 1).Nonempty ∧ θ ≤ (eligibleLevel G v c 1).card then
    PMF.uniformOfFinset (eligibleLevel G v c 1) h.1
  else PMF.pure (freshColor c)

/-- The **run of the three-level algorithm** on the first `m` arrivals of `G : SimpleGraph (Fin n)`
(Kawarabayashi–Yoneda–Yoneda, STOC 2027 submission (manuscript sha256 3d1eeea6…), Section 5.3,
printed p.15 = PDF p.17): the distribution, over the algorithm's coins only, of the list of colors
of the vertices `0, …, m − 1` in arrival order. The input graph and its arrival order are fixed
in advance (oblivious adversary, Definition 3.2, p.10 = PDF p.12). -/
noncomputable def threeLevelRun (θ : ℕ) (sel : List ℕ → Finset ℕ → ℕ) {n : ℕ}
    (G : SimpleGraph (Fin n)) : (m : ℕ) → m ≤ n → PMF (List ℕ)
  | 0, _ => PMF.pure []
  | m + 1, h =>
    (threeLevelRun θ sel G m (Nat.le_of_succ_le h)).bind
      (fun c => (threeLevelStep θ sel G ⟨m, h⟩ c).map (fun x => c ++ [x]))

end OnlineColoringKYY.Supplement


