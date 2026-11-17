-- Prove2me | Definitions.Def_OnlineCAP_Supplement_IsDSTHitter
-- name    : OnlineCAP_Supplement_IsDSTHitter
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T07:18:52.434194+00:00
-- url     : https://prove2.me/theorems/8751be62-7faa-42f1-9595-c6f9df596414
-- title:
--   Rectangle-hitting subroutine family with the properties of Theorem 1.11 [DST25]
-- statement:
--   Let $\mathcal S$ be a class of planar rectangles (leftless or topless). A **subroutine family** assigns to every grid size $N\in\mathbb N$ and every finite point set $P\subseteq\mathbb R^2$ an online algorithm $A_{N,P}$ that receives rectangles $R_1,R_2,\dots$ one at a time and maintains a purchased point set $Q_t$. The family **has the properties of Theorem 1.11** for $\mathcal S$ if every $A_{N,P}$ is deterministic and there is one function $f(N)=O(\log N)$ such that for every $N$, every $P\subseteq[0,N)^2\cap\mathbb Z^2$ and every sequence of rectangles of $\mathcal S$:
--
--   1. the purchased points lie in $P$, and every fed rectangle that contains a point of $P$ is hit by $Q_t$;
--   2. (**property 1**) if the arriving rectangle $R_t$ is already hit by $Q_{t-1}$ (satisfied on arrival), then $Q_t=Q_{t-1}$; in every case $|Q_t\setminus Q_{t-1}|\le 2$;
--   3. (**property 2**) for every $p\in P$, the number of times $t$ with $p\in R_t$ and $R_t$ not hit by $Q_{t-1}$ is at most $f(N)$.
--
--   Theorem 1.11 (De, Singh and Tóth) asserts such an algorithm for bottomless rectangles, and the paper notes that by rotation it handles leftless and topless rectangles with the same guarantee. These properties are exactly what the analysis of Algorithm 1 uses.
--
--   **Formalization Note** Rectangles containing no point of $P$ may be fed; they need not be hit and, being never satisfied, may trigger at most two purchases. $O(\log N)$ is an asymptotic bound as $N\to\infty$, uniform over point sets and fed sequences, natural logarithm. Each $A_{N,P}$ is a randomized online algorithm of the mission whose purchases do not depend on its coins.
-- source:
--   Hathcock, Subramanian, Umboh, Zlatin, Weighted and Unweighted Online Connectivity Augmentation via Geometric Hitting Set (manuscript of Nov. 3, 2026, sha256 e3b9cb64…), Theorem 1.11, p.6 and p.11 (PDF p.6, p.11)

import Mathlib
import Definitions.Def_OnlineCAP_RandOnlineAlg
import Definitions.Def_OnlineCAP_RandOnlineAlg_IsDeterministic

open Filter Asymptotics

namespace OnlineCAP.Supplement

/-- **A rectangle-hitting subroutine family with the two properties of Theorem 1.11.**
Hathcock–Subramanian–Umboh–Zlatin, *Weighted and Unweighted Online Connectivity Augmentation via
Geometric Hitting Set*, manuscript of Nov. 3, 2026 (sha256 e3b9cb64…), Theorem 1.11 (De, Singh,
Tóth [DST25]), p.6 and p.11 (PDF p.6, p.11): "Let P ⊆ [0, N)² ∩ Z² be a point set. Then there is a
deterministic algorithm for online bottomless rectangle hitting set satisfying: 1. If a bottomless
rectangle is satisfied on arrival, the algorithm adds no new points. Otherwise, it adds at most two
points. 2. For every point p ∈ P, there are O(log N) rectangles containing p that are unsatisfied
on arrival." and p.11: "By rotation, this algorithm can easily be adapted to handle topless and
leftless rectangles with the same guarantee."

`IsDSTHitter shape A` says that the family `A N P` (one online algorithm for every grid size `N`
and every point set `P`) is deterministic and that there is one function `f(N) = O(log N)` such
that, for every `N`, every `P ⊆ [0, N)² ∩ ℤ²` and every list `s` of rectangles of the given
`shape` fed to `A N P`:
1. the purchased points lie in `P`, and every fed rectangle that contains a point of `P` is hit;
2. (property 1) if the next rectangle `R` is already hit on arrival, nothing is bought; in any
   case at most two new points are bought;
3. (property 2) for every `p ∈ P`, the number of positions `t` of `s` whose rectangle contains
   `p` and is not hit by the points bought after the first `t` rectangles is at most `f(N)`.

**Formalization Note.** "Satisfied on arrival" is relative to the subroutine's own purchases.
Rectangles containing no point of `P` may be fed (Algorithm 1 feeds both of its rectangles); they
need not be hit and, being never satisfied, may trigger at most two purchases. `O(log N)` is
`Asymptotics.IsBigO` along `N → ∞` with one function `f` for all `P` and all lists (natural log).
The algorithm is a `RandOnlineAlg` with `IsDeterministic`; the conditions are required for every
outcome `ω`. -/
def IsDSTHitter (shape : Set (ℝ × ℝ) → Prop)
    (A : ℕ → Finset (ℝ × ℝ) → RandOnlineAlg (ℝ × ℝ) (Set (ℝ × ℝ))) : Prop := by
  classical
  exact (∀ N P, (A N P).IsDeterministic) ∧
    ∃ f : ℕ → ℝ, f =O[atTop] (fun N : ℕ => Real.log N) ∧
      ∀ (N : ℕ) (P : Finset (ℝ × ℝ)),
        (∀ p ∈ P, ∃ i j : ℕ, i < N ∧ j < N ∧ p = ((i : ℝ), (j : ℝ))) →
        ∀ (ω : (A N P).Ω) (s : List (Set (ℝ × ℝ))), (∀ R ∈ s, shape R) →
          (A N P).buy ω s ⊆ P ∧
          (∀ R ∈ s, (∃ p ∈ P, p ∈ R) → ∃ p ∈ (A N P).buy ω s, p ∈ R) ∧
          (∀ R, shape R →
            ((∃ p ∈ (A N P).buy ω s, p ∈ R) → (A N P).buy ω (s ++ [R]) = (A N P).buy ω s) ∧
            ((A N P).buy ω (s ++ [R]) \ (A N P).buy ω s).card ≤ 2) ∧
          (∀ p ∈ P, ((((Finset.range s.length).filter (fun t =>
              p ∈ s.getD t ∅ ∧ ¬ ∃ q ∈ (A N P).buy ω (s.take t), q ∈ s.getD t ∅)).card : ℕ) : ℝ)
              ≤ f N)

end OnlineCAP.Supplement


