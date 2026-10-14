-- Prove2me | Definitions.Def_StableMatching_GaleShapley
-- name    : StableMatching_GaleShapley
-- status  : Definition
-- author  : @Lucas
-- created : 2026-10-11T13:30:58.7487+00:00
-- url     : https://prove2.me/theorems/80ac7470-0424-4b8a-8c26-71fcbeb4efcc
-- title:
--   Stable marriage instances, stability and the Gale–Shapley algorithm
-- statement:
--   Shared model for the stable marriage problem with $n$ men and $n$ women, both indexed by $\mathrm{Fin}\,n = \{0,\dots,n-1\}$.
--
--   * **Instance.** Each man $m$ has a strict ranking of all women, given by a bijection $\mathrm{manRank}_m : \mathrm{Fin}\,n \to \mathrm{Fin}\,n$, where $\mathrm{manRank}_m(w)$ is the position of $w$ in $m$'s list (position $0$ = most preferred); symmetrically $\mathrm{womanRank}_w(m)$. Man $m$ *prefers* $w$ to $w'$ iff $\mathrm{manRank}_m(w) < \mathrm{manRank}_m(w')$, and similarly for women.
--   * **Matching.** A bijection $\mu$ from men to women; $\mu(m)$ is $m$'s partner and $\mu^{-1}(w)$ is $w$'s partner.
--   * **Stability.** $(m,w)$ is a *blocking pair* for $\mu$ if $m$ prefers $w$ to $\mu(m)$ and $w$ prefers $m$ to $\mu^{-1}(w)$. $\mu$ is *stable* if there is no blocking pair.
--   * **Gale–Shapley algorithm (men proposing).** A state records, for each man $m$, the number $\mathrm{next}(m)$ of women he has proposed to, and for each woman $w$ her current provisional fiancé (or none). Initially nobody has proposed and nobody is engaged. In each round: (a) every unengaged man $m$ with $\mathrm{next}(m) < n$ proposes to the woman of rank $\mathrm{next}(m)$ in his list, i.e. his most-preferred woman not yet proposed to, and increments $\mathrm{next}(m)$; (b) every woman becomes engaged to the man she ranks best among her current fiancé and this round's suitors, rejecting the rest. The *output* of the algorithm is the state after $n^2$ rounds, and a matching $\mu$ is *the Gale–Shapley outcome* if in that state every man $m$ is engaged to $\mu(m)$.
--   * **Deviations.** $I'$ is a *deviation of the men in $C$* from $I$ if $I'$ and $I$ have the same women's rankings and the same rankings for every man outside $C$; $I'$ is a *deviation of woman $w$* if only $w$'s ranking may differ.
--   * **Example.** The 3×3 instance of the section *Different stable matchings*: men $A,B,C = 0,1,2$, women $X,Y,Z = 0,1,2$, with $A: YXZ$, $B: ZYX$, $C: XZY$, $X: BAC$, $Y: CBA$, $Z: ACB$ (lists from most to least preferred).
-- source:
--   Wikipedia, "Stable matching problem" (https://en.wikipedia.org/wiki/Stable_matching_problem), sections "Stable matching problem" (introduction), "Different stable matchings" and "Algorithmic solution"; primary reference: D. Gale, L. S. Shapley, College Admissions and the Stability of Marriage, Amer. Math. Monthly 69 (1962) 9–14, doi:10.2307/2312726.

import Mathlib

/-!
# Stable matching problem: definitions

Source: Wikipedia, *Stable matching problem* (https://en.wikipedia.org/wiki/Stable_matching_problem),
sections "Stable matching problem" (introduction), "Different stable matchings" and
"Algorithmic solution".

Men and women are both indexed by `Fin n`. Preferences are strict total orders, encoded by
rank bijections: `I.manRank m w` is the position of woman `w` in man `m`'s list
(`0` = most preferred), and symmetrically for women.
-/

namespace StableMatching

/-- An instance of the stable marriage problem with `n` men and `n` women, each person
ranking all members of the other side in a strict order. `manRank m w` is the position of
woman `w` in man `m`'s preference list, `womanRank w m` the position of man `m` in woman `w`'s
list; position `0` is the most preferred. -/
structure Instance (n : ℕ) where
  manRank : Fin n → (Fin n ≃ Fin n)
  womanRank : Fin n → (Fin n ≃ Fin n)

variable {n : ℕ}

/-- Man `m` strictly prefers woman `w` to woman `w'`. -/
def Instance.manPrefers (I : Instance n) (m w w' : Fin n) : Prop :=
  I.manRank m w < I.manRank m w'

/-- Woman `w` strictly prefers man `m` to man `m'`. -/
def Instance.womanPrefers (I : Instance n) (w m m' : Fin n) : Prop :=
  I.womanRank w m < I.womanRank w m'

instance (I : Instance n) (m w w' : Fin n) : Decidable (I.manPrefers m w w') := by
  unfold Instance.manPrefers; infer_instance

instance (I : Instance n) (w m m' : Fin n) : Decidable (I.womanPrefers w m m') := by
  unfold Instance.womanPrefers; infer_instance

/-- A matching is a bijection from men to women: `μ m` is the wife of man `m`, and
`μ.symm w` the husband of woman `w`. -/
abbrev Matching (n : ℕ) := Fin n ≃ Fin n

/-- `(m, w)` is a blocking pair for `μ`: man `m` prefers `w` to his partner and `w` prefers
`m` to her partner. -/
def Instance.IsBlockingPair (I : Instance n) (μ : Matching n) (m w : Fin n) : Prop :=
  I.manPrefers m w (μ m) ∧ I.womanPrefers w m (μ.symm w)

/-- A matching is stable when there is no pair `(m, w)` who both prefer each other to their
current partners. -/
def Instance.IsStable (I : Instance n) (μ : Matching n) : Prop :=
  ∀ m w : Fin n, ¬ I.IsBlockingPair μ m w

instance (I : Instance n) (μ : Matching n) : Decidable (I.IsStable μ) := by
  unfold Instance.IsStable Instance.IsBlockingPair; infer_instance

/-! ## The Gale–Shapley (deferred acceptance) algorithm, men proposing -/

/-- State of the Gale–Shapley algorithm between rounds.
* `next m` is the number of women man `m` has proposed to so far; he proposes in order of
  preference, so his next proposal goes to the woman of rank `next m`.
* `fiance w` is the man woman `w` is currently (provisionally) engaged to, if any. -/
structure GSState (n : ℕ) where
  next : Fin n → ℕ
  fiance : Fin n → Option (Fin n)

/-- Initial state: nobody has proposed, nobody is engaged. -/
def GSState.init (n : ℕ) : GSState n := ⟨fun _ => 0, fun _ => none⟩

/-- Man `m` is engaged in state `s`. -/
def GSState.IsEngaged (s : GSState n) (m : Fin n) : Prop := ∃ w, s.fiance w = some m

instance (s : GSState n) (m : Fin n) : Decidable (s.IsEngaged m) := by
  unfold GSState.IsEngaged; infer_instance

/-- The woman to whom man `m` proposes in the current round, if any: an unengaged man
proposes to the most-preferred woman to whom he has not yet proposed. -/
def Instance.proposal (I : Instance n) (s : GSState n) (m : Fin n) : Option (Fin n) :=
  if h : ¬ s.IsEngaged m ∧ s.next m < n then some ((I.manRank m).symm ⟨s.next m, h.2⟩)
  else none

/-- Among the set of men `c`, the one woman `w` most prefers (`none` if `c` is empty). -/
def Instance.favourite (I : Instance n) (w : Fin n) (c : Finset (Fin n)) : Option (Fin n) :=
  if h : c.Nonempty then
    some ((I.womanRank w).symm ((c.image (I.womanRank w)).min' (h.image _)))
  else none

/-- One round of the Gale–Shapley algorithm: (a) every unengaged man proposes to the
most-preferred woman he has not yet proposed to; (b) every woman becomes (or stays) engaged to
the man she most prefers among her current partner and this round's suitors, rejecting all
others. -/
def Instance.gsRound (I : Instance n) (s : GSState n) : GSState n where
  next m := if (I.proposal s m).isSome then s.next m + 1 else s.next m
  fiance w := I.favourite w
    ((Finset.univ.filter fun m => I.proposal s m = some w) ∪ (s.fiance w).toFinset)

/-- The state after `k` rounds. -/
def Instance.gsRun (I : Instance n) (k : ℕ) : GSState n := (I.gsRound)^[k] (GSState.init n)

/-- The final state of the Gale–Shapley algorithm, taken after `n ^ 2` rounds. (Once every
man is engaged no one proposes any more and rounds leave the state unchanged; that `n ^ 2`
rounds suffice is a separate milestone.) -/
def Instance.galeShapley (I : Instance n) : GSState n := I.gsRun (n ^ 2)

/-- `μ` is the matching produced by the Gale–Shapley algorithm: in the final state every man
`m` is engaged to the woman `μ m`. -/
def Instance.IsGSOutcome (I : Instance n) (μ : Matching n) : Prop :=
  ∀ m : Fin n, I.galeShapley.fiance (μ m) = some m

/-- `I'` is obtained from `I` by changing only the preference lists of the men in `C`. -/
def Instance.MenDeviation (I I' : Instance n) (C : Finset (Fin n)) : Prop :=
  (∀ m, m ∉ C → I'.manRank m = I.manRank m) ∧ I'.womanRank = I.womanRank

/-- `I'` is obtained from `I` by changing only the preference list of woman `w`. -/
def Instance.WomanDeviation (I I' : Instance n) (w : Fin n) : Prop :=
  I'.manRank = I.manRank ∧ ∀ w', w' ≠ w → I'.womanRank w' = I.womanRank w'

/-! ## The 3 × 3 example from "Different stable matchings"

Men `A, B, C` are `0, 1, 2`; women `X, Y, Z` are `0, 1, 2`. Preferences:
`A: YXZ, B: ZYX, C: XZY` and `X: BAC, Y: CBA, Z: ACB`. -/

/-- Rank bijection of `Fin 3` given by an involutive permutation table. -/
def rank3 (f : Fin 3 → Fin 3) (h : ∀ i, f (f i) = i) : Fin 3 ≃ Fin 3 :=
  ⟨f, f, h, h⟩

/-- The 3-men, 3-women instance from the section "Different stable matchings". -/
def example3 : Instance 3 where
  manRank
    | 0 => rank3 ![1, 0, 2] (by decide)   -- A: Y X Z
    | 1 => rank3 ![2, 1, 0] (by decide)   -- B: Z Y X
    | 2 => rank3 ![0, 2, 1] (by decide)   -- C: X Z Y
  womanRank
    | 0 => rank3 ![1, 0, 2] (by decide)   -- X: B A C
    | 1 => rank3 ![2, 1, 0] (by decide)   -- Y: C B A
    | 2 => rank3 ![0, 2, 1] (by decide)   -- Z: A C B

end StableMatching


