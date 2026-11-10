-- Prove2me | Definitions.Def_LinearHashingPoissonesque_ExpectedLoads_LoadVector
-- name    : LinearHashingPoissonesque_ExpectedLoads_LoadVector
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-09T19:02:09.909003+00:00
-- url     : https://prove2.me/theorems/65b0356c-988b-4354-b698-3cedb11935c3
-- title:
--   Labelled load vectors of fixed total mass
-- statement:
--   For a finite set of bins $B$ and an integer $m\ge0$, the space of labelled load vectors is
--
--   $$\Sigma^B(m)=\{w:B\to\mathbb N:\sum_{y\in B}w_y=m\}.$$
--
--   If a finite set $S\subseteq A$ has size $m$ and $f:A\to B$, its actual vector is $\vec L(S,f)=(L_y(S,f))_{y\in B}$. Counting each element of $S$ in its unique fibre proves that this vector belongs to $\Sigma^B(m)$. Labels are retained; functions of this vector need not be symmetric. This is the domain for the arbitrary nonnegative statistic in Lemma 1.
-- source:
--   Vinayak Kumar, STOC 2027 submission #1155 (October 2026), p.8, Section 2, definition of Σ; p.9, Lemma 1; https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1155.pdf

import Definitions.Def_LinearHashingPoissonesque_ExpectedLoads_BinLoad

namespace LinearHashingPoissonesque.ExpectedLoads

/-- Section 2, p.8: nonnegative integer labelled loads with total mass m. -/
def LoadVector (B : Type*) [Fintype B] (m : ℕ) :=
  {w : B → ℕ // ∑ y, w y = m}

/-- The actual load vector; the equality is only the cardinality of its input set. -/
noncomputable def labelledLoads {A B : Type*} [Fintype B] {m : ℕ}
    (S : Finset A) (hm : S.card = m) (f : A → B) : LoadVector B m := by
  classical
  refine ⟨binLoad S f, ?_⟩
  have h := Finset.card_eq_sum_card_fiberwise
    (s := S) (t := (Finset.univ : Finset B)) (f := f) (by intro a ha; simp)
  simpa [binLoad, hm] using h.symm

end LinearHashingPoissonesque.ExpectedLoads


