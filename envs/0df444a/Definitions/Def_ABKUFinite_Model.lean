-- Prove2me | Definitions.Def_ABKUFinite_Model
-- name    : ABKUFinite_Model
-- status  : Definition
-- author  : @Yuxuan Xu
-- created : 2026-10-29T10:31:49.505995+00:00
-- url     : https://prove2.me/theorems/9049a2f9-c8be-44f9-87f1-65bcb612f992
-- title:
--   Finite greedy allocation with uniform independent choices
-- statement:
--   **`Trace`.** For natural numbers \(n,d\), a trace is an ordered array with \(n+1\) rows and \(d+2\) entries per row, each entry belonging to \(\{0,\ldots,n\}\). Repeated entries within and between rows are permitted.
--
--   **`step`.** Given natural numbers \(n,d\), a load function from \(\{0,\ldots,n\}\) to the natural numbers, and an ordered list of \(d+2\) choices in \(\{0,\ldots,n\}\), select a choice having the smallest current load, breaking ties by the earliest occurrence in the list. Increase that selected bin’s load by one and leave all other loads unchanged.
--
--   **`finalLoads`.** For natural numbers \(n,d\) and a trace with \(n+1\) rows of \(d+2\) bin choices each, start all \(n+1\) bin loads at zero and process the rows in order. At each row, increase by one the load of the earliest minimum-load choice in that row. The result is the load function after exactly \(n+1\) increments.
--
--   **`maxLoad`.** For natural numbers \(n,d\) and a trace, take the largest of the \(n+1\) bin loads obtained by starting all loads at zero and applying the preceding selection-and-increment procedure to its \(n+1\) rows.
--
--   **`probability`.** For natural numbers \(n,d\) and any predicate \(E\) on the finite set of arrays of \(n+1\) rows and \(d+2\) entries per row, with each entry in \(\{0,\ldots,n\}\), the probability of \(E\) is the number of arrays satisfying \(E\), divided in the real numbers by the total number of such arrays. This is uniform probability on all \((n+1)^{(n+1)(d+2)}\) arrays; equivalently, every individual choice is independent and uniform, with replacement.
--
--   **`center`.** For natural numbers \(n,d\), the center is the real number \(\log(\log(n+1))/\log(d+2)\), where \(\log\) is the natural logarithm as defined by Lean’s total real logarithm. In particular, at \(n=0\), its value is zero because Lean defines \(\log 0=0\).
--
--   **`Upper`.** For a natural number \(d\), this property means that there exists a nonnegative real constant \(C\) such that for every positive real \(\varepsilon\), there exists a natural number \(N\) such that every natural number \(n\ge N\) satisfies
--   \[
--    \Pr\!\left[M_{n,d}\le \frac{\log\log(n+1)}{\log(d+2)}+C\right]\ge 1-\varepsilon.
--   \]
--   Here \(M_{n,d}\) is the maximum load after allocating \(n+1\) balls sequentially to \(n+1\) initially empty bins, each ball taking \(d+2\) independent uniform choices with replacement and entering the earliest chosen bin of minimum current load. Probability is uniform counting over all complete choice arrays.
--
--   **`Lower`.** For a natural number \(d\), this property means that there exists a nonnegative real constant \(C\) such that for every positive real \(\varepsilon\), there exists a natural number \(N\) such that every natural number \(n\ge N\) satisfies
--   \[
--    \Pr\!\left[\frac{\log\log(n+1)}{\log(d+2)}-C\le M_{n,d}\right]\ge 1-\varepsilon.
--   \]
--   Here \(M_{n,d}\) is the maximum load after allocating \(n+1\) balls sequentially to \(n+1\) initially empty bins, using \(d+2\) independent uniform choices with replacement for each ball and selecting the earliest choice of minimum current load; probability is uniform counting over the complete arrays.
--
--   **`TwoSided`.** For a natural number \(d\), this property means that there exists a nonnegative real constant \(C\) such that for every positive real \(\varepsilon\), there exists a natural number \(N\) such that every natural number \(n\ge N\) satisfies
--   \[
--    \Pr\!\left[\left|M_{n,d}-\frac{\log\log(n+1)}{\log(d+2)}\right|\le C\right]\ge 1-\varepsilon.
--   \]
--   Here \(M_{n,d}\) is the maximum load after allocating \(n+1\) balls sequentially to \(n+1\) initially empty bins, each ball making \(d+2\) independent uniform choices with replacement and entering the earliest minimum-load choice; probability is uniform counting over all complete choice arrays.
-- source:
--   Azar, Broder, Karlin, Upfal (1999), Balanced Allocations, https://cs.brown.edu/people/eupfal/papers/SICOMP29.pdf, section 2, p.183; fixed equal-load case

import Mathlib

noncomputable section
namespace ABKUFinite

abbrev Trace (n d : ℕ) := Fin (n + 1) → Fin (d + 2) → Fin (n + 1)

def step {n d : ℕ} (loads : Fin (n + 1) → ℕ)
    (choices : Fin (d + 2) → Fin (n + 1)) : Fin (n + 1) → ℕ :=
  let selected := (List.ofFn choices).foldl
    (fun best candidate => if loads candidate < loads best then candidate else best)
    (choices 0)
  Function.update loads selected (loads selected + 1)

def finalLoads (n d : ℕ) (w : Trace n d) : Fin (n + 1) → ℕ :=
  (List.ofFn w).foldl step (fun _ => 0)

def maxLoad (n d : ℕ) (w : Trace n d) : ℕ :=
  Finset.univ.sup (finalLoads n d w)

def probability (n d : ℕ) (event : Trace n d → Prop) : ℝ := by
  classical
  exact (Fintype.card {w : Trace n d // event w} : ℝ) / Fintype.card (Trace n d)

def center (n d : ℕ) : ℝ :=
  Real.log (Real.log (n + 1 : ℝ)) / Real.log (d + 2 : ℝ)

def Upper (d : ℕ) : Prop :=
  ∃ C : ℝ, 0 ≤ C ∧ ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ n ≥ N,
    1 - ε ≤ probability n d (fun w => (maxLoad n d w : ℝ) ≤ center n d + C)

def Lower (d : ℕ) : Prop :=
  ∃ C : ℝ, 0 ≤ C ∧ ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ n ≥ N,
    1 - ε ≤ probability n d (fun w => center n d - C ≤ (maxLoad n d w : ℝ))

def TwoSided (d : ℕ) : Prop :=
  ∃ C : ℝ, 0 ≤ C ∧ ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ n ≥ N,
    1 - ε ≤ probability n d (fun w => |(maxLoad n d w : ℝ) - center n d| ≤ C)

end ABKUFinite


