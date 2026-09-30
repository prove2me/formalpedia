-- Prove2me | Definitions.Def_LysgaardCVRP_Shrink_binPackingNumber
-- name    : LysgaardCVRP_Shrink_binPackingNumber
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-28T16:26:53.583181+00:00
-- url     : https://prove2.me/theorems/7341fe01-42b1-44dc-aee0-4f281afe2487
-- title:
--   Bin-packing number $r(S)$: minimum number of vehicles for $S$
-- statement:
--   Let $Q > 0$ be the vehicle capacity and let the customers have demands $q_i$. For a set $S$ of customers, $r(S)$ is the minimum number of vehicles required to serve the customers in $S$, that is, the optimal value of the bin packing problem with bin capacity $Q$ and item sizes $q_i$, $i \in S$:
--
--   $$r(S) = \min\Big\{ m \in \mathbb N : \exists f : S \to \{0, \dots, m-1\} \text{ with } \sum_{i \in S,\ f(i) = b} q_i \le Q \text{ for every } b < m \Big\}.$$
--
--   The capacity inequalities $x(\delta(S)) \ge 2r(S)$ of the two-index formulation use this number as their right-hand side: every vehicle serving a customer of $S$ enters and leaves $S$.
--
--   **Formalization Note** Written as an infimum over natural numbers. When every customer of $S$ has $q_i \le Q$ (a standing hypothesis of every theorem using $r$), one bin per customer is feasible, so the infimum is attained and equals the minimum; without that hypothesis the set can be empty and the infimum would be the junk value $0$. The empty set has $r(\emptyset) = 0$.
-- source:
--   Lysgaard, Letchford & Eglese, A new branch-and-cut algorithm for the capacitated vehicle routing problem, Math. Program. Ser. A 100 (2004), p. 424 (PDF p. 2), §1, definition of r(S)

import Mathlib

namespace LysgaardCVRP.Shrink

/-- The bin-packing number $r(S)$ of Lysgaard, Letchford & Eglese, Math. Program. Ser. A 100
(2004), §1, p. 424 (PDF p. 2): "the minimum number of vehicles required to serve the customers in
$S$. That is, $r(S)$ is the optimal solution to the Bin Packing Problem (BPP) with bin capacity $Q$
and item sizes given by the demands of the customers in $S$."

It is the least $m$ such that the customers of $S$ can be assigned to bins $0, \dots, m-1$
(`f i < m`) with the total demand of every bin at most $Q$.

**Formalization Note.** Written as `sInf` on `ℕ`. Under the paper's standing hypothesis
$q_i \le Q$ for every customer in $S$, the set contains `S.card` (one bin per customer), so the
infimum is attained and is the true minimum; every theorem using `binPackingNumber` carries that
hypothesis. The assignment `f` is a function on all vertices whose values outside $S$ are ignored,
so $m = 0$ is allowed exactly when $S = \emptyset$, and $r(\emptyset) = 0$. -/
noncomputable def binPackingNumber {n : ℕ} (q : Fin (n + 1) → ℕ) (Q : ℝ)
    (S : Finset (Fin (n + 1))) : ℕ :=
  sInf {m : ℕ | ∃ f : Fin (n + 1) → ℕ, (∀ i ∈ S, f i < m) ∧
    ∀ b < m, ∑ i ∈ S.filter (fun i => f i = b), (q i : ℝ) ≤ Q}

end LysgaardCVRP.Shrink


