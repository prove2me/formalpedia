-- Prove2me | Definitions.Def_ReserveLB_Tsig
-- name    : ReserveLB_Tsig
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T02:29:55.357105+00:00
-- url     : https://prove2.me/theorems/de6b5e56-fefc-4eb8-8f09-06d25fe4a007
-- title:
--   Optimal whole-job cost $T_\sigma(x)$ of a reservation
-- statement:
--   Let every job $j$ reserve a nonempty set $\sigma(j)$ of machines with speeds $s_i$. For a size vector $x$,
--   $$
--   T_\sigma(x) = \min_{\pi:\ \pi(j) \in \sigma(j)\ \forall j}\ \max_i \sum_{j:\ \pi(j) = i} \frac{x_j}{s_i},
--   $$
--   the least makespan of a whole-job assignment that sends every job to one of its reserved machines.
--
--   After the sizes are revealed the comparator uses this optimal recourse; $\mathrm{OPT}_k$ averages it over the sizes, and Lemma 2.2 compares it on original and virtual machines.
--
--   **Formalization Note** The minimum is over the finite set of admissible assignments, which is nonempty when every $\sigma(j)$ is nonempty (assumed wherever the cost is used); the value $0$ for an empty set is never used. The machine type is arbitrary.
-- source:
--   Mahboub–Rahgoshay, Stochastic Load Balancing with Strict Machine-Reservation Budgets, manuscript of Oct. 30, 2026 (sha256 aefe1158e8000194527b025b3c358dcb571c94e1038c0bfdd295c6119bc9f630), Section 1, p.2 (definition of $T_\sigma$)

import Mathlib
import Definitions.Def_ReserveLB_makespan

namespace ReserveLB

/-- **Optimal whole-job cost `T_σ(x)` of a reservation graph.**
Mahboub–Rahgoshay, *Stochastic Load Balancing with Strict Machine-Reservation Budgets*,
manuscript of Oct. 30, 2026 (sha256 aefe1158…), Section 1, p.2: "For nonempty σ(j) ⊆ [m], |σ(j)| ≤ k, define
Tσ(x) = min_(π:π(j)∈σ(j)) max_i Σ_(j:π(j)=i) xj/si".

`Tsig s σ x` is the minimum, over the assignments `π` with `π j ∈ σ j` for every job, of the
makespan of `π` at sizes `x`.

**Formalization Note.** The minimum is `Finset.inf'` over the finite set of admissible
assignments; that set is nonempty exactly when every `σ j` is nonempty, which every use assumes.
The value `0` on an empty set is never used. The machine type is arbitrary, so the same
definition gives the virtual cost of Lemma 2.2. -/
noncomputable def Tsig {n : ℕ} {M : Type*} [Fintype M] [DecidableEq M]
    (s : M → ℝ) (σ : Fin n → Finset M) (x : Fin n → ℝ) : ℝ :=
  if h : (Finset.univ.filter fun π : Fin n → M => ∀ j, π j ∈ σ j).Nonempty then
    (Finset.univ.filter fun π : Fin n → M => ∀ j, π j ∈ σ j).inf' h fun π => makespan s π x
  else 0

end ReserveLB


