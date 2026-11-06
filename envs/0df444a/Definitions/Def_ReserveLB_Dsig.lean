-- Prove2me | Definitions.Def_ReserveLB_Dsig
-- name    : ReserveLB_Dsig
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T02:28:57.1362+00:00
-- url     : https://prove2.me/theorems/9262ba8f-bedc-41db-bc58-f4302f160f60
-- title:
--   Fractional volume threshold $D_\sigma(x)$
-- statement:
--   For a reservation $\sigma$, machine speeds $s_i$ and sizes $x_j$, the **fractional volume threshold** is
--   $$
--   D_\sigma(x) = \max_{\emptyset \ne A \subseteq M}\ \frac{\sum_{j:\ \sigma(j) \subseteq A} x_j}{\sum_{i \in A} s_i},
--   $$
--   the largest ratio between the work trapped in a machine set $A$ (jobs all of whose reserved machines lie in $A$) and the total speed of $A$.
--
--   It is the least time in which the sizes can be routed fractionally along the reserved arcs (a max-flow threshold), a lower bound on the integral cost, and the reference value of Lemma 2.1.
--
--   **Formalization Note** The maximum is over the nonempty subsets of a finite machine type.
-- source:
--   Mahboub–Rahgoshay, Stochastic Load Balancing with Strict Machine-Reservation Budgets, manuscript of Oct. 30, 2026 (sha256 aefe1158e8000194527b025b3c358dcb571c94e1038c0bfdd295c6119bc9f630), Section 2, p.3 (fractional volume threshold)

import Mathlib

namespace ReserveLB

/-- **Fractional volume threshold `D_σ(x)`.**
Mahboub–Rahgoshay, *Stochastic Load Balancing with Strict Machine-Reservation Budgets*,
manuscript of Oct. 30, 2026 (sha256 aefe1158…), Section 2, p.3: "For a fixed graph and sizes, the fractional volume threshold is
Dσ(x) = max_(∅≠A⊆M) Σ_(j: σ(j)⊆A) xj / Σ_(i∈A) si".

`Dsig s σ x` is the maximum over nonempty machine sets `A` of the volume of the jobs whose whole
reservation lies in `A`, divided by the total speed of `A`.

**Formalization Note.** The maximum is `Finset.sup'` over the nonempty subsets of the finite machine
type; the value `0` on an empty machine type is never used. -/
noncomputable def Dsig {n : ℕ} {M : Type*} [Fintype M] [DecidableEq M]
    (s : M → ℝ) (σ : Fin n → Finset M) (x : Fin n → ℝ) : ℝ :=
  if h : ((Finset.univ : Finset (Finset M)).filter fun A => A.Nonempty).Nonempty then
    ((Finset.univ : Finset (Finset M)).filter fun A => A.Nonempty).sup' h fun A =>
      (∑ j ∈ Finset.univ.filter (fun j => σ j ⊆ A), x j) / ∑ i ∈ A, s i
  else 0

end ReserveLB


