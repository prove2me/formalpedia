-- Prove2me | Definitions.Def_FMMM_TSM_realOPT
-- name    : FMMM_TSM_realOPT
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-30T01:16:31.895337+00:00
-- url     : https://prove2.me/theorems/e0ee8bf6-fcdf-4c57-b331-d6f5ab3af358
-- title:
--   $\mathrm{OPT}(\hat I)$: maximum matching of the realization graph
-- statement:
--   Let $E$ be the edges between ads $A$ and impression types $I$, and let $\tau_0, \dots, \tau_{n-1}$ be the types of the $n$ drawn impressions. The **realization graph** $\hat G$ has the ads and the $n$ drawn impressions as vertices, with an edge between ad $a$ and draw $t$ whenever $(a, \tau_t) \in E$; repeated draws of the same type are distinct vertices. $\mathrm{OPT}$ is the size of a maximum matching of $\hat G$:
--
--   $$\mathrm{OPT}(\tau) = \max\{|M| : M \subseteq A \times \{0, \dots, n-1\},\ (a, \tau_t) \in E \text{ for } (a, t) \in M,\ \text{no ad and no draw in two pairs of } M\}.$$
--
--   It is the offline optimum against which the online algorithm is compared.
-- source:
--   Feldman, Mehta, Mirrokni, Muthukrishnan, Online Stochastic Matching: Beating 1-1/e, arXiv:0905.4100v1, §2, p. 4 (scenario Î, realization graph Ĝ(Î), OPT(Î))

import Mathlib

namespace FMMM.TSM

/-- **`OPT(Î)`: maximum matching of the realization graph.**
Feldman, Mehta, Mirrokni, Muthukrishnan, *Online Stochastic Matching: Beating 1-1/e*,
arXiv:0905.4100v1, §2, p. 4: "Let D(i) be the set of draws of impression type i that arrive during
the run of the algorithm. We let a scenario Î = ∪_{i∈I} D(i) be the set of impressions. Let Ĝ(Î)
be the "realization" graph, i.e., with node sets A and Î, and edges Ê = {(a, i′) : (a, i) ∈ E,
i′ ∈ D(i)}." OPT(Î) is the size of a maximum matching of Ĝ(Î).

For arrivals `τ : Fin n → I` (draw `t` is an impression of type `τ t`), `realOPT E τ` is the
maximum of `|M|` over sets `M` of pairs `(a, t)` with `(a, τ t) ∈ E` such that no ad and no draw
occurs in two pairs of `M`.

**Formalization Note.** The draws are the vertices `t : Fin n` of the realization graph, so
repeated draws of one type are distinct impressions. -/
noncomputable def realOPT {A I : Type} [Fintype A] [DecidableEq A] [DecidableEq I] {n : ℕ}
    (E : Finset (A × I)) (τ : Fin n → I) : ℕ := by
  classical
  exact ((Finset.univ : Finset (A × Fin n)).powerset.filter
    (fun M => (∀ p ∈ M, (p.1, τ p.2) ∈ E) ∧
      (∀ p ∈ M, ∀ q ∈ M, p.1 = q.1 → p = q) ∧
      (∀ p ∈ M, ∀ q ∈ M, p.2 = q.2 → p = q))).sup Finset.card

end FMMM.TSM


