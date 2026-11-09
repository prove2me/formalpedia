-- Prove2me | Definitions.Def_InflMaxAdapt_Static
-- name    : InflMaxAdapt_Static
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T16:34:39.293735+00:00
-- url     : https://prove2.me/theorems/e8c0e6ed-13ea-4aa0-9248-b9c448ed8e82
-- title:
--   Best static value $\mathrm{Static}_k$
-- statement:
--   For an instance $(V, \mathbf p)$ and a budget $k \in \mathbb N$, the value of the best **static policy** is
--   $$
--   \mathrm{Static}_k(V, \mathbf p) \;=\; \max_{S \subseteq V,\ |S| \le k} \mathbb E[\sigma(S)] .
--   $$
--   A static policy fixes all seeds before any cascade is observed.
--
--   **Formalization Note** The maximum is taken over the finite, nonempty family of seed sets of size at most $k$ (it contains $\emptyset$), so it is attained.
-- source:
--   de Azevedo–Hennebelle, Adaptivity Gaps for Influence Maximization: Percolation and Depletion, STOC 2027 submission (manuscript sha256 67dfe75c…abe5d5), Section 1.1, printed p.2 (PDF p.3)

import Mathlib
import Definitions.Def_InflMaxAdapt_expInfluence

namespace InflMaxAdapt

/-- The value of the best static policy (Section 1.1, printed p.2 = PDF p.3, of de Azevedo–Hennebelle, *Adaptivity Gaps for Influence Maximization: Percolation and Depletion*, STOC 2027 submission manuscript (sha256 67dfe75c…abe5d5)):
`Static_k(V, p) = max_{S ⊆ V, |S| ≤ k} E[σ(S)]`.

**Formalization Note** The maximum over the finite nonempty family `{S : |S| ≤ k}` (it contains `∅`)
is `Finset.sup'`, so it is attained. -/
noncomputable def Static {V : Type} [Fintype V] [DecidableEq V] (p : V → V → ℝ) (k : ℕ) : ℝ :=
  (Finset.univ.filter fun S : Finset V => S.card ≤ k).sup' ⟨∅, by simp⟩ (expInfluence p)

end InflMaxAdapt


