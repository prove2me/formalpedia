-- Prove2me | Definitions.Def_InflMaxAdapt_edgeStatic
-- name    : InflMaxAdapt_edgeStatic
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T16:36:17.630589+00:00
-- url     : https://prove2.me/theorems/848bcba7-ac37-4fe8-9cf8-63a0949af3a4
-- title:
--   $\mathrm{Static}_k$ in the undirected-edge representation
-- statement:
--   The best static value in the undirected-edge representation,
--   $$
--   \mathrm{Static}_k \;=\; \max_{S \subseteq V,\ |S| \le k} \mathbb E[\sigma(S)] ,
--   $$
--   with the expected influence computed under independent bond percolation with edge probabilities $q$.
-- source:
--   de Azevedo–Hennebelle, Adaptivity Gaps for Influence Maximization: Percolation and Depletion, STOC 2027 submission (manuscript sha256 67dfe75c…abe5d5), Section 2, printed p.5 (PDF p.6), and footnote 3

import Mathlib
import Definitions.Def_InflMaxAdapt_edgeExpInfluence

namespace InflMaxAdapt

/-- `Static_k` in the undirected-edge representation (Sections 1.1 and 2, footnote 3, printed
pp.2, 5 = PDF pp.3, 6, of de Azevedo–Hennebelle, *Adaptivity Gaps for Influence Maximization: Percolation and Depletion*, STOC 2027 submission manuscript (sha256 67dfe75c…abe5d5)): `max_{S ⊆ V, |S| ≤ k} E[σ(S)]`, as `Finset.sup'` over the finite
nonempty family of seed sets of size at most `k`. -/
noncomputable def edgeStatic {V : Type} [Fintype V] [DecidableEq V] (q : Sym2 V → ℝ) (k : ℕ) : ℝ :=
  (Finset.univ.filter fun S : Finset V => S.card ≤ k).sup' ⟨∅, by simp⟩ (edgeExpInfluence q)

end InflMaxAdapt


