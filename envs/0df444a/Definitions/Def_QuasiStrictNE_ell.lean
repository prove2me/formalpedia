-- Prove2me | Definitions.Def_QuasiStrictNE_ell
-- name    : QuasiStrictNE_ell
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T13:06:00.355915+00:00
-- url     : https://prove2.me/theorems/e2d7f9e4-ad2e-43a4-a9c8-c7b2c2ce0336
-- title:
--   Barycenter $\ell_k(I)$ of a face of $\Delta_k$
-- statement:
--   For nonempty $I\subseteq[k]$,
--   $$
--   \ell_k(I)=\frac{1}{|I|}\sum_{i\in I} e_i
--   $$
--   is the barycenter of the face $\mathrm{conv}\{e_i : i\in I\}$ of $\Delta_k$.
--
--   **Formalization Note** For $I=\emptyset$ the formula gives the zero vector; the paper uses $\ell_k$ only on nonempty sets and no theorem of the mission uses the empty case.
-- source:
--   Hansen & Nie, On Existence and Computational Complexity of Quasi-strict Equilibria, arXiv:2611.06350 (preprint, sha256 c265dace…), §3, p.10

import Mathlib

namespace QuasiStrictNE

/-- **The barycenter `ℓk(I)` of a face of `Δk`** (Hansen & Nie, *On Existence and Computational
Complexity of Quasi-strict Equilibria*, arXiv:2611.06350, §3, p.10: "For each nonempty I ⊆ [k],
define ℓk(I) = (1/|I|) ∑_{i∈I} ei. This is the barycenter of the face conv{ei : i ∈ I} of ∆k").

`ell k I` has coordinate `1/|I|` at every `i ∈ I` and `0` elsewhere.

**Formalization Note** Indices are 0-based (`Fin k`). The paper uses `ℓk(I)` only for nonempty `I`;
for `I = ∅` the formula gives the zero vector, a value no theorem of the mission uses. -/
noncomputable def ell (k : ℕ) (I : Finset (Fin k)) : Fin k → ℝ :=
  fun i => if i ∈ I then 1 / (I.card : ℝ) else 0

end QuasiStrictNE


