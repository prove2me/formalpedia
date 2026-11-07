-- Prove2me | Definitions.Def_DDNNFNeg_IsCrossing
-- name    : DDNNFNeg_IsCrossing
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T07:18:16.860648+00:00
-- url     : https://prove2.me/theorems/c3aceed2-9bf0-4233-b9b3-a284e1661ca6
-- title:
--   Crossing edge of a partition $(A, B)$
-- statement:
--   For a partition $(A, B)$ of $V = [n]$, an edge $e = \{u, v\}$ is a **crossing edge** if $u \in A$ and $v \in B$.
--
--   **Formalization Note** $B = V \setminus A$; the predicate is stated for any unordered pair.
-- source:
--   Arenas–Broadrick–Liew–Van den Broeck, d-DNNF is Not Polynomially Closed Under Negation, STOC 2027 submission manuscript (sha256 64e4212767c37c44…fbb68), §5.2, p.12

import Mathlib

namespace DDNNFNeg

/-- For a partition `(A, Aᶜ)` of `V = [n]`, the unordered pair `e` is crossing: `e = {u, v}`
with `u ∈ A` and `v ∈ B = Aᶜ` (Arenas–Broadrick–Liew–Van den Broeck, *d-DNNF is Not Polynomially Closed Under Negation*, STOC 2027 submission manuscript (sha256 64e42127…fbb68), §5.2, p.12). -/
def IsCrossing {n : ℕ} (A : Finset (Fin n)) (e : Sym2 (Fin n)) : Prop :=
  ∃ u ∈ A, ∃ v, v ∉ A ∧ e = s(u, v)

instance {n : ℕ} (A : Finset (Fin n)) (e : Sym2 (Fin n)) : Decidable (IsCrossing A e) := by
  unfold IsCrossing; infer_instance

end DDNNFNeg


