-- Prove2me | Definitions.Def_MatroidOptGame_unionMinBaseWeight
-- name    : MatroidOptGame_unionMinBaseWeight
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T12:51:27.28932+00:00
-- url     : https://prove2.me/theorems/5a978908-d140-438a-8b0f-cbe0b9906293
-- title:
--   Minimum base weight of the union $w(B_{\min}(M\vee M,w))$
-- statement:
--   $w(B_{\min}(M \vee M, w))$ is the minimum weight of a base of the union $M \vee M$, that is, of a set $I \cup J$ ($I, J$ independent in $M$) of the maximum size $r_{M\vee M}(E)$:
--   $$
--   w(B_{\min}(M \vee M, w)) = \min\{ w(F) : F \text{ independent in } M\vee M,\ |F| = r_{M\vee M}(E)\}.
--   $$
--
--   **Formalization Note** The bases of the matroid $M \vee M$ are its independent sets of maximum size, so this is the minimum base weight of $M \vee M$. The set is nonempty, so the infimum in $\mathbb N$ is a minimum.
-- source:
--   Jahn–Koolyk–Ostrovsky–Rabani–Schulman, Approximation and Hardness in Optimization Games, STOC 2027 submission (manuscript sha256 7ad38b1a…dee74), Section 2.1, p.4

import Mathlib
import Definitions.Def_MatroidOptGame_weight
import Definitions.Def_MatroidOptGame_UnionIndep
import Definitions.Def_MatroidOptGame_unionRank

namespace MatroidOptGame

/-- `w(B_min(M ∨ M, w))`: the minimum weight of a base of the union `M ∨ M`, i.e. of a
union-independent set of maximum size `r_{M∨M}(E)`.

Source: Jahn–Koolyk–Ostrovsky–Rabani–Schulman, *Approximation and Hardness in Optimization Games*,
STOC 2027 submission (manuscript sha256 7ad38b1a…dee74), Section 2.1, p.4 (definition of `δ`).

**Formalization Note.** Since `M ∨ M` is a matroid (p.20), its bases are exactly the
union-independent sets of size `r_{M∨M}(E)`. The set below is nonempty on a finite type (the
maximum in `unionRank` is attained), so the `sInf` is a minimum. -/
noncomputable def unionMinBaseWeight {α : Type*} [Fintype α] [DecidableEq α] (M : Matroid α) (w : α → ℕ) : ℕ :=
  sInf {x : ℕ | ∃ F : Finset α, UnionIndep M F ∧ F.card = unionRank M ∧ weight w F = x}

end MatroidOptGame


