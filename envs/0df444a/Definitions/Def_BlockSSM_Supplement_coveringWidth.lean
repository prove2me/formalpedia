-- Prove2me | Definitions.Def_BlockSSM_Supplement_coveringWidth
-- name    : BlockSSM_Supplement_coveringWidth
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T05:02:16.34792+00:00
-- url     : https://prove2.me/theorems/f3fafedf-6692-4cec-9e1c-ef23f9bc3768
-- title:
--   The covering width $w^{\twoheadrightarrow}(G)$
-- statement:
--   For a finite group $H$, $w(H)$ is the least positive integer $b$ for which $H$ has a **jointly faithful** family of irreducible complex representations (the intersection of their kernels is trivial) all of degree at most $b$; in particular $w(1)=1$. The **covering width** of $G$ is
--   $$
--   w^{\twoheadrightarrow}(G)=\min_{H\twoheadrightarrow G} w(H),
--   $$
--   the minimum over all finite groups $H$ surjecting onto $G$. The class $V_b=\{G: w^{\twoheadrightarrow}(G)\le b\}$ (Proposition 3) is used by the cascade theorem.
--
--   **Formalization Note** The two minima are merged into one infimum in $\mathbb N\cup\{\infty\}$ over $b\ge1$. Families are finite, which loses nothing for a finite group (finitely many kernels). This is the paper's definition, not its later characterization $\min\{b: D_b(G)<\infty\}$.
-- source:
--   C. Geng, The State Complexity of Block-Diagonal State Space Models, STOC 2027 submission manuscript (sha256 f9071794…), Definition 2, p.2 (PDF p.3)

import Mathlib

universe u

namespace BlockSSM.Supplement

/-- **The covering width `w↠(G)`.** Geng, *The State Complexity of Block-Diagonal State Space Models*, STOC 2027 submission manuscript (sha256 f9071794…), Definition 2, p.2 (PDF p.3): "For a finite group H, let
w(H) be the least positive integer b for which a jointly faithful family of irreducible complex
representations has all degrees at most b. In particular, w(1) = 1. Define w↠(G) = min_{H↠G} w(H)."

The two minima are merged: `w↠(G)` is the least `b ≥ 1` such that some finite group `H` surjects
onto `G` and has a jointly faithful family of irreducible complex representations of degrees at most
`b` (jointly faithful: an element acting trivially in every member is the identity).

**Formalization Note.** The infimum is taken in `ℕ∞`. A family is finite (indexed by `Fin k`):
for a finite group the kernels are finitely many subgroups, so every jointly faithful family has a
finite jointly faithful subfamily. The empty family (`k = 0`) is jointly faithful exactly for the
trivial group, which with `1 ≤ b` gives `w(1) = 1`. A `d`-dimensional representation is taken on
`Fin d → ℂ` and the cover in `Type`, as in `BlockSSM.coverDim`. This is the paper's definition,
not the characterization `min {b : D_b(G) < ∞}`, which the paper states as a consequence. -/
noncomputable def coveringWidth (G : Type u) [Group G] : ℕ∞ :=
  sInf {b : ℕ∞ | 1 ≤ b ∧ ∃ (H : Type) (_ : Group H) (_ : Finite H) (φ : H →* G),
    Function.Surjective φ ∧ ∃ (k : ℕ) (d : Fin k → ℕ) (ρ : ∀ j, Representation ℂ H (Fin (d j) → ℂ)),
      (∀ j, (ρ j).IsIrreducible) ∧ (∀ j, (d j : ℕ∞) ≤ b) ∧ ∀ h : H, (∀ j, ρ j h = 1) → h = 1}

end BlockSSM.Supplement


