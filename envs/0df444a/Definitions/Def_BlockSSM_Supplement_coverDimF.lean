-- Prove2me | Definitions.Def_BlockSSM_Supplement_coverDimF
-- name    : BlockSSM_Supplement_coverDimF
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T05:04:28.595586+00:00
-- url     : https://prove2.me/theorems/e0ad56c2-82fd-4c23-9942-1e7b46ec52bb
-- title:
--   The cover invariant $D_{b,F}(G)$ over a field $F$
-- statement:
--   Let $F$ be a field. $D_{b,F}(G)$ is the least dimension of a faithful representation $V$ over $F$ of a finite group $H$ surjecting onto $G$, all of whose $F$-irreducible constituents have degree at most $b$; it is $\infty$ when no such pair exists:
--   $$
--   D_{b,F}(G)=\min_{\substack{\phi:H\twoheadrightarrow G,\ V\text{ faithful over }F\\ \text{all $F$-irreducible degrees in }V\le b}}\dim_F V .
--   $$
--
--   This is the group side of Theorem 30.
--
--   **Formalization Note** The degree condition is stated for $F$-irreducible subrepresentations; over a field of characteristic zero, Maschke's theorem makes every irreducible constituent isomorphic to one, so this is the paper's condition. $V=F^d$ and $H$ is taken in the lowest universe, as for $D_b$.
-- source:
--   C. Geng, The State Complexity of Block-Diagonal State Space Models, STOC 2027 submission manuscript (sha256 f9071794…), Theorem 30, p.18 (PDF p.19), with Definition 2, p.2 (PDF p.3)

import Mathlib

universe u v

namespace BlockSSM.Supplement

/-- All `F`-irreducible subrepresentations of `V` have dimension at most `b` (the side condition
of `D_{b,F}`, with "irreducible constituents … taken over F"). -/
def IrrepDegreesLEF (F : Type v) [Field F] {H V : Type*} [Group H] [AddCommGroup V] [Module F V]
    (ρ : Representation F H V) (b : ℕ∞) : Prop :=
  ∀ W : Subrepresentation ρ, W.toRepresentation.IsIrreducible →
    (Module.finrank F W.toSubmodule : ℕ∞) ≤ b

/-- **`D_{b,F}(G)`.** Geng, *The State Complexity of Block-Diagonal State Space Models*, STOC 2027 submission manuscript (sha256 f9071794…), Theorem 30, p.18 (PDF p.19): Definition 2's `D_b(G)` with
"representations, and irreducible constituents … taken over F": the least `dim V` over finite covers
`φ : H ↠ G` and faithful `F`-representations `V` of `H` all of whose `F`-irreducible constituents
have degree at most `b`; `∞` if none.

**Formalization Note.** Infimum in `ℕ∞`. A `d`-dimensional representation is on `Fin d → F` and
the cover `H` in `Type`, as in `BlockSSM.coverDim`. For a finite group and a field of
characteristic zero, Maschke's theorem makes every irreducible constituent isomorphic to an
irreducible subrepresentation, so the side condition is the paper's. `F` need not be algebraically
closed. -/
noncomputable def coverDimF (F : Type v) [Field F] (G : Type u) [Group G] (b : ℕ∞) : ℕ∞ :=
  sInf {D : ℕ∞ | ∃ d : ℕ, D = (d : ℕ∞) ∧
    ∃ (H : Type) (_ : Group H) (_ : Finite H) (φ : H →* G) (ρ : Representation F H (Fin d → F)),
      Function.Surjective φ ∧ Function.Injective ρ ∧ IrrepDegreesLEF F ρ b}

end BlockSSM.Supplement


