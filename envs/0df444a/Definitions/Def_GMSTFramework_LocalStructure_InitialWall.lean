-- Prove2me | Definitions.Def_GMSTFramework_LocalStructure_InitialWall
-- name    : GMSTFramework_LocalStructure_InitialWall
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-10T19:04:26.208401+00:00
-- url     : https://prove2.me/theorems/e790d5a9-e841-4e22-a432-54dc1f8d014c
-- title:
--   The outcome of Theorem 6.4: a sphere-rendition with one vortex and an initial representative extended surface-wall
-- statement:
--   For a sphere-rendition $\rho$ of $G-A$, an extended $k$-surface-wall $D$ and $I\subseteq\mathbb N$: $\rho$ has a unique vortex $c_0$; $D$ has signature $(0,0,f,1)$ for some $f\le 4rp$ and lies in $G-A$; (i) $D$ is grounded in $\rho$; (ii) the tangle induced by $D$ is a truncation of the tangle induced by $M$; (iii) $\bar c_0$ lies in the interior of the disk bounded by the trace of the inner cycle of the vortex-segment of $D$ that avoids the simple cycle of $D$; (iv) $I=\bigcup\{\varphi(\mathrm{protrusion}_{\rho,A}(c)):c\text{ simple}\}\subseteq[p]$ and $\rho$ is $I$-blank w.r.t. $\varphi$ and $A$; (v) if $I\ne\emptyset$, $D$ represents $\varphi$ w.r.t. $A$ with strength $r$.
--
--   **Formalization Note.** "$D$ in $\rho$" is $D^-\le G-A$ and $V(D)\cap A=\emptyset$.
-- source:
--   Gorsky, Protopapas, Wiederrecht, A unifying framework for Graph Minor Structure Theorems with polynomial bounds, STOC 2027 submission (manuscript sha256 b2ee466d…), Theorem 6.4, p. 51 (PDF 54)

import Mathlib
import Definitions.Def_GMSTFramework_LocalStructure_Algorithms

open scoped Classical

noncomputable section

namespace GMSTFramework.LocalStructure

/-!
# The outcome of Theorem 6.4 (an initial representative surface-wall)

Gorsky, Protopapas, Wiederrecht, *A unifying framework for Graph Minor Structure Theorems with
polynomial bounds*, STOC 2027 submission (manuscript sha256 b2ee466d…), Theorem 6.4, p. 51
(PDF 54).

`IsInitialWall b p φ G χ label A M k r ρ D I` says: `ρ` is a sphere-rendition of `G - A` with a unique
vortex `c₀`, `D` is an extended `k`-surface-wall of `G - A` with signature `(0, 0, f, 1)` for some
`f ≤ 4rp`, and
i) `D` is grounded in `ρ`;
ii) the tangle induced by `D` is a truncation of the tangle induced by `M`;
iii) `c̄₀` lies in the interior of the disk bounded by the trace of the inner cycle of the unique
vortex-segment of `D` that avoids (the trace of) the simple cycle of `D`;
iv) `I = ⋃ {φ(protrusion_{ρ,A}(c)) : c simple} ⊆ [p]` and `ρ` is `I`-blank with respect to `φ` and `A`;
v) if `I ≠ ∅`, `D` represents `φ` (that is, `I`) with respect to `A` in `ρ` with strength `r`.
"`D` in `ρ`" is encoded as `D⁻ ≤ G - A` and `V(D) ∩ A = ∅`.
-/

variable {V : Type} [Fintype V] [DecidableEq V]

/-- The conclusion of Theorem 6.4 for the rendition `ρ`, the wall `D` and the colour set `I`. -/
def IsInitialWall (b p : ℕ) (φ : BGraph → Finset ℕ) (G : SimpleGraph V) (χ : V → Finset ℕ)
    (label : V ≃ Fin (Fintype.card V)) (A : Finset V) {m : ℕ} (M : Mesh G m m) (k r : ℕ)
    (ρ : Rendition TheSphere (minusVerts G A)) (D : SurfaceWall G k) (I : Finset ℕ) : Prop :=
  ρ.vortices.ncard = 1 ∧ (∃ f, f ≤ 4 * r * p ∧ D.HasSignature 0 0 f 1) ∧
  D.sub ≤ minusVerts G A ∧ Disjoint (A : Set V) D.verts ∧
  -- i)
  ρ.GroundedSub D.sub ∧
  -- ii)
  IsTruncation D.tangle M.tangle ∧
  -- iii)
  (∀ c₀ ∈ ρ.vortices, ∀ i, D.IsVortexSeg i →
    ∃ T Dk Ts, ρ.IsTraceCycle (D.nestCycle i ⟨0, by have := D.two_le; omega⟩) T ∧
      IsDiskWithBoundary Dk T ∧ ρ.IsTraceCycle D.simpleCycle Ts ∧ Disjoint Dk Ts ∧
      closure c₀ ⊆ Dk \ T) ∧
  -- iv)
  (I : Set ℕ) = (⋃ c ∈ {c | ρ.IsSimple c}, (φ (protrusion G χ label A ρ c) : Set ℕ)) ∧
  I ⊆ Finset.Icc 1 p ∧ IsIBlank φ G χ label A ρ I ∧
  -- v)
  (I.Nonempty → Represents φ G χ label A ρ D I r)

end GMSTFramework.LocalStructure


