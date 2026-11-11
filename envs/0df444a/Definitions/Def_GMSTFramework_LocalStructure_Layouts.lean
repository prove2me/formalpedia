-- Prove2me | Definitions.Def_GMSTFramework_LocalStructure_Layouts
-- name    : GMSTFramework_LocalStructure_Layouts
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-10T19:04:13.629538+00:00
-- url     : https://prove2.me/theorems/73739879-2ea0-4691-b264-6742433ebd7a
-- title:
--   Well-represented $\Sigma$-landscapes (L1–L8) and well-represented $k$-$(a,\mathsf b,d,r,w')$-$\Sigma$-layouts centred at a mesh; certificates of the outcomes of Theorem 8.2 (§8.1)
-- statement:
--   Let $(G,\chi)$ be $q$-colorful, $\varphi$ a $(b,q,p)$-colour-explorer, $\Sigma$ a surface of Euler-genus $g=2h+c$ with $c\ne0$ iff $\Sigma$ is non-orientable, $D\subseteq G$ an extended $k$-surface-wall with signature $(h,c,f,\mathsf b)$, $A\subseteq V(G)\setminus V(D)$, $I\subseteq[p]$ and $W\subseteq G-A$ a $w$-mesh. $(A,W,D,I,\rho)$ is a **well-represented $\Sigma$-landscape of detail $k$** if L1 $|A^{\mathrm{major}}|+3\le b$; L2 $\rho$ is a $\Sigma$-rendition of $(G-A,\chi)$ with $\mathsf b$ vortices, $I$-blank w.r.t. $\varphi$ and $A^{\mathrm{major}}$; L3 $D$, $W$ grounded; L4 $W$ flat and $D$ represents $\varphi$ w.r.t. $A^{\mathrm{major}}$ with strength $r$; L5 the disk bounded by the trace of the simple cycle avoids the traces of the other base cycles; L6 $\mathcal T_D\subseteq\mathcal T_W$; L7 the traces of the nest cycles of vortex-segments are contractible; L8 a bijection between the $\mathsf b$ vortices and the vortex-segments $S_v$ such that $v$ is the unique vortex in the disk of the inner cycle of $S_v$ avoiding the simple cycle. $(G,\chi)$ with $M$ and $\varphi$ has a **well-represented $k$-$(a,\mathsf b,d,r,w')$-$\Sigma$-layout centred at $M$** if there are $A$, $|A|\le a$, $I\subseteq[p]$ and a submesh $M'\subseteq M$ with a landscape $(A,M',D,I,\rho)$ of detail $k$, breadth $\mathsf b$, strength $r$ and depth $d$, every vortex with a linear decomposition of adhesion $\le d$, and $M'$ a $w$-mesh with $w\ge a+\mathsf b(2d+1)+6+w'$.
--
--   **Formalization Note.** In Lean the breadth is `br`. The preamble ranges $k,w\ge4$ are not conditions (finding I1). L4 is `Represents` with $J=I$ also for $I=\emptyset$ (finding I2: then $D$ has no flap-segment). The layout's breadth $\mathsf b$ and depth $d$ are upper bounds (breadth $\mathsf b'\le\mathsf b$, depth $\le d$) and the parameters enter $w\ge a+\mathsf b(2d+1)+6+w'$. L5 and L7 are required of every trace. `ModelCertificate` / `LayoutCertificate` describe outputs: `[0]` and the branch sets of a $K_t$-model controlled by $\mathcal T_M$, or `[1]`, the apex set, $I$, the submesh, the surface-wall and the cells of $\rho$ of a layout in some surface where $K_t$ does not embed.
-- source:
--   Gorsky, Protopapas, Wiederrecht, A unifying framework for Graph Minor Structure Theorems with polynomial bounds, STOC 2027 submission (manuscript sha256 b2ee466d…), p. 84–85 (PDF 87–88), §8.1

import Mathlib
import Definitions.Def_GMSTFramework_LocalStructure_Algorithms

open scoped Classical

noncomputable section

namespace GMSTFramework.LocalStructure

/-!
# Well-represented landscapes and layouts

Gorsky, Protopapas, Wiederrecht, *A unifying framework for Graph Minor Structure Theorems with
polynomial bounds*, STOC 2027 submission (manuscript sha256 b2ee466d…), §8.1 p. 84–85
(PDF 87–88). (Italic `b` is the colour-explorer's boundary bound; sans-serif `𝖻` the breadth.)

* `IsLandscape` (`Λ = (A, W, D, I, ρ)` a well-represented `Σ`-landscape of detail `k`, strength `r`
  and breadth `𝖻`), conditions L1–L8 together with the setting of the definition: `Σ` has
  Euler-genus `2h + c`, `c ≠ 0` iff `Σ` is non-orientable, `D` an extended `k`-surface-wall of
  signature `(h, c, f, 𝖻)`, `A ∩ V(D) = ∅`, `I ⊆ [p]`, `W ⊆ G - A` a `w`-mesh. The preamble's ranges
  `k, w ≥ 4` are context and not conditions (finding I1: Theorem 8.2 uses `k ≥ 3`).
  - L4 uses `Represents` for `J = I` also when `I = ∅` (finding I2: then `D` has no flap-segment).
  - L5, L7: "the trace" is read for every trace (the property is invariant under the push).
  - L8: a bijection between the vortices of `ρ` and the vortex-segments of `D`.
* `IsLayoutWitness`, `HasLayout` (a well-represented `k-(a, 𝖻, d, r, w')-Σ`-layout centred at `M`):
  `|A| ≤ a`, `I ⊆ [p]`, a `w`-submesh `M' ⊆ M` with `w ≥ a + 𝖻(2d + 1) + 6 + w'`, and a
  landscape `(A, M', D, I, ρ)` of detail `k`, strength `r`, **breadth at most `𝖻` and depth at most
  `d`** (the reading of "breadth `𝖻`, depth `d`" in which the layout's parameters are bounds, as
  "`|A|` at most `a`" is), every vortex with a linear decomposition of adhesion at most `d`.
* `LayoutCertificate`: the output of the algorithm of Theorem 8.2 in case ii): the apex set, `I`, the
  submesh, the surface-wall and the cells of the rendition; it is valid when some layout realizes it.
-/

variable {V : Type} [Fintype V] [DecidableEq V]

/-- `(A, W, D, I, ρ)` is a well-represented `Σ`-landscape of detail `k` (the order of `D`), strength
`r` and breadth `𝖻`, where `D` has signature `(h, c, f, 𝖻)`. -/
def IsLandscape (b p : ℕ) (φ : BGraph → Finset ℕ) (G : SimpleGraph V) (χ : V → Finset ℕ)
    (label : V ≃ Fin (Fintype.card V)) (X : Type) [TopologicalSpace X] (r : ℕ)
    {k w : ℕ} (A : Finset V) (W : Mesh G w w) (D : SurfaceWall G k) (I : Finset ℕ)
    (ρ : Rendition X (minusVerts G A)) (h c f br : ℕ) : Prop :=
  -- setting
  HasEulerGenus X (2 * h + c) ∧ (c ≠ 0 ↔ IsNonOrientable X) ∧ D.HasSignature h c f br ∧
  Disjoint (A : Set V) D.verts ∧ I ⊆ Finset.Icc 1 p ∧ W.sub ≤ minusVerts G A ∧
  -- L1
  (majorApices A ρ).card + 3 ≤ b ∧
  -- L2
  ρ.vortices.ncard = br ∧ IsIBlank φ G χ label (majorApices A ρ) ρ I ∧
  -- L3
  ρ.GroundedSub D.sub ∧ ρ.GroundedSub W.sub ∧
  -- L4
  ρ.FlatSub W.sub ∧ Represents φ G χ label (majorApices A ρ) ρ D I r ∧
  -- L5
  (∃ Ts Dk : Set X, ρ.IsTraceCycle D.simpleCycle Ts ∧ IsDiskWithBoundary Dk Ts ∧
    ∀ i : Fin k, i.val ≠ k - 1 → ∀ T', ρ.IsTraceCycle (D.baseCycle i) T' → Disjoint Dk T') ∧
  -- L6
  IsTruncation D.tangle W.tangle ∧
  -- L7
  (∀ i, D.IsVortexSeg i → ∀ j : Fin k, ∀ T, ρ.IsTraceCycle (D.nestCycle i j) T →
    IsContractibleCurve T) ∧
  -- L8
  (∃ e : ρ.vortices ≃ {i : Fin D.kinds.length // D.IsVortexSeg i},
    ∀ v : ρ.vortices, ∃ T₁ Dk Ts : Set X,
      ρ.IsTraceCycle (D.nestCycle (e v).1 ⟨0, by have := D.two_le; omega⟩) T₁ ∧
      IsDiskWithBoundary Dk T₁ ∧ ρ.IsTraceCycle D.simpleCycle Ts ∧ Disjoint Dk Ts ∧
      (v : Set X) ⊆ Dk ∧ ∀ v' ∈ ρ.vortices, v' ⊆ Dk → v' = v)

/-- The witnesses of a well-represented `k-(a, 𝖻, d, r, w')-Σ`-layout centred at `M`. -/
def IsLayoutWitness (b p : ℕ) (φ : BGraph → Finset ℕ) (G : SimpleGraph V) (χ : V → Finset ℕ)
    (label : V ≃ Fin (Fintype.card V)) {m : ℕ} (M : Mesh G m m) (X : Type) [TopologicalSpace X]
    (k a br d r w' : ℕ) (A : Finset V) (I : Finset ℕ) {w : ℕ} (M' : Mesh G w w)
    (D : SurfaceWall G k) (ρ : Rendition X (minusVerts G A)) : Prop :=
  A.card ≤ a ∧ I ⊆ Finset.Icc 1 p ∧ M'.IsSubmeshOf M ∧ a + br * (2 * d + 1) + 6 + w' ≤ w ∧
    (∃ h c f br', br' ≤ br ∧ IsLandscape b p φ G χ label X r A M' D I ρ h c f br') ∧
    RenditionDepthLE ρ d ∧ VorticesAdhesionLE ρ d

/-- `(G, χ)` with the mesh `M` and the `(b, q, p)`-colour-explorer `φ` has a well-represented
`k-(a, 𝖻, d, r, w')-Σ`-layout centred at `M`. -/
def HasLayout (b p : ℕ) (φ : BGraph → Finset ℕ) (G : SimpleGraph V) (χ : V → Finset ℕ)
    (label : V ≃ Fin (Fintype.card V)) {m : ℕ} (M : Mesh G m m) (X : Type) [TopologicalSpace X]
    (k a br d r w' : ℕ) : Prop :=
  ∃ (A : Finset V) (I : Finset ℕ) (w : ℕ) (M' : Mesh G w w) (D : SurfaceWall G k)
    (ρ : Rendition X (minusVerts G A)),
    IsLayoutWitness b p φ G χ label M X k a br d r w' A I M' D ρ

/-- The output list `out` is a certificate of a layout as in `HasLayout` in some surface in which
`K_t` does not embed: `out = [1] ++ A ++ I ++ M' ++ D ++ cells(ρ)` for such a layout. -/
def LayoutCertificate (b p t : ℕ) (φ : BGraph → Finset ℕ) (G : SimpleGraph V)
    (χ : V → Finset ℕ) (label : V ≃ Fin (Fintype.card V)) {m : ℕ} (M : Mesh G m m)
    (k a br d r w' : ℕ) (out : List ℚ) : Prop :=
  ∃ (X : Type) (_ : TopologicalSpace X) (A : Finset V) (I : Finset ℕ) (w : ℕ) (M' : Mesh G w w)
    (D : SurfaceWall G k) (ρ : Rendition X (minusVerts G A)) (ks : List ℕ)
    (es zl cells : List (List ℕ)),
    ¬ EmbedsIn (SimpleGraph.completeGraph (Fin t)) X ∧
    IsLayoutWitness b p φ G χ label M X k a br d r w' A I M' D ρ ∧
    DescribesWall label D ks es zl ∧ DescribesRendition label ρ cells ∧
    out = [1] ++ encNats (namesOf label (A : Set V)) ++ encNats (sortedNats I) ++
      encMesh label M' ++ encWall k ks es zl ++ encNested cells

/-- The output list `out` is a certificate of a `K_t`-minor-model controlled by `M`:
`out = [0] ++ branch sets`. -/
def ModelCertificate (t : ℕ) (G : SimpleGraph V) (label : V ≃ Fin (Fintype.card V)) {m : ℕ}
    (M : Mesh G m m) (out : List ℚ) : Prop :=
  ∃ (μ : (SimpleGraph.completeGraph (Fin t)).Minor G) (bs : List (List ℕ)),
    ControlledBy μ M.tangle ∧ DescribesModel label (Fintype.equivFin (Fin t)) μ bs ∧
    out = [0] ++ encNested bs

end GMSTFramework.LocalStructure


