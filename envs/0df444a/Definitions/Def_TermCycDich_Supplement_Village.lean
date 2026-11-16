-- Prove2me | Definitions.Def_TermCycDich_Supplement_Village
-- name    : TermCycDich_Supplement_Village
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T00:47:00.488282+00:00
-- url     : https://prove2.me/theorems/b04c8edd-d094-4f16-95a2-935b578724b6
-- title:
--   $(w,b)$-villages
-- statement:
--   Let $b\ge1$ and $w\ge3$ be integers and let $(G,R)$ be a vital instance of Terminal Cyclability with (unique) solution $S$ and $\mathrm{bidim}(G,R)\le b$. Write $t=6(b+1)^2+1$ and let $\mathrm{apex}$, $\mathrm{depth}$ be the functions $\mathrm{apex}_{2.4}$, $\mathrm{depth}_{2.4}$ of Proposition 2.4. The tuple $(G,R,S,A,\rho,\Sigma,\Delta,\mathcal C)$ is a **$(w,b)$-village** of $(G,R)$ if
--
--   1. $A\subseteq V(G)$ with $|A|\le\mathrm{apex}(3,t,b)$;
--   2. $\Sigma$ is a surface of Euler genus less than $9t^2$;
--   3. $\rho$ is a blank $\Sigma$-rendition of $(G-A,R\setminus A)$ of breadth at most $\tfrac32\,(6(b+1)^2)(18(b+1)^2-1)+(3b+2)(3b+1)-3$ and depth at most $\mathrm{depth}(3,t,b)$;
--   4. $\Delta\subseteq\Sigma$ is a vortex-free $\rho$-aligned disc whose restriction contains $w$ concentric cycles $\mathcal C=\langle C_1,\dots,C_w\rangle$, and no vertex of $N_S(A)$ (the neighbours of $A$ along $S$) lies in the crop by $\Delta$;
--   5. every vortex $v$ of $\rho$ lies in a $\rho$-aligned disc $\Delta_v$, the discs $\Delta_v$ being pairwise disjoint and disjoint from $\Delta$.
--
--   Villages are the first refinement of large-treewidth vital instances in the proof of Theorem 1.3.
--
--   **Formalization Note** $\mathrm{apex}_{2.4}$ and $\mathrm{depth}_{2.4}$ are fixed by the cited Proposition 2.4 only through their existence and a polynomial bound, so the definition takes them as parameters. The breadth bound is computed in $\mathbb N$ as $9(b+1)^2(18(b+1)^2-1)+(3b+2)(3b+1)-3$ (the same integer). The concentric cycles lie in the crop by $\Delta$, with $C_i$-discs inside $\Delta$. A vortex-free disc contains no vortex cell.
-- source:
--   Bentert–Cavallaro–Wiederrecht, A Dichotomy for Terminal Cyclability, arXiv:2611.06234 (held version, sha256 34a10f1a…4d4ea1), §3.3 "Villages", p.26 (PDF 28)

import Mathlib
import Definitions.Def_TermCycDich_IsRCycle
import Definitions.Def_TermCycDich_IsVital
import Definitions.Def_TermCycDich_bidim
import Definitions.Def_TermCycDich_Supplement_Surface
import Definitions.Def_TermCycDich_Supplement_Traces
import Definitions.Def_TermCycDich_Supplement_Society

open scoped Classical

noncomputable section

namespace TermCycDich

namespace Supplement

open GMSTFramework.LocalStructure

/-!
# `(w, b)`-villages

Bentert–Cavallaro–Wiederrecht, *A Dichotomy for Terminal Cyclability*, arXiv:2611.06234 (held
version, sha256 34a10f1a…4d4ea1), §3.3 "Villages", p.26 (PDF 28):

"Let b ≥ 1 and w ≥ 3 be integers and (G, R) be a vital instance of Terminal Cyclability with
solution S such that bidim(G, R) ≤ b. Suppose further that there exists i) a set A ⊆ V(G) with
|A| ≤ apex2.4(3, 6·(b+1)²+1, b) and ii) a surface Σ of Euler genus less than 9(6·(b+1)²+1)² such
that iii) (G − A, R ∖ A) has a blank Σ-rendition ρ with breadth at most
3/2(6·(b+1)²)(18·(b+1)²−1) + (3b+2)(3b+1) − 3, depth at most depth2.4(3, 6·(b+1)²+1, b), and
there exists a vortex-free, ρ-aligned disc ∆ ⊆ Σ such that the restriction of ρ to ∆ contains a
sequence C = ⟨C₁, …, C_w⟩ of w concentric cycles where no vertex of N_S(A) is contained in the crop
of G by ∆. Moreover, if we denote by V the vortices of ρ, then for every v ∈ V there exists a
ρ-aligned disc ∆_v such that ∆_v contains v and is disjoint from ∆ and from ∆_{v'} for all
v' ∈ V ∖ {v}. We refer to (G, R, S, A, ρ, Σ, ∆, C) as a (w, b)-village of (G, R)."

**Formalization Note**
* `apex2.4` and `depth2.4` are the functions of the cited Proposition 2.4 [GPW26], which the paper
  fixes only by their existence and the bound `∈ poly(k + t + r)`; `IsVillage` takes them as the
  parameters `apex depth : ℕ → ℕ → ℕ → ℕ`.
* `3/2 · (6(b+1)²)(18(b+1)²−1) = 9(b+1)²(18(b+1)²−1)`, an integer; the breadth bound is computed in
  `ℕ` (`(3b+2)(3b+1) ≥ 20`, so the `− 3` never truncates).
* `S` is a closed walk with `IsRCycle G R S` and `(G, R)` is vital (`S` is then its unique solution,
  up to the choice of base point and direction).
* `G − A` is the public `minusVerts G A` (a `G.Subgraph`); the rendition is of `G − A` and is
  blank for `R ∖ A`. `N_S(A)` is the set of vertices joined to a vertex of `A` by an edge of `S`.
* "The restriction of `ρ` to `Δ` contains `w` concentric cycles" is `IsConcentricIn ρ Δ C D T`:
  cycles of the crop by `Δ`, grounded, with nested `Cᵢ`-discs `Dᵢ ⊆ Δ` (the `C`-disc chosen inside
  the specified disc, p.20).
* "Vortex-free" disc: no vortex cell lies in `Δ`. The discs `Δ_v` are one family `Dv` indexed by
  the vortex cells.
-/

variable {V : Type} [Fintype V] [DecidableEq V]

/-- `N_S(A)`: the vertices joined to a vertex of `A` by an edge of the closed walk `S`. -/
def nbrOn {G : SimpleGraph V} {u : V} (S : G.Walk u u) (A : Set V) : Set V :=
  {v | ∃ a ∈ A, s(a, v) ∈ S.edges}

/-- `(G, R, S, A, ρ, Σ, Δ, C)` is a `(w, b)`-village of `(G, R)`, relative to the functions
`apex = apex2.4` and `depth = depth2.4`; the surface `Σ` is the type `X`. -/
def IsVillage (apex depth : ℕ → ℕ → ℕ → ℕ) (w b : ℕ) (G : SimpleGraph V) (R : Set V) {u : V}
    (S : G.Walk u u) (A : Finset V) (X : Type) [TopologicalSpace X]
    (ρ : Rendition X (minusVerts G (A : Set V))) (Δ : Set X) (C : Fin w → G.Subgraph) : Prop :=
  1 ≤ b ∧ 3 ≤ w ∧ IsVital G R ∧ IsRCycle G R S ∧ bidim G R ≤ b ∧
  A.card ≤ apex 3 (6 * (b + 1) ^ 2 + 1) b ∧
  IsSurface X ∧ HasEulerGenusLT X (9 * (6 * (b + 1) ^ 2 + 1) ^ 2) ∧
  ρ.IsBlank (R \ (A : Set V)) ∧
  ρ.breadth ≤ 9 * (b + 1) ^ 2 * (18 * (b + 1) ^ 2 - 1) + (3 * b + 2) * (3 * b + 1) - 3 ∧
  ρ.RenditionDepthLE (depth 3 (6 * (b + 1) ^ 2 + 1) b) ∧
  ρ.IsAlignedDisk Δ ∧ (∀ c ∈ ρ.vortices, ¬ c ⊆ Δ) ∧
  (∃ D T : Fin w → Set X, ρ.IsConcentricIn Δ C D T) ∧
  Disjoint (nbrOn S (A : Set V)) (ρ.crop Δ).verts ∧
  ∃ Dv : Set X → Set X, ∀ c ∈ ρ.vortices,
    ρ.IsAlignedDisk (Dv c) ∧ c ⊆ Dv c ∧ Disjoint (Dv c) Δ ∧
      ∀ c' ∈ ρ.vortices, c' ≠ c → Disjoint (Dv c) (Dv c')

end Supplement

end TermCycDich


