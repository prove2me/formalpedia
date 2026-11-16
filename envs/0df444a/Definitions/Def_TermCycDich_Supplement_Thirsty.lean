-- Prove2me | Definitions.Def_TermCycDich_Supplement_Thirsty
-- name    : TermCycDich_Supplement_Thirsty
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T00:47:55.217796+00:00
-- url     : https://prove2.me/theorems/3e6e14e7-864c-43be-8ba5-0d7f7ec2c68f
-- title:
--   Wells (tight, drained, dry) and thirsty villages
-- statement:
--   Let $(G,R,S,A,\rho,\Sigma,\Delta,\mathcal C)$ be a $(w,b)$-village with $\mathcal C=\langle C_1,\dots,C_w\rangle$ and $C_i$-discs $\Delta_1\subsetneq\cdots\subsetneq\Delta_w$. It is **thirsty** if:
--
--   1. inside $\Delta$ every cell of $\rho$ represents a single edge or an isolated vertex;
--   2. the cycles of $\mathcal C$ are **tight** (for every $i$ there is no grounded $C_i$-path whose trace lies in $\Delta_i\setminus\Delta_{i-1}$, with $\Delta_0=\emptyset$) and their traces lie in the interior of $\Delta$;
--   3. with $B$ the vertices represented on $\mathrm{bd}(\Delta)$ and $\mathcal P$ the set of subpaths $P\subseteq S$ that are nontrivial $B$-paths in the crop by $\Delta$ meeting $V(\mathcal C)$ (the **legs**), $W=\bigcup\mathcal P\cup\bigcup\mathcal C$ and $V(\Omega)=V(W)\cap B$, the tuple $(W,\Omega,\rho_\Delta,\mathcal C,\mathcal P)$ is a **dry $w$-well**:
--      - the legs are pairwise internally vertex-disjoint nontrivial $V(\Omega)$-paths (prewell);
--      - no leg contains a grounded $C_1$-path whose trace, except for its ends, lies in the interior of $\Delta_1$ (well);
--      - (drained) if a leg $P$ meets $C_i$ with $i<w$, another leg $Q$ with trace inside the interior $\Delta_P$ of $P$ (the closure of the component of $\Delta$ minus the trace of $P$ that avoids the trace of $C_1$) meets $C_{i+1}$; and no $C_i$-path inside a leg and disjoint from the other cycles lies in a cell whose graph contains an edge of $C_i$;
--      - (dry) for every leg $P$: $C_1\cap P$ is empty or a single path; there is a unique $i$ (the apex) with $C_i\cap P$ a single path; $C_j\cap P=\emptyset$ for $j<i$; and $C_j\cap P$ consists of exactly two paths for $j>i$.
--
--   Thirsty villages are the input of the logarithmic size bound, Theorem 4.3.
--
--   **Formalization Note** Legs are path subgraphs of the cycle $S$ (orientation-free). Since legs and cycles lie inside $\Delta$, the induced rendition $\rho_\Delta$ uses the cells of $\rho$ inside $\Delta$, and every condition is stated through $\rho$. Tightness is with respect to $C_i$-paths of the crop by $\Delta$ (the village's rendition inside $\Delta$). Traces are relations: "a path whose trace lies in $Y$" means some trace of it does, and the drained condition holds for every choice of $\Delta_P$. Only the vertex set of $\Omega$ is used.
-- source:
--   Bentert–Cavallaro–Wiederrecht, A Dichotomy for Terminal Cyclability, arXiv:2611.06234 (held version, sha256 34a10f1a…4d4ea1), §3.2 "The wells are running dry", pp.24–25 (PDF 26–27); §3.4 "Water is getting scarce", p.27 (PDF 29)

import Mathlib
import Definitions.Def_TermCycDich_Supplement_Village

open scoped Classical

noncomputable section

namespace TermCycDich

namespace Supplement

open GMSTFramework.LocalStructure

/-!
# Wells (tight, drained, dry) and thirsty villages

Bentert–Cavallaro–Wiederrecht, *A Dichotomy for Terminal Cyclability*, arXiv:2611.06234 (held
version, sha256 34a10f1a…4d4ea1), §3.2 "The wells are running dry", pp.24–25 (PDF 26–27):
prewells, wells, tight concentric cycles, the interior `Δ_P` of a path, drained and dry wells;
§3.4 "Water is getting scarce", p.27 (PDF 29): thirsty villages:

"Let V = (G, R, S, A, ρ, Σ, ∆, C) be a (w, b)-village, where C = ⟨C₁, …, C_w⟩. We say that V is
thirsty if the following holds. All crops in this definition are taken through the rendition ρ of
G − A. Inside ∆, the rendition is refined into cells representing individual edges or isolated
vertices, so that the crop is explicitly embedded in ∆. The cycles of C are tight and their traces
lie in int(∆). Let B be the set of graph vertices represented on bd(∆), and let
P := {P ⊆ S | P is a nontrivial B-path contained in the crop by ∆ and V(P) ∩ V(C) ≠ ∅}.
Let W := ⋃P ∪ ⋃C, and let Ω be the cyclic order of V(W) ∩ B inherited from bd(∆). We require that
W = (W, Ω, ρ_∆, C, P) is a dry w-well, where ρ_∆ is the induced rendition."

**Formalization Note**
* Refined inside `Δ` (`RefinedIn`): for every cell `c ⊆ Δ`, `σ(c)` is a single edge with its two
  ends, or a single vertex.
* `B = π(N(ρ) ∩ bd(Δ))`, with `bd(Δ)` the manifold boundary of the disc. The legs `P` are path
  subgraphs (orientation-free) of the cycle `S`; a leg is a nontrivial `B`-path inside the crop by
  `Δ` meeting some `Cᵢ`. Since every leg lies inside `Δ` and ends in `B`, the well's rendition
  `ρ_Δ` draws exactly these paths and cycles in the cells of `ρ` inside `Δ`, so all well
  conditions are stated through `ρ` (traces, groundedness and cells are those of `ρ` inside `Δ`).
  Only the vertex set `V(Ω) = V(W) ∩ B` of the society is used (no condition depends on its cyclic
  order).
* Tightness ("the cycles of C are tight", in the village's rendition inside `Δ`): for every `i`
  there is no grounded `Cᵢ`-path of the crop by `Δ` with a trace in `Δᵢ ∖ Δᵢ₋₁` (`Δ₀ = ∅`).
* The interior `Δ_P` of a leg `P` with trace `γ` is the closure of the component of `Δ − γ` that is
  disjoint from the trace of `C₁`; conditions about `Δ_P` hold for every such choice.
* Traces are relations; "a path whose trace is contained in `Y`" is "some trace of it is
  contained in `Y`". The `C`-discs `Dᵢ` and traces `Tᵢ` are fixed once (`IsConcentricIn`).
* Indices are `0`-based: the paper's `C₁` is `C 0`.
-/

variable {V : Type} [Fintype V] [DecidableEq V] {G : SimpleGraph V}
variable {X : Type} [TopologicalSpace X]

namespace Rendition

variable {H : G.Subgraph} (ρ : Rendition X H)

/-- Inside `Δ` every cell represents a single edge (with its two ends) or a single vertex. -/
def RefinedIn (Δ : Set X) : Prop :=
  ∀ c ∈ ρ.cells, c ⊆ Δ →
    (∃ x y, G.Adj x y ∧ (ρ.σ c).verts = {x, y} ∧ (ρ.σ c).edgeSet = {s(x, y)}) ∨
      (∃ x, (ρ.σ c).verts = {x} ∧ (ρ.σ c).edgeSet = ∅)

/-- `B`: the vertices whose nodes lie on the boundary of `Δ`. -/
def bdVerts (Δ : Set X) : Set V := ρ.π '' (ρ.N ∩ manifoldBd Δ)

/-- The legs of the well: the path subgraphs of the closed walk `S` that are nontrivial `B`-paths
inside the crop by `Δ` and meet some cycle of `C`. -/
def legs {w : ℕ} {u : V} (S : G.Walk u u) (Δ : Set X) (C : Fin w → G.Subgraph) :
    Set G.Subgraph :=
  {Q | ∃ P : GPath G, P.sub = Q ∧ P.sub ≤ S.toSubgraph ∧ 0 < P.walk.length ∧
    IsAPath (ρ.bdVerts Δ) P ∧ P.sub ≤ ρ.crop Δ ∧ ∃ i, ∃ v ∈ P.verts, v ∈ (C i).verts}

/-- The well graph `W = ⋃ P ∪ ⋃ C`. -/
def wellGraph {w : ℕ} {u : V} (S : G.Walk u u) (Δ : Set X) (C : Fin w → G.Subgraph) :
    G.Subgraph :=
  (⨆ Q ∈ ρ.legs S Δ C, Q) ⊔ ⨆ i, C i

/-- The path subgraph `Q` has a trace contained in `Y`. -/
def TraceWithin (Q : G.Subgraph) (Y : Set X) : Prop :=
  ∃ P : GPath G, P.sub = Q ∧ ∃ γ, ρ.IsTracePath P γ ∧ γ ⊆ Y

/-- `DQ` is an interior `Δ_Q` of the path subgraph `Q` in the disc `Δ`: the closure of the component
of `Δ − γ` disjoint from `T₁` (the trace of `C₁`), for a trace `γ` of `Q`. -/
def IsLegInterior (Δ T₁ : Set X) (Q : G.Subgraph) (DQ : Set X) : Prop :=
  ∃ P : GPath G, P.sub = Q ∧ ∃ γ, ρ.IsTracePath P γ ∧ ∃ y ∈ Δ \ γ,
    Disjoint (connectedComponentIn (Δ \ γ) y) T₁ ∧ DQ = closure (connectedComponentIn (Δ \ γ) y)

/-- The `w`-well `(W, Ω, ρ_Δ, C, P)` of the village is a dry `w`-well (with the `C`-discs `D` and
traces `T`; `C₁ = C ⟨0, hw⟩`). -/
def IsDryWell {w : ℕ} (hw : 0 < w) {u : V} (S : G.Walk u u) (Δ : Set X)
    (C : Fin w → G.Subgraph) (D T : Fin w → Set X) : Prop :=
  let P := ρ.legs S Δ C
  let VΩ := (ρ.wellGraph S Δ C).verts ∩ ρ.bdVerts Δ
  -- prewell: the legs are pairwise internally vertex-disjoint nontrivial `V(Ω)`-paths
  (∀ Q ∈ P, ∃ P' : GPath G, P'.sub = Q ∧ 0 < P'.walk.length ∧ IsAPath VΩ P') ∧
  (∀ Q ∈ P, ∀ Q' ∈ P, Q ≠ Q' → ∀ P₁ P₂ : GPath G, P₁.sub = Q → P₂.sub = Q' →
    ∀ v ∈ P₁.verts, v ∈ P₂.verts → v ∉ P₁.inner ∧ v ∉ P₂.inner) ∧
  -- well: no leg contains a grounded `C₁`-path whose trace, except for its ends, lies in `int(D₁)`
  (¬ ∃ Q ∈ P, ∃ P' : GPath G, P'.sub ≤ Q ∧ IsHPath (C ⟨0, hw⟩) P' ∧ ∃ γ, ρ.IsTracePath P' γ ∧
      γ \ {x | x ∈ ρ.N ∧ (ρ.π x = P'.s ∨ ρ.π x = P'.t)} ⊆ interiorOf (D ⟨0, hw⟩)) ∧
  -- drained (first condition)
  (∀ Q ∈ P, ∀ i : Fin w, ∀ hi : i.val + 1 < w, (Q ⊓ C i).verts.Nonempty →
    ∀ DQ, ρ.IsLegInterior Δ (T ⟨0, hw⟩) Q DQ →
      ∃ Q' ∈ P, Q' ≠ Q ∧ ρ.TraceWithin Q' DQ ∧ (Q' ⊓ C ⟨i.val + 1, hi⟩).verts.Nonempty) ∧
  -- drained (second condition)
  (∀ i : Fin w, ¬ ∃ P' : GPath G, IsHPath (C i) P' ∧ (∃ Q ∈ P, P'.sub ≤ Q) ∧
      (∀ j, j ≠ i → Disjoint (P'.verts : Set V) (C j).verts) ∧
      ∃ c ∈ ρ.cells, P'.sub ≤ ρ.σ c ∧ ∃ e ∈ (ρ.σ c).edgeSet, e ∈ (C i).edgeSet) ∧
  -- dry
  (∀ Q ∈ P,
    ((Q ⊓ C ⟨0, hw⟩).verts = ∅ ∨ IsPathSub (Q ⊓ C ⟨0, hw⟩)) ∧
    ∃ i : Fin w, IsPathSub (Q ⊓ C i) ∧ (∀ j, IsPathSub (Q ⊓ C j) → j = i) ∧
      (∀ j, j < i → (Q ⊓ C j).verts = ∅) ∧ (∀ j, i < j → IsTwoPaths (Q ⊓ C j)))

/-- The cycles `C` (with `C`-discs `D`, bounded by the traces `T`) are tight in the crop by `Δ`:
for every `i` there is no grounded `Cᵢ`-path of the crop by `Δ` with a trace in `Dᵢ ∖ Dᵢ₋₁`
(`D₋₁ = ∅`). -/
def IsTight {w : ℕ} (Δ : Set X) (C : Fin w → G.Subgraph) (D : Fin w → Set X) : Prop :=
  ∀ i : Fin w, ¬ ∃ P : GPath G, P.sub ≤ ρ.crop Δ ∧ IsHPath (C i) P ∧
    ∃ γ, ρ.IsTracePath P γ ∧
      γ ⊆ D i \ (if h : 0 < i.val then D ⟨i.val - 1, by omega⟩ else ∅)

end Rendition

/-- `(G, R, S, A, ρ, Σ, Δ, C)` is a thirsty `(w, b)`-village (relative to `apex = apex2.4`,
`depth = depth2.4`). -/
def IsThirstyVillage (apex depth : ℕ → ℕ → ℕ → ℕ) (w b : ℕ) (G : SimpleGraph V) (R : Set V)
    {u : V} (S : G.Walk u u) (A : Finset V) (X : Type) [TopologicalSpace X]
    (ρ : Rendition X (minusVerts G (A : Set V))) (Δ : Set X) (C : Fin w → G.Subgraph) : Prop :=
  IsVillage apex depth w b G R S A X ρ Δ C ∧ ρ.RefinedIn Δ ∧
    ∃ hw : 0 < w, ∃ D T : Fin w → Set X, ρ.IsConcentricIn Δ C D T ∧
      (∀ i, T i ⊆ interiorOf Δ) ∧ ρ.IsTight Δ C D ∧ ρ.IsDryWell hw S Δ C D T

end Supplement

end TermCycDich


