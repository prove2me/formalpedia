-- Prove2me | Definitions.Def_GMSTFramework_LocalStructure_Societies
-- name    : GMSTFramework_LocalStructure_Societies
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-10T19:02:02.401638+00:00
-- url     : https://prove2.me/theorems/d62d9c75-070f-48ac-b50d-4127bdc133c6
-- title:
--   Societies, segments, society renditions, vortex societies, transactions, depth, nests, radial linkages, cozy nests, linear decompositions, surface configurations
-- statement:
--   A **society** $(G,\Omega)$ is a graph with a cyclic ordering $\Omega$ of $V(\Omega)\subseteq V(G)$; $S\subseteq V(\Omega)$ is a **segment** if it has at most two endpoints (vertices of $S$ with a cyclic neighbour outside $S$). A **rendition** of $(G,\Omega)$ in a surface with a single cuff $B$ is a $\Sigma$-rendition with $\pi(N\cap B)=V(\Omega)$, $\Omega$ being one of the two cyclic orders of these nodes along $B$; it is **cylindrical** if it is in the disk with a unique vortex. The **vortex society** of $c_0$ is $(\sigma(c_0),\Omega_{c_0})$ with $\Omega_{c_0}$ the order of $N(c_0)$ along $\mathrm{bd}(\bar c_0)$.
--
--   A **transaction** is an $X$-$Y$-linkage of $V(\Omega)$-paths for disjoint segments $X,Y$; it is **planar** (crosscap) if for some enumeration $x_1,\dots,x_n,y_n,\dots,y_1$ ($x_1,\dots,x_n,y_1,\dots,y_n$) occur in $\Omega$ in this cyclic order or its reverse; a **handle transaction** of order $2n$ splits into planar $\mathcal R,\mathcal Q$ of order $n$ with segments $S^{\mathcal R}_1,S^{\mathcal Q}_1,S^{\mathcal R}_2,S^{\mathcal Q}_2$ partitioning $\Omega$ in this order. The **depth** of a society is the maximum order of a transaction. A **nest** in a rendition is a family of disjoint grounded cycles $C_1,\dots,C_s$ with $C_i$-disks $\Delta_1\subseteq\cdots\subseteq\Delta_s$ and every vortex in $\Delta_1$; a **radial linkage** for it is a $V(\Omega)$-$V(C_1)$-linkage of grounded paths internally disjoint from $V(\Omega)$, **orthogonal** if every $C\cap R$ is a path (for a transaction: exactly two paths). A nest is **cozy** if every grounded $C_i$-path whose trace does not lie in the $C_i$-disk meets $V(\Omega)$ or another $C_j$. A **linear decomposition** is a labelling $v_1,\dots,v_n$ of $V(\Omega)$ in the order of $\Omega$ with bags $X_i\ni v_i$ covering $V(G)$ and every edge, each vertex in an interval of bags; its **adhesion** is $\max|X_i\cap X_{i+1}|$. A **surface configuration** $(G,\Omega,\mathcal C,\mathcal R,\mathcal P)$ of strength $(s,r,p_1,\dots,p_\ell)$: a cylindrical rendition with a nest $\mathcal C$ of order $s$ around its vortex, a radial linkage $\mathcal R$ of order $r$, transactions $\mathcal P_i$ of order $p_i$, pairwise disjoint and disjoint from $\mathcal R$, all orthogonal to $\mathcal C$, and disjoint segments $I_1,J_1,\dots,I_\ell,J_\ell,R$ in this cyclic order with $\mathcal P_i$ a $V(I_i)$-$V(J_i)$-linkage and every path of $\mathcal R$ ending in $R$.
--
--   **Formalization Note.** A cyclic ordering is a duplicate-free list read cyclically; "occur in the listed cyclic order" is `List.Sublist` of a rotation of $\Omega$ or of its reverse. `IsVortexSociety` admits both orientations (depth and adhesion are invariant under reversal), and depth/adhesion bounds of a rendition are required for every such ordering. A nest stores its $C_i$-disks; indices are 0-based (`C.C 0` is the inner cycle $C_1$). A linear decomposition's labelling is $\Omega$ read from a starting position.
-- source:
--   Gorsky, Protopapas, Wiederrecht, A unifying framework for Graph Minor Structure Theorems with polynomial bounds, STOC 2027 submission (manuscript sha256 b2ee466d…), p. 16–19 (PDF 19–22), §2.3.2–2.3.3; p. 60 (PDF 63) "cozy"; p. 84 (PDF 87) "Linear decompositions"; p. 86 (PDF 89) "surface configuration"

import Mathlib
import Definitions.Def_GMSTFramework_LocalStructure_Renditions

open scoped Classical

noncomputable section

namespace GMSTFramework.LocalStructure

/-!
# Societies, transactions, nests, radial linkages, cozy nests, depth, linear decompositions,
# surface configurations

Gorsky, Protopapas, Wiederrecht, *A unifying framework for Graph Minor Structure Theorems with
polynomial bounds*, STOC 2027 submission (manuscript sha256 b2ee466d…), §2.3.2 "Societies"
p. 16 (PDF 19), §2.3.3 p. 17–19 (PDF 20–22), §7.2.2 p. 60 (PDF 63), §8.1 p. 84 (PDF 87),
§8.2 p. 86 (PDF 89).

* A society `(H, Ω)`: a graph `H ≤ G` and a cyclic ordering `Ω` of `V(Ω) ⊆ V(H)`, given as a
  duplicate-free list read cyclically (every rotation is the same cyclic ordering).
* `IsSegment Ω S`: `S ⊆ V(Ω)` has at most two endpoints (vertices of `S` with a cyclic neighbour in
  `Ω` outside `S`).
* `IsSocietyRendition ρ Ω` (p. 16): `ρ` is a rendition of `(H, Ω)` in a surface `X` with a single
  cuff: the boundary of `X` is a simple closed curve, `π(N(ρ) ∩ bd X) = V(Ω)`, and the nodes of
  `V(Ω)` occur along the cuff in the cyclic order `Ω` (for a suitable parametrisation of the cuff,
  which covers both of the two cyclic orderings).
* `IsVortexSociety ρ c₀ Ω` (p. 19): `Ω` lists `π(N(c₀))` in the cyclic order along `bd(c̄₀)`
  (either orientation; every use is invariant under reversal: depth and the existence of a linear
  decomposition of given adhesion). The vortex society is `(σ(c₀), Ω)`.
* `Transaction H Ω n` (p. 17): `n` disjoint `V(Ω)`-paths of `H`, each an `X`-`Y`-path for disjoint
  segments `X, Y`; planar, crosscap and handle transactions (p. 17–18); orthogonality to a set of
  cycles (`C ∩ P` is exactly two paths).
* `DepthLE H Ω k`: every transaction has order at most `k` (the depth is the maximum order).
* `Nest ρ s` (p. 18): `s` disjoint grounded cycles with `C`-disks `Δ₁ ⊆ ⋯ ⊆ Δ_s`, every vortex
  inside `Δ₁` (indices `0`-based). Radial linkages for a family of cycles, orthogonality, cozy nests
  (p. 60).
* `LinearDecomposition H Ω` (p. 84): a labelling `v₁, …, vₙ` of `V(Ω)` in the order of `Ω`
  (a rotation of the list) with bags `X₁, …, Xₙ`; its adhesion.
* `SurfaceConfiguration` (p. 86): a cylindrical rendition, a nest, a radial linkage `R` and
  transactions `P₁, …, P_ℓ` with the stated disjointness, orthogonality and segment conditions.
-/

variable {V : Type} [Fintype V] [DecidableEq V] {G : SimpleGraph V}
variable {X : Type} [TopologicalSpace X]

/-! ### Cyclic orderings and segments -/

/-- The vertex `s ∈ S` at position `i` of `Ω` is an endpoint of `S`: its cyclic successor or
predecessor in `Ω` is not in `S`. -/
def IsEndpointAt (Ω : List V) (S : Finset V) (i : ℕ) : Prop :=
  ∃ x, (Ω)[i]? = some x ∧ x ∈ S ∧
    ∃ y, ((Ω)[(i + 1) % Ω.length]? = some y ∨ (Ω)[(i + Ω.length - 1) % Ω.length]? = some y) ∧ y ∉ S

/-- `S` is a segment of `Ω`: `S ⊆ V(Ω)` with at most two endpoints. -/
def IsSegment (Ω : List V) (S : Finset V) : Prop :=
  (∀ x ∈ S, x ∈ Ω) ∧ ((Finset.range Ω.length).filter fun i => IsEndpointAt Ω S i).card ≤ 2

/-- The vertices of the list `l` occur in the cyclic ordering `Ω`, or in its reverse, in the listed
order. -/
def CyclicallyOrdered (Ω l : List V) : Prop :=
  ∃ k, l.Sublist (Ω.rotate k) ∨ l.Sublist (Ω.reverse.rotate k)

/-- The embedding of the unit circle into the closed unit disk. -/
def circleToDisk (z : Circle) : TheDisk :=
  ⟨(z : ℂ), by rw [Metric.mem_closedBall, dist_zero_right, Circle.norm_coe]⟩

/-- `ρ` is a rendition of the society `(H, Ω)` in the surface `X` with a single cuff. -/
def IsSocietyRendition {H : G.Subgraph} (ρ : Rendition X H) (Ω : List V) : Prop :=
  Ω.Nodup ∧ (∀ v ∈ Ω, v ∈ H.verts) ∧ ρ.π '' (ρ.N ∩ surfaceBd X) = {v | v ∈ Ω} ∧
    ∃ e : C(Circle, X), Function.Injective e ∧ Set.range e = surfaceBd X ∧
      ∃ pts : List X, pts.map ρ.π = Ω ∧ (∀ x ∈ pts, x ∈ ρ.N) ∧ ArrangedAlong e pts

/-- `ρ` is a cylindrical rendition of `(H, Ω)`: a rendition in the disk with a unique vortex. -/
def IsCylindricalRendition {H : G.Subgraph} (ρ : Rendition TheDisk H) (Ω : List V) : Prop :=
  IsSocietyRendition ρ Ω ∧ ρ.vortices.ncard = 1

/-- `Ω` is the cyclic ordering of the vortex society of the vortex `c₀`: it lists `π(N(c₀))` in the
order of the nodes along the boundary of the disk `c̄₀`. -/
def IsVortexSociety {H : G.Subgraph} (ρ : Rendition X H) (c₀ : Set X) (Ω : List V) : Prop :=
  ρ.IsVortex c₀ ∧ Ω.Nodup ∧ {v | v ∈ Ω} = ρ.cellNodeVerts c₀ ∧
    ∃ e : C(TheDisk, X), Function.Injective e ∧ Set.range e = closure c₀ ∧
      ∃ pts : List X, pts.map ρ.π = Ω ∧ (∀ x ∈ pts, x ∈ ρ.N) ∧
        ArrangedAlong (fun z => e (circleToDisk z)) pts

/-! ### Transactions -/

/-- A transaction of order `n` in the society `(H, Ω)`: an `X`-`Y`-linkage of `V(Ω)`-paths of `H`
for disjoint segments `X`, `Y`. -/
structure Transaction (H : G.Subgraph) (Ω : List V) (n : ℕ) where
  /-- the paths -/
  L : Linkage G n
  /-- one end segment -/
  X : Finset V
  /-- the other end segment -/
  Y : Finset V
  segX : IsSegment Ω X
  segY : IsSegment Ω Y
  disjXY : Disjoint X Y
  inH : ∀ i, (L.path i).sub ≤ H
  ΩPath : ∀ i, IsAPath {v | v ∈ Ω} (L.path i)
  XYPath : ∀ i, IsABPath (X : Set V) (Y : Set V) (L.path i)

namespace Transaction

variable {H : G.Subgraph} {Ω : List V} {n : ℕ} (T : Transaction H Ω n)

/-- The end of the `i`-th path in `X`. -/
def endX (i : Fin n) : V := if (T.L.path i).s ∈ T.X then (T.L.path i).s else (T.L.path i).t

/-- The end of the `i`-th path in `Y`. -/
def endY (i : Fin n) : V := if (T.L.path i).s ∈ T.X then (T.L.path i).t else (T.L.path i).s

/-- The vertices of the transaction. -/
def verts : Finset V := T.L.verts

end Transaction

/-- A family of `k` paths with ends `(xᵢ, yᵢ)` is planar in `Ω`: for some enumeration,
`x₁, …, x_k, y_k, …, y₁` occur in `Ω` in this cyclic order or its reverse. -/
def PlanarEnds (Ω : List V) {k : ℕ} (ends : Fin k → V × V) : Prop :=
  ∃ σ : Equiv.Perm (Fin k),
    CyclicallyOrdered Ω (List.ofFn (fun i => (ends (σ i)).1) ++
      (List.ofFn (fun i => (ends (σ i)).2)).reverse)

/-- Crosscap ends: for some enumeration `x₁, …, x_k, y₁, …, y_k` occur in this cyclic order or its
reverse. -/
def CrosscapEnds (Ω : List V) {k : ℕ} (ends : Fin k → V × V) : Prop :=
  ∃ σ : Equiv.Perm (Fin k),
    CyclicallyOrdered Ω (List.ofFn (fun i => (ends (σ i)).1) ++
      List.ofFn (fun i => (ends (σ i)).2))

/-- A planar transaction. -/
def IsPlanarTransaction {H : G.Subgraph} {Ω : List V} {n : ℕ} (T : Transaction H Ω n) : Prop :=
  PlanarEnds Ω fun i => (T.endX i, T.endY i)

/-- A crosscap transaction. -/
def IsCrosscapTransaction {H : G.Subgraph} {Ω : List V} {n : ℕ} (T : Transaction H Ω n) : Prop :=
  CrosscapEnds Ω fun i => (T.endX i, T.endY i)

/-- A handle transaction (p. 18): order `2m` (`m ≥ 1`), partitioned into two planar transactions
`R`, `Q` of order `m`, with segments `S^R₁, S^Q₁, S^R₂, S^Q₂` partitioning `Ω` in this cyclic order,
`R` an `S^R₁`-`S^R₂`-linkage and `Q` an `S^Q₁`-`S^Q₂`-linkage. -/
def IsHandleTransaction {H : G.Subgraph} {Ω : List V} {n : ℕ} (T : Transaction H Ω n) : Prop :=
  ∃ m : ℕ, 1 ≤ m ∧ n = 2 * m ∧ ∃ (r q : Fin m → Fin n), Function.Injective r ∧
    Function.Injective q ∧ (∀ i j, r i ≠ q j) ∧
    ∃ (k : ℕ) (l₁ l₂ l₃ l₄ : List V),
      (Ω.rotate k = l₁ ++ l₂ ++ l₃ ++ l₄ ∨ Ω.reverse.rotate k = l₁ ++ l₂ ++ l₃ ++ l₄) ∧
      (∀ i, IsABPath {v | v ∈ l₁} {v | v ∈ l₃} (T.L.path (r i))) ∧
      (∀ i, IsABPath {v | v ∈ l₂} {v | v ∈ l₄} (T.L.path (q i))) ∧
      PlanarEnds Ω (fun i => (T.endX (r i), T.endY (r i))) ∧
      PlanarEnds Ω (fun i => (T.endX (q i), T.endY (q i)))

/-- The society `(H, Ω)` has depth at most `k`: every transaction has order at most `k`. -/
def DepthLE (H : G.Subgraph) (Ω : List V) (k : ℕ) : Prop :=
  ∀ n, Transaction H Ω n → n ≤ k

/-! ### Nests and radial linkages -/

/-- A nest of order `s` in the rendition `ρ` (of a society): disjoint grounded cycles
`C₀, …, C_{s-1}` with `Cᵢ`-disks `Δ₀ ⊆ ⋯ ⊆ Δ_{s-1}` and every vortex inside `Δ₀`. -/
structure Nest {H : G.Subgraph} (ρ : Rendition X H) (s : ℕ) where
  /-- the cycles, innermost first -/
  C : Fin s → G.Subgraph
  /-- their disks -/
  disk : Fin s → Set X
  cycle : ∀ i, IsCycleSub (C i) ∧ C i ≤ H
  disj : Pairwise fun i j => Disjoint (C i).verts (C j).verts
  isCDisk : ∀ i, ρ.IsCDisk (C i) (disk i)
  vortex_in : ∀ i, ∀ c ∈ ρ.vortices, c ⊆ disk i
  mono : ∀ i j, i ≤ j → disk i ⊆ disk j

/-- The union `⋃ C` of a family of cycles. -/
def cyclesSub {s : ℕ} (C : Fin s → G.Subgraph) : G.Subgraph := ⨆ i, C i

/-- `R` is a radial linkage for the family of disjoint cycles `C` (with innermost cycle `C₀`, so
`s ≥ 1`) in the rendition `ρ` of `(H, Ω)`: a `V(Ω)`-`V(C₀)`-linkage of `H` whose paths are grounded
and internally disjoint from `V(Ω)`. -/
def IsRadialLinkage {H : G.Subgraph} (ρ : Rendition X H) (Ω : List V) {s r : ℕ} (hs : 0 < s)
    (C : Fin s → G.Subgraph) (R : Linkage G r) : Prop :=
  ∀ j, (R.path j).sub ≤ H ∧ IsABPath {v | v ∈ Ω} (C ⟨0, hs⟩).verts (R.path j) ∧
    ρ.GroundedPath (R.path j) ∧ (R.path j).InternallyDisjoint {v | v ∈ Ω}

/-- A linkage is orthogonal to the family of cycles `C` (radial-linkage sense): every `C ∩ R` is a
path. -/
def RadialOrthogonal {s r : ℕ} (C : Fin s → G.Subgraph) (R : Linkage G r) : Prop :=
  ∀ i j, IsPathSub (C i ⊓ (R.path j).sub)

/-- A transaction is orthogonal to the family of cycles `C`: every `C ∩ P` consists of exactly two
paths. -/
def TransactionOrthogonal {H : G.Subgraph} {Ω : List V} {s n : ℕ} (C : Fin s → G.Subgraph)
    (T : Transaction H Ω n) : Prop :=
  ∀ i j, IsTwoPaths (C i ⊓ (T.L.path j).sub)

/-- A nest is cozy (p. 60): for every `i` and every grounded `Cᵢ`-path `P` with a trace not inside
the `Cᵢ`-disk, `P` meets `V(Ω)` or another cycle of the nest. -/
def IsCozy {H : G.Subgraph} {ρ : Rendition X H} (Ω : List V) {s : ℕ} (C : Nest ρ s) : Prop :=
  ∀ i, ∀ P : GPath G, P.sub ≤ H → IsAPath (C.C i).verts P → ρ.GroundedPath P →
    (∃ T, ρ.IsTracePath P T ∧ ¬ T ⊆ C.disk i) →
      (∃ v ∈ P.verts, v ∈ Ω) ∨ ∃ j, j ≠ i ∧ ∃ v ∈ P.verts, v ∈ (C.C j).verts

/-! ### Linear decompositions -/

/-- A linear decomposition of the society `(H, Ω)`: the labelling `v₁, …, vₙ` is `Ω` read from
position `rot` (so the `vᵢ` appear in `Ω` in the listed order), with bags `X₁, …, Xₙ`. -/
structure LinearDecomposition (H : G.Subgraph) (Ω : List V) where
  /-- starting position of the labelling -/
  rot : ℕ
  /-- the bags -/
  bag : Fin Ω.length → Finset V
  bag_sub : ∀ i, (bag i : Set V) ⊆ H.verts
  mem : ∀ i, (Ω.rotate rot).get ⟨i, by simp⟩ ∈ bag i
  cover_verts : ∀ v ∈ H.verts, ∃ i, v ∈ bag i
  cover_edges : ∀ u v, H.Adj u v → ∃ i, u ∈ bag i ∧ v ∈ bag i
  interval : ∀ x (i j k : Fin Ω.length), i ≤ j → j ≤ k → x ∈ bag i → x ∈ bag k → x ∈ bag j

/-- The linear decomposition has adhesion at most `k`: `|Xᵢ ∩ X_{i+1}| ≤ k` for all `i`. -/
def LinearDecomposition.AdhesionLE {H : G.Subgraph} {Ω : List V} (D : LinearDecomposition H Ω)
    (k : ℕ) : Prop :=
  ∀ (i j : Fin Ω.length), j.val = i.val + 1 → (D.bag i ∩ D.bag j).card ≤ k

/-- Every vortex society of `ρ` has depth at most `d` (`ρ` has depth at most `d`). -/
def RenditionDepthLE {H : G.Subgraph} (ρ : Rendition X H) (d : ℕ) : Prop :=
  ∀ c ∈ ρ.vortices, ∀ Ω, IsVortexSociety ρ c Ω → DepthLE (ρ.σ c) Ω d

/-- Every vortex society of `ρ` has a linear decomposition of adhesion at most `d`. -/
def VorticesAdhesionLE {H : G.Subgraph} (ρ : Rendition X H) (d : ℕ) : Prop :=
  ∀ c ∈ ρ.vortices, ∀ Ω, IsVortexSociety ρ c Ω →
    ∃ D : LinearDecomposition (ρ.σ c) Ω, D.AdhesionLE d

/-! ### Surface configurations -/

/-- A surface configuration `(G, Ω, C, R, P = {P₁, …, P_ℓ})` of strength `(s, r, p₁, …, p_ℓ)`
(p. 86): `ρ` a cylindrical rendition of `(G, Ω)` (here `H = ⊤`), `C` a nest of order `s ≥ 1`
around its vortex, `R` a radial linkage of order `r`, transactions `Pᵢ` of order `pᵢ`, pairwise
disjoint and disjoint from `R`, all orthogonal to `C`, and pairwise disjoint segments
`I₁, J₁, …, I_ℓ, J_ℓ, R` of `Ω` in this cyclic order with `Pᵢ` a `V(Iᵢ)`-`V(Jᵢ)`-linkage and every
path of `R` with an end in the segment `R`. -/
structure SurfaceConfiguration (G : SimpleGraph V) (Ω : List V) (s r ℓ : ℕ) (p : Fin ℓ → ℕ) where
  /-- the cylindrical rendition -/
  ρ : Rendition TheDisk (⊤ : G.Subgraph)
  cyl : IsCylindricalRendition ρ Ω
  hs : 0 < s
  /-- the nest -/
  nest : Nest ρ s
  /-- the radial linkage -/
  R : Linkage G r
  radial : IsRadialLinkage ρ Ω hs nest.C R
  /-- the transactions -/
  P : (i : Fin ℓ) → Transaction (⊤ : G.Subgraph) Ω (p i)
  disjP : Pairwise fun i j => Disjoint (P i).verts (P j).verts
  disjR : ∀ i, Disjoint R.verts (P i).verts
  orthP : ∀ i, TransactionOrthogonal nest.C (P i)
  orthR : RadialOrthogonal nest.C R
  segments : ∃ (I J g₁ g₂ : Fin ℓ → List V) (Rs g₃ : List V) (k : ℕ),
    (Ω.rotate k = (List.ofFn fun i => I i ++ g₁ i ++ J i ++ g₂ i).flatten ++ Rs ++ g₃ ∨
      Ω.reverse.rotate k = (List.ofFn fun i => I i ++ g₁ i ++ J i ++ g₂ i).flatten ++ Rs ++ g₃) ∧
    (∀ i j, IsABPath {v | v ∈ I i} {v | v ∈ J i} ((P i).L.path j)) ∧
    ∀ j, (R.path j).s ∈ Rs ∨ (R.path j).t ∈ Rs

/-- The configuration has `h` handle-transactions and `c` crosscap-transactions. -/
def SurfaceConfiguration.HasTypes {G : SimpleGraph V} {Ω : List V} {s r ℓ : ℕ} {p : Fin ℓ → ℕ}
    (S : SurfaceConfiguration G Ω s r ℓ p) (h c : ℕ) : Prop :=
  ∃ isHandle : Fin ℓ → Bool,
    (∀ i, if isHandle i then IsHandleTransaction (S.P i) else IsCrosscapTransaction (S.P i)) ∧
    (Finset.univ.filter fun i => isHandle i = true).card = h ∧
    (Finset.univ.filter fun i => isHandle i = false).card = c

end GMSTFramework.LocalStructure


