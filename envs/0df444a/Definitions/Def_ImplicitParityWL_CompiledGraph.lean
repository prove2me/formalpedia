-- Prove2me | Definitions.Def_ImplicitParityWL_CompiledGraph
-- name    : ImplicitParityWL_CompiledGraph
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T02:15:00.935711+00:00
-- url     : https://prove2.me/theorems/ed1acccf-3dc4-491f-a67f-a11ccabf193b
-- title:
--   The graph compiler: the colored graphs $G_0$, $G_1$ of an implicit parity system
-- statement:
--   From an implicit parity system with coordinate set $[k]\times\mathbb F_2^\ell$ the compiler builds colored graphs $G_\varepsilon$, $\varepsilon\in\mathbb F_2$:
--
--   1. for $v\in W$ and $c\in\mathfrak c_v$, a coordinate color class: the pair $\{\mathrm{crd}_{v,c}[0],\mathrm{crd}_{v,c}[1]\}$ if $\iota(v)=\star$; otherwise the singleton $\{\mathrm{crd}_{v,c}[0]\}$ in $G_0$, and in $G_1$ the singleton $\{\mathrm{crd}_{v,c}[\iota(v)]\}$ in the first block and $\{\mathrm{crd}_{v,c}[0]\}$ elsewhere;
--   2. for a ternary schema and $c\in\mathfrak c_e$, a sum pair $\{\mathrm{sum}_{e,c}[t]\}$ and a junction class $\{\mathrm{junc}_{e,c}[s,t,s+t]\}$, where $\mathrm{junc}_{e,c}[s,t,s+t]$ is adjacent to $\mathrm{crd}_{u,\sigma(c)}[s]$, $\mathrm{crd}_{v,\tau(c)}[t]$ and $\mathrm{sum}_{e,c}[s+t]$;
--   3. for each schema a strip with internal track pairs $\{\mathrm{trk}_{e,h,c}[s]\}$, $1\le h\le k+1$, $c\in\mathfrak c_e$. At the index $0$ the track is $\mathrm{crd}_{u,\sigma(c)}$ for a binary schema and $\mathrm{sum}_{e,c}$ for a ternary one; at the index $k+2$ it is $\mathrm{crd}_{v,\tau(c)}$ for a binary schema and $\mathrm{crd}_{w,\pi(c)}$ for a ternary one;
--   4. for each stage $1\le h\le k+2$, a mask vertex $\mathrm{msk}_{e,h}[x]$ for every $x\in\mathrm{rowspan}(B_e)$, and for each $c\in\mathfrak c_e$ an update class $\{\mathrm{upd}_{e,h,c}[s,t]\}$, where $\mathrm{upd}_{e,h,c}[s,t]$ is adjacent to $\mathrm{trk}_{e,h-1,c}[s]$, $\mathrm{trk}_{e,h,c}[t]$ and exactly the $\mathrm{msk}_{e,h}[x]$ with $s+t=x_c$.
--
--   There are no other edges, and a name with its subscripts is a color. Only the choice of retained coordinate vertices depends on $\varepsilon$.
--
--   The module also defines the pebble-matching predicate of Lemmas 5.5 and 5.6: $k$ pebble pairs match $L_c[0]\leftrightarrow L_c[b_c]$ for every $c\in\mathrm{supp}(a)$.
--
--   **Formalization Note** All vertex names form an inductive type, of which $G_\varepsilon$ is the induced subgraph on the retained names; a coordinate vertex that is not retained has no edges. The bit retained at an initialized location is $\varepsilon\iota(v)$ in the first block and $0$ elsewhere. The junction name stores $s,t$ only. In a pebble match, which pebble index carries which coordinate does not matter and the spare index is unconstrained.
-- source:
--   Curticapean, Liu, Neuen, Seppelt, Lower Bounds for the Weisfeiler–Leman Algorithm via Implicit Parity Systems (STOC 2027 submission, manuscript of November 3, 2026, sha256 6604ccc9…), §5.1, pp.24–25

import Mathlib
import Definitions.Def_ImplicitParityWL_ImplicitSystem
import Definitions.Def_ImplicitParityWL_CheckMatrix
import Definitions.Def_ImplicitParityWL_PebbleGame

namespace ImplicitParityWL

/-- The vertex names of the graph compiler (Curticapean, Liu, Neuen, Seppelt, *Lower Bounds for the
Weisfeiler–Leman Algorithm via Implicit Parity Systems*, manuscript of November 3, 2026, §5.1,
pp.24–25): a name with its subscripts and its bracketed bit, tuple or mask.

**Formalization Note** `junc e c s t` is the page's `junc_{e,c}[s, t, s + t]`. All names exist as terms;
`ImplicitSystem.IsVertex` selects those that are vertices of `G_ε`. -/
inductive Vtx (k ℓ : ℕ) (W E : Type*) where
  | crd (v : W) (c : Coord k ℓ) (s : ZMod 2)
  | sum (e : E) (c : Coord k ℓ) (t : ZMod 2)
  | junc (e : E) (c : Coord k ℓ) (s t : ZMod 2)
  | trk (e : E) (h : ℕ) (c : Coord k ℓ) (s : ZMod 2)
  | upd (e : E) (h : ℕ) (c : Coord k ℓ) (s t : ZMod 2)
  | msk (e : E) (h : ℕ) (x : Word k ℓ)

/-- The color classes of the compiler (§5.1, p.24): a name with its subscripts, without the bracket. -/
inductive CColor (k ℓ : ℕ) (W E : Type*) where
  | crd (v : W) (c : Coord k ℓ)
  | sum (e : E) (c : Coord k ℓ)
  | junc (e : E) (c : Coord k ℓ)
  | trk (e : E) (h : ℕ) (c : Coord k ℓ)
  | upd (e : E) (h : ℕ) (c : Coord k ℓ)
  | msk (e : E) (h : ℕ)

/-- The color of a vertex name. -/
def Vtx.color {k ℓ : ℕ} {W E : Type*} : Vtx k ℓ W E → CColor k ℓ W E
  | .crd v c _ => .crd v c
  | .sum e c _ => .sum e c
  | .junc e c _ _ => .junc e c
  | .trk e h c _ => .trk e h c
  | .upd e h c _ _ => .upd e h c
  | .msk e h _ => .msk e h

namespace ImplicitSystem

variable {k ℓ : ℕ} {W E : Type*} (I : ImplicitSystem k ℓ W E)

/-- The track vertex `trk_{e,h,c}[s]` for `0 ≤ h ≤ k + 2` (§5.1, item 3, p.25): at the index `0` it is
`crd_{u,σ(c)}[s]` for a binary schema and `sum_{e,c}[s]` for a ternary one; at the index `k + 2` it is
`crd_{v,τ(c)}[s]` for a binary schema and `crd_{w,π(c)}[s]` for a ternary one. -/
def track (e : E) (h : ℕ) (c : Coord k ℓ) (s : ZMod 2) : Vtx k ℓ W E :=
  if h = 0 then
    match (I.schema e).third with
    | none => .crd (I.schema e).u ((I.schema e).σ c) s
    | some _ => .sum e c s
  else if h = k + 2 then
    match (I.schema e).third with
    | none => .crd (I.schema e).v ((I.schema e).τ c) s
    | some (w, π) => .crd w (π c) s
  else .trk e h c s

/-- The edge relation of the compiler (§5.1, items 2 and 4, pp.24–25), read from the junction and update
side. A junction vertex `junc_{e,c}[s, t, s + t]` is adjacent to `crd_{u,σ(c)}[s]`, `crd_{v,τ(c)}[t]` and
`sum_{e,c}[s + t]`. An update vertex `upd_{e,h,c}[s, t]` is adjacent to its track vertices
`trk_{e,h-1,c}[s]` and `trk_{e,h,c}[t]`, and to exactly the mask vertices `msk_{e,h}[x]` with `s + t = x_c`.
There are no other edges. -/
inductive Edge : Vtx k ℓ W E → Vtx k ℓ W E → Prop
  | junc_u (e : E) (c : Coord k ℓ) (s t : ZMod 2) :
      Edge (.junc e c s t) (.crd (I.schema e).u ((I.schema e).σ c) s)
  | junc_v (e : E) (c : Coord k ℓ) (s t : ZMod 2) :
      Edge (.junc e c s t) (.crd (I.schema e).v ((I.schema e).τ c) t)
  | junc_sum (e : E) (c : Coord k ℓ) (s t : ZMod 2) :
      Edge (.junc e c s t) (.sum e c (s + t))
  | upd_prev (e : E) (h : ℕ) (c : Coord k ℓ) (s t : ZMod 2) :
      Edge (.upd e h c s t) (I.track e (h - 1) c s)
  | upd_next (e : E) (h : ℕ) (c : Coord k ℓ) (s t : ZMod 2) :
      Edge (.upd e h c s t) (I.track e h c t)
  | upd_msk (e : E) (h : ℕ) (c : Coord k ℓ) (s t : ZMod 2) (x : Word k ℓ) (hx : s + t = x c) :
      Edge (.upd e h c s t) (.msk e h x)

/-- The vertex names retained in `G_ε` (§5.1, pp.24–25).

1. `crd_{v,c}[s]` for `c ∈ 𝔠_v`. If `v` is uninitialized both bits are kept. If `ι(v) ∈ {0, 1}` one vertex is
   kept: bit `0` in `G₀`; in `G₁` bit `ι(v)` in the first block and bit `0` elsewhere.
2. `sum_{e,c}[t]` and `junc_{e,c}[s, t, s + t]` for a ternary schema and `c ∈ 𝔠_e`.
3. `trk_{e,h,c}[s]` for `1 ≤ h ≤ k + 1` and `c ∈ 𝔠_e`.
4. `upd_{e,h,c}[s, t]` for `1 ≤ h ≤ k + 2` and `c ∈ 𝔠_e`, and `msk_{e,h}[x]` for `1 ≤ h ≤ k + 2` and
   `x ∈ rowspan(B_e)`.

**Formalization Note** The first block is the index `0`, and `ε * b` is `0` in `G₀` and `b` in `G₁`. -/
def IsVertex (ε : ZMod 2) : Vtx k ℓ W E → Prop
  | .crd v c s => c ∈ I.dom v ∧ ∀ b, I.init v = some b → s = if c.1.val = 0 then ε * b else 0
  | .sum e c _ => (I.schema e).third.isSome ∧ c ∈ (I.schema e).dom
  | .junc e c _ _ => (I.schema e).third.isSome ∧ c ∈ (I.schema e).dom
  | .trk e h c _ => 1 ≤ h ∧ h ≤ k + 1 ∧ c ∈ (I.schema e).dom
  | .upd e h c _ _ => 1 ≤ h ∧ h ≤ k + 2 ∧ c ∈ (I.schema e).dom
  | .msk e h x => 1 ≤ h ∧ h ≤ k + 2 ∧ x ∈ maskSpace (I.schema e).dom

/-- The vertex set of `G_ε`. -/
abbrev Vertex (ε : ZMod 2) := {p : Vtx k ℓ W E // I.IsVertex ε p}

instance vertex_finite [Finite W] [Finite E] (ε : ZMod 2) : Finite (I.Vertex ε) := by
  have hfin : ({p | I.IsVertex ε p} : Set (Vtx k ℓ W E)).Finite := by
    refine Set.Finite.subset (s :=
      Set.range (fun x : W × Coord k ℓ × ZMod 2 => Vtx.crd x.1 x.2.1 x.2.2) ∪
      Set.range (fun x : E × Coord k ℓ × ZMod 2 => Vtx.sum x.1 x.2.1 x.2.2) ∪
      Set.range (fun x : E × Coord k ℓ × ZMod 2 × ZMod 2 => Vtx.junc x.1 x.2.1 x.2.2.1 x.2.2.2) ∪
      Set.range (fun x : E × Fin (k + 3) × Coord k ℓ × ZMod 2 =>
        Vtx.trk x.1 x.2.1.val x.2.2.1 x.2.2.2) ∪
      Set.range (fun x : E × Fin (k + 3) × Coord k ℓ × ZMod 2 × ZMod 2 =>
        Vtx.upd x.1 x.2.1.val x.2.2.1 x.2.2.2.1 x.2.2.2.2) ∪
      Set.range (fun x : E × Fin (k + 3) × Word k ℓ => Vtx.msk x.1 x.2.1.val x.2.2)) ?_ ?_
    · exact (((((Set.finite_range _).union (Set.finite_range _)).union (Set.finite_range _)).union
        (Set.finite_range _)).union (Set.finite_range _)).union (Set.finite_range _)
    · intro p hp
      cases p with
      | crd v c s => exact Or.inl <| Or.inl <| Or.inl <| Or.inl <| Or.inl ⟨(v, c, s), rfl⟩
      | sum e c t => exact Or.inl <| Or.inl <| Or.inl <| Or.inl <| Or.inr ⟨(e, c, t), rfl⟩
      | junc e c s t => exact Or.inl <| Or.inl <| Or.inl <| Or.inr ⟨(e, c, s, t), rfl⟩
      | trk e h c s =>
        have hp' : 1 ≤ h ∧ h ≤ k + 1 ∧ c ∈ (I.schema e).dom := hp
        exact Or.inl <| Or.inl <| Or.inr ⟨(e, ⟨h, by omega⟩, c, s), rfl⟩
      | upd e h c s t =>
        have hp' : 1 ≤ h ∧ h ≤ k + 2 ∧ c ∈ (I.schema e).dom := hp
        exact Or.inl <| Or.inr ⟨(e, ⟨h, by omega⟩, c, s, t), rfl⟩
      | msk e h x =>
        have hp' : 1 ≤ h ∧ h ≤ k + 2 ∧ x ∈ maskSpace (I.schema e).dom := hp
        exact Or.inr ⟨(e, ⟨h, by omega⟩, x), rfl⟩
  exact hfin.to_subtype

noncomputable instance vertex_fintype [Finite W] [Finite E] (ε : ZMod 2) :
    Fintype (I.Vertex ε) := Fintype.ofFinite _

/-- The colored graph `G_ε` compiled from the implicit parity system `I` (§5.1, pp.24–25): the retained
vertices, with the edges of `Edge` (made undirected) between them, and each vertex colored by its name
without the bracket. -/
def graph (ε : ZMod 2) : ColoredGraph (CColor k ℓ W E) (I.Vertex ε) where
  graph := (SimpleGraph.fromRel I.Edge).comap Subtype.val
  χ := fun p => p.val.color

/-- The family of track vertices at the index `h` of the schema `e`. -/
def trackFamily (e : E) (h : ℕ) : Coord k ℓ → ZMod 2 → Vtx k ℓ W E := fun c s => I.track e h c s

/-- `k` pebble indices of the state `S` of the `(k + 1)`-pebble game on `(G₀, G₁)` match
`L c 0 ↔ L c (b c)` for every `c ∈ supp(a)` (Lemmas 5.5 and 5.6, pp.27–28); `L` is a family of vertex names
indexed by a coordinate and a bracketed bit, such as `trk_{e,h,c}[·]` or `crd_{w,π(c)}[·]`.

**Formalization Note** Which pebble index carries which coordinate does not matter, and the remaining
pebble index is unconstrained: it is the page's "one additional pebble pair". -/
def PebbleMatch (S : GameState (I.Vertex 0) (I.Vertex 1) (k + 1))
    (L : Coord k ℓ → ZMod 2 → Vtx k ℓ W E) (a : Address k ℓ) (b : Coord k ℓ → ZMod 2) : Prop :=
  ∃ g : Coord k ℓ → Fin (k + 1), Set.InjOn g a.supp ∧ ∀ c ∈ a.supp,
    ∃ (x : I.Vertex 0) (y : I.Vertex 1),
      S (g c) = some (x, y) ∧ x.val = L c 0 ∧ y.val = L c (b c)

end ImplicitSystem

/-- The family of coordinate vertices `crd_{v,π(c)}[·]`, used in Lemma 5.6, p.28. -/
def crdFamily {k ℓ : ℕ} {W E : Type*} (v : W) (π : BlockPerm k ℓ) :
    Coord k ℓ → ZMod 2 → Vtx k ℓ W E := fun c s => .crd v (π c) s

end ImplicitParityWL


