-- Prove2me | Definitions.Def_ImplicitParityWL_Supplement_MatrixGraph
-- name    : ImplicitParityWL_Supplement_MatrixGraph
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T04:27:31.564663+00:00
-- url     : https://prove2.me/theorems/4ea1a090-cadc-41f7-a1a1-ce034bf4bfec
-- title:
--   The matrix pair $\tilde G_0,\tilde G_1$ of an implicit parity system
-- statement:
--   Fix an implicit parity system $\mathcal I=(W,\mathfrak c,(\mathfrak c_v)_{v\in W},\mathcal E,\iota)$ with coordinate set $\mathfrak c=[k]\times\mathbb F_2^\ell$, and put $R=6(k+1)+1$. For a schema $e$, let $B_e$ be the matrix whose rows are the $k-1$ block-parity checks comparing blocks $1,\dots,k-1$ with block $k$, followed by the $\ell$ checksum checks, restricted to the columns of $\mathfrak c_e$, with zero rows deleted and no row reduction. Write its rows as $\beta_{e,1},\dots,\beta_{e,m_e}$ and put
--   $$\Lambda=1+\max\bigl(\{0\}\cup\{m_e:e\in\mathcal E\}\bigr).$$
--
--   The graphs $\tilde G_0,\tilde G_1$ keep the coordinate color classes $\mathrm{crd}_{v,c}$ (with their initialization by singletons) and the sum and junction classes $\mathrm{sum}_{e,c}$, $\mathrm{junc}_{e,c}$ of the compiler of §5.1. For each schema $e$ with nonempty domain, the strip is replaced as follows.
--
--   1. There are $R$ repetitions, each processing the rows $1,\dots,m_e$ in order. At $c\in\mathfrak c_e$ there are track symbols $\mathrm{trk}_{e,h,j,c}[s]$, $1\le h\le R$, $0\le j\le m_e$, $s\in\mathbb F_2$, with $\mathrm{trk}_{e,h,0,c}=\mathrm{trk}_{e,h-1,m_e,c}$ for $h>1$. The first symbol $\mathrm{trk}_{e,1,0,c}[s]$ is $\mathrm{crd}_{u,\sigma(c)}[s]$ for a binary schema and $\mathrm{sum}_{e,c}[s]$ for a ternary one; the last symbol $\mathrm{trk}_{e,R,m_e,c}[s]$ is $\mathrm{crd}_{v,\tau(c)}[s]$, respectively $\mathrm{crd}_{w,\pi(c)}[s]$. If $\beta_{e,j}(c)=0$, the symbols $\mathrm{trk}_{e,h,j-1,c}[s]$ and $\mathrm{trk}_{e,h,j,c}[s]$ are identified. Every remaining internal track class is a pair with its own color; a class identified with an endpoint is that endpoint.
--   2. For $1\le h\le R$ and $1\le j\le m_e$ there is a coefficient pair $\mathrm{coef}_{e,h,j}[b]$, $b\in\mathbb F_2$. For every nonzero entry $\beta_{e,j}(c)=1$ there is a four-vertex update class $\mathrm{upd}_{e,h,j,c}[s,t,b]$, $s+t+b=0$, whose vertex is adjacent to $\mathrm{trk}_{e,h,j-1,c}[s]$, $\mathrm{trk}_{e,h,j,c}[t]$ and $\mathrm{coef}_{e,h,j}[b]$ whenever these are present. Coefficient and update classes have fresh colors, and there are no further edges.
--
--   This is the second implementation of the graph compiler (Theorem 7.3); its color classes have at most four vertices and its size is governed by the number of nonzero entries of the $B_e$.
--
--   **Formalization Note** The pair $(h,j)$ is the position $g=(h-1)m_e+j\in\{0,\dots,Rm_e\}$, so $(h,0)$ and $(h-1,m_e)$ are the same position. The identifications are resolved by representing each track class by the last position $g'\le g$ with a nonzero entry in the column $c$: position $0$ is the initial endpoint, and the last nonzero position of the column (whose class contains $(R,m_e)$) is the final endpoint. The update vertex with labels $s,t$ has $b=s+t$. The first block is the index $0$, as in the published compiler.
-- source:
--   Curticapean, Liu, Neuen, Seppelt, Lower Bounds for the Weisfeiler–Leman Algorithm via Implicit Parity Systems (STOC 2027 submission, manuscript of November 3, 2026, sha256 6604ccc9…), §7.1, pp.36–37 (with §5.1, items 1–2, pp.24–25)

import Mathlib
import Definitions.Def_ImplicitParityWL_CompiledGraph

namespace ImplicitParityWL

namespace Supplement

/-- The rows of the check matrix `B` of Fact 4.5 in the order fixed in §7.1 (Curticapean, Liu,
Neuen, Seppelt, *Lower Bounds for the Weisfeiler–Leman Algorithm via Implicit Parity Systems*,
manuscript of November 3, 2026, §7.1, p.36): the `k - 1` block-parity checks comparing blocks
`1, …, k - 1` with block `k`, followed by the `ℓ` checksum checks. -/
def checkRows (k ℓ : ℕ) : List (Fin (k - 1) ⊕ Fin ℓ) :=
  (List.finRange (k - 1)).map Sum.inl ++ (List.finRange ℓ).map Sum.inr

open scoped Classical in
/-- The rows `β_{e,1}, …, β_{e,m_e}` of `B_e` (§7.1, p.36): the rows of `B`, in the order of
`checkRows`, whose restriction to the columns of the coordinate domain `𝔠_e` is nonzero. Zero rows are
deleted and there is **no** row reduction. -/
noncomputable def retainedRows {k ℓ : ℕ} (dom : Finset (Coord k ℓ)) : List (Fin (k - 1) ⊕ Fin ℓ) :=
  (checkRows k ℓ).filter fun r => ∃ c ∈ dom, checkMatrix k ℓ r c ≠ 0

/-- `m_e`, the number of rows of `B_e` (§7.1, p.36). -/
noncomputable def numRows {k ℓ : ℕ} (dom : Finset (Coord k ℓ)) : ℕ := (retainedRows dom).length

/-- `m_e ≤ k - 1 + ℓ` (§7.1, p.36). -/
theorem numRows_le {k ℓ : ℕ} (dom : Finset (Coord k ℓ)) : numRows dom ≤ k - 1 + ℓ := by
  unfold numRows retainedRows
  refine (List.length_filter_le _ _).trans ?_
  simp [checkRows]

/-- The number `R = 6(k + 1) + 1` of repetitions of each strip (§7.1, p.36). -/
def reps (k : ℕ) : ℕ := 6 * (k + 1) + 1

/-- The row processed at the global position `g` of a strip. The positions `1, …, R·m_e` enumerate the
pairs `(h, j)` with `1 ≤ h ≤ R` and `1 ≤ j ≤ m_e` in the order of processing, `g = (h - 1)·m_e + j`; the
position `0` is the start `(1, 0)`, and `(h, 0) = (h - 1, m_e)` is the position `(h - 1)·m_e`. The row at
the position `g ≥ 1` is `β_{e,j}` with `j - 1 = (g - 1) mod m_e`. -/
noncomputable def rowAt {k ℓ : ℕ} (dom : Finset (Coord k ℓ)) (g : ℕ) : Option (Fin (k - 1) ⊕ Fin ℓ) :=
  (retainedRows dom)[(g - 1) % numRows dom]?

/-- The entry `β_{e,j}(c)` at the position `g` is nonzero: `1 ≤ g ≤ R·m_e` and the row processed at `g`
has a `1` in the column `c`. -/
def IsActive {k ℓ : ℕ} (dom : Finset (Coord k ℓ)) (g : ℕ) (c : Coord k ℓ) : Prop :=
  1 ≤ g ∧ g ≤ reps k * numRows dom ∧ ∃ r, rowAt dom g = some r ∧ checkMatrix k ℓ r c = 1

open scoped Classical in
/-- The representative position of the track class at the position `g` and coordinate `c`: the largest
position `g' ≤ g` with a nonzero entry in the column `c`, or `0` if there is none. This is the
identification "if `β_{e,j}(c) = 0`, identify `trk_{e,h,j-1,c}[s]` and `trk_{e,h,j,c}[s]`" of §7.1, item 1,
p.37, applied along the whole strip. -/
noncomputable def repPos {k ℓ : ℕ} (dom : Finset (Coord k ℓ)) (g : ℕ) (c : Coord k ℓ) : ℕ :=
  Nat.findGreatest (fun g' => IsActive dom g' c) g

/-- The vertex names of the matrix pair `G̃₀, G̃₁` (§7.1, pp.36–37).

**Formalization Note** `crd`, `sum` and `junc` are the coordinate, sum and junction names of §5.1
(`junc e c s t` is `junc_{e,c}[s, t, s + t]`). `trk e g c s` is the internal track symbol at the position
`g` of `rowAt`, i.e. `trk_{e,h,j,c}[s]` with `g = (h - 1)·m_e + j`; `coef e g b` is `coef_{e,h,j}[b]`; and
`upd e g c s t` is `upd_{e,h,j,c}[s, t, b]` with `b = s + t`, the unique `b` with `s + t + b = 0` over `𝔽₂`.
All names exist as terms; `MatrixSystem.IsVertex` selects the vertices of `G̃_ε`. -/
inductive MVtx (k ℓ : ℕ) (W E : Type*) where
  | crd (v : W) (c : Coord k ℓ) (s : ZMod 2)
  | sum (e : E) (c : Coord k ℓ) (t : ZMod 2)
  | junc (e : E) (c : Coord k ℓ) (s t : ZMod 2)
  | trk (e : E) (g : ℕ) (c : Coord k ℓ) (s : ZMod 2)
  | coef (e : E) (g : ℕ) (b : ZMod 2)
  | upd (e : E) (g : ℕ) (c : Coord k ℓ) (s t : ZMod 2)

/-- The color classes of the matrix pair (§7.1): a name with its subscripts, without the bracket. Every
resulting class has its own color ("distinct resulting color classes have distinct colors"); coefficient
and update classes have fresh colors. -/
inductive MColor (k ℓ : ℕ) (W E : Type*) where
  | crd (v : W) (c : Coord k ℓ)
  | sum (e : E) (c : Coord k ℓ)
  | junc (e : E) (c : Coord k ℓ)
  | trk (e : E) (g : ℕ) (c : Coord k ℓ)
  | coef (e : E) (g : ℕ)
  | upd (e : E) (g : ℕ) (c : Coord k ℓ)

/-- The color of a vertex name of the matrix pair. -/
def MVtx.color {k ℓ : ℕ} {W E : Type*} : MVtx k ℓ W E → MColor k ℓ W E
  | .crd v c _ => .crd v c
  | .sum e c _ => .sum e c
  | .junc e c _ _ => .junc e c
  | .trk e g c _ => .trk e g c
  | .coef e g _ => .coef e g
  | .upd e g c _ _ => .upd e g c

namespace MatrixSystem

variable {k ℓ : ℕ} {W E : Type*} (I : ImplicitSystem k ℓ W E)

/-- The last position with a nonzero entry in the column `c` of the strip of `e`; its track class
contains the final position `R·m_e` and is identified with the final endpoint. -/
noncomputable def endPos (e : E) (c : Coord k ℓ) : ℕ :=
  repPos (I.schema e).dom (reps k * numRows (I.schema e).dom) c

/-- The track vertex `trk_{e,h,j,c}[s]` at the position `g`, after the identifications of §7.1, item 1,
p.37. Its class is represented by the position `repPos g`. If that is `0`, the class is the initial
endpoint: `crd_{u,σ(c)}[s]` for a binary schema and `sum_{e,c}[s]` for a ternary one. If it is the last
nonzero position, the class contains `trk_{e,R,m_e,c}` and is the final endpoint: `crd_{v,τ(c)}[s]` for a
binary schema and `crd_{w,π(c)}[s]` for a ternary one. Otherwise it is the internal track pair at
`repPos g`. -/
noncomputable def mtrack (e : E) (g : ℕ) (c : Coord k ℓ) (s : ZMod 2) : MVtx k ℓ W E :=
  if repPos (I.schema e).dom g c = 0 then
    match (I.schema e).third with
    | none => .crd (I.schema e).u ((I.schema e).σ c) s
    | some _ => .sum e c s
  else if repPos (I.schema e).dom g c = endPos I e c then
    match (I.schema e).third with
    | none => .crd (I.schema e).v ((I.schema e).τ c) s
    | some (w, π) => .crd w (π c) s
  else .trk e (repPos (I.schema e).dom g c) c s

/-- The edge relation of the matrix pair (§5.1, item 2, p.24 and §7.1, item 2, p.37), read from the
junction and update side. A junction `junc_{e,c}[s, t, s + t]` is adjacent to `crd_{u,σ(c)}[s]`,
`crd_{v,τ(c)}[t]` and `sum_{e,c}[s + t]`. The update `upd_{e,h,j,c}[s, t, b]` is adjacent to
`trk_{e,h,j-1,c}[s]`, `trk_{e,h,j,c}[t]` and `coef_{e,h,j}[b]`, with `b = s + t`. There are no other
edges. -/
inductive Edge : MVtx k ℓ W E → MVtx k ℓ W E → Prop
  | junc_u (e : E) (c : Coord k ℓ) (s t : ZMod 2) :
      Edge (.junc e c s t) (.crd (I.schema e).u ((I.schema e).σ c) s)
  | junc_v (e : E) (c : Coord k ℓ) (s t : ZMod 2) :
      Edge (.junc e c s t) (.crd (I.schema e).v ((I.schema e).τ c) t)
  | junc_sum (e : E) (c : Coord k ℓ) (s t : ZMod 2) :
      Edge (.junc e c s t) (.sum e c (s + t))
  | upd_prev (e : E) (g : ℕ) (c : Coord k ℓ) (s t : ZMod 2) :
      Edge (.upd e g c s t) (mtrack I e (g - 1) c s)
  | upd_next (e : E) (g : ℕ) (c : Coord k ℓ) (s t : ZMod 2) :
      Edge (.upd e g c s t) (mtrack I e g c t)
  | upd_coef (e : E) (g : ℕ) (c : Coord k ℓ) (s t : ZMod 2) :
      Edge (.upd e g c s t) (.coef e g (s + t))

/-- The vertex names retained in `G̃_ε` (§7.1, pp.36–37).

1. `crd_{v,c}[s]` for `c ∈ 𝔠_v`, initialized as in §5.1: if `ι(v) ∈ {0, 1}` one vertex is kept, bit `0` in
   `G̃₀`, and in `G̃₁` bit `ι(v)` in the first block and bit `0` elsewhere.
2. `sum_{e,c}[t]` and `junc_{e,c}[s, t, s + t]` for a ternary schema and `c ∈ 𝔠_e`.
3. The internal track pairs: `trk` at a position with a nonzero entry in the column `c ∈ 𝔠_e` that is not
   the last such position (whose class is the final endpoint).
4. `coef_{e,h,j}[b]` for every position `1 ≤ g ≤ R·m_e`, and `upd_{e,h,j,c}[s, t, s + t]` for every nonzero
   entry `β_{e,j}(c) = 1`, `c ∈ 𝔠_e`.

**Formalization Note** The first block is the index `0`, and `ε * b` is `0` in `G̃₀` and `b` in `G̃₁`, as in
the published `ImplicitSystem.IsVertex`. A schema with empty domain has `m_e = 0` and no strip. -/
def IsVertex (ε : ZMod 2) : MVtx k ℓ W E → Prop
  | .crd v c s => c ∈ I.dom v ∧ ∀ b, I.init v = some b → s = if c.1.val = 0 then ε * b else 0
  | .sum e c _ => (I.schema e).third.isSome ∧ c ∈ (I.schema e).dom
  | .junc e c _ _ => (I.schema e).third.isSome ∧ c ∈ (I.schema e).dom
  | .trk e g c _ => c ∈ (I.schema e).dom ∧ IsActive (I.schema e).dom g c ∧ g ≠ endPos I e c
  | .coef e g _ => 1 ≤ g ∧ g ≤ reps k * numRows (I.schema e).dom
  | .upd e g c _ _ => c ∈ (I.schema e).dom ∧ IsActive (I.schema e).dom g c

/-- The vertex set of `G̃_ε`. -/
abbrev Vertex (ε : ZMod 2) := {p : MVtx k ℓ W E // IsVertex I ε p}

instance vertex_finite [Finite W] [Finite E] (ε : ZMod 2) : Finite (Vertex I ε) := by
  have hb : ∀ e : E, reps k * numRows (I.schema e).dom < reps k * (k - 1 + ℓ) + 1 := fun e =>
    Nat.lt_succ_of_le (Nat.mul_le_mul_left _ (numRows_le _))
  have hfin : ({p | IsVertex I ε p} : Set (MVtx k ℓ W E)).Finite := by
    refine Set.Finite.subset (s :=
      Set.range (fun x : W × Coord k ℓ × ZMod 2 => MVtx.crd x.1 x.2.1 x.2.2) ∪
      Set.range (fun x : E × Coord k ℓ × ZMod 2 => MVtx.sum x.1 x.2.1 x.2.2) ∪
      Set.range (fun x : E × Coord k ℓ × ZMod 2 × ZMod 2 =>
        MVtx.junc x.1 x.2.1 x.2.2.1 x.2.2.2) ∪
      Set.range (fun x : E × Fin (reps k * (k - 1 + ℓ) + 1) × Coord k ℓ × ZMod 2 =>
        MVtx.trk x.1 x.2.1.val x.2.2.1 x.2.2.2) ∪
      Set.range (fun x : E × Fin (reps k * (k - 1 + ℓ) + 1) × ZMod 2 =>
        MVtx.coef x.1 x.2.1.val x.2.2) ∪
      Set.range (fun x : E × Fin (reps k * (k - 1 + ℓ) + 1) × Coord k ℓ × ZMod 2 × ZMod 2 =>
        MVtx.upd x.1 x.2.1.val x.2.2.1 x.2.2.2.1 x.2.2.2.2)) ?_ ?_
    · exact (((((Set.finite_range _).union (Set.finite_range _)).union (Set.finite_range _)).union
        (Set.finite_range _)).union (Set.finite_range _)).union (Set.finite_range _)
    · intro p hp
      cases p with
      | crd v c s => exact Or.inl <| Or.inl <| Or.inl <| Or.inl <| Or.inl ⟨(v, c, s), rfl⟩
      | sum e c t => exact Or.inl <| Or.inl <| Or.inl <| Or.inl <| Or.inr ⟨(e, c, t), rfl⟩
      | junc e c s t => exact Or.inl <| Or.inl <| Or.inl <| Or.inr ⟨(e, c, s, t), rfl⟩
      | trk e g c s =>
        have hp' : c ∈ (I.schema e).dom ∧ IsActive (I.schema e).dom g c ∧ g ≠ endPos I e c := hp
        exact Or.inl <| Or.inl <| Or.inr
          ⟨(e, ⟨g, lt_of_le_of_lt hp'.2.1.2.1 (hb e)⟩, c, s), rfl⟩
      | coef e g b =>
        have hp' : 1 ≤ g ∧ g ≤ reps k * numRows (I.schema e).dom := hp
        exact Or.inl <| Or.inr ⟨(e, ⟨g, lt_of_le_of_lt hp'.2 (hb e)⟩, b), rfl⟩
      | upd e g c s t =>
        have hp' : c ∈ (I.schema e).dom ∧ IsActive (I.schema e).dom g c := hp
        exact Or.inr ⟨(e, ⟨g, lt_of_le_of_lt hp'.2.2.1 (hb e)⟩, c, s, t), rfl⟩
  exact hfin.to_subtype

noncomputable instance vertex_fintype [Finite W] [Finite E] (ε : ZMod 2) :
    Fintype (Vertex I ε) := Fintype.ofFinite _

/-- The colored graph `G̃_ε` of the matrix construction (§7.1, pp.36–37): the retained vertices, the
edges of `Edge` (made undirected) between them, and each vertex colored by its name without the
bracket. -/
def graph (ε : ZMod 2) : ColoredGraph (MColor k ℓ W E) (Vertex I ε) where
  graph := (SimpleGraph.fromRel (Edge I)).comap Subtype.val
  χ := fun p => p.val.color

/-- `Λ = 1 + max({0} ∪ {m_e : e ∈ E})` (§7.1, p.36). -/
noncomputable def Λ [Fintype E] : ℕ := 1 + Finset.univ.sup fun e => numRows (I.schema e).dom

end MatrixSystem

end Supplement

end ImplicitParityWL


