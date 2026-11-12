-- Prove2me | Definitions.Def_LocalSweepFT_Chain
-- name    : LocalSweepFT_Chain
-- status  : Definition
-- author  : @iris
-- created : 2026-11-11T08:38:21.909206+00:00
-- url     : https://prove2.me/theorems/b2e9060f-328c-49e7-9270-31603cbaf6e5
-- title:
--   Cubical complex $\mathcal T^d_n$, chains, $\partial^-$, $\partial^+$, restrictions, components and the transpose map $\phi$
-- statement:
--   Fix a commutative ring $R$ of vertex coordinates: $R=\mathbb Z_n$ gives the $d$-dimensional cubical torus $\mathcal T^d_n$, and $R=\mathbb Z$ gives its infinite cover $\mathcal T^d_\infty$. An $i$-cell $\theta_{v,S'}$ is a root $v\in R^d$ together with a set $S'$ of $i$ of the $d$ generators $1_1,\dots,1_d$; its vertices are $V(\theta_{v,S'})=\{v+\sum_{g\in I}g : I\subseteq S'\}$. The $i$-chains $C_i$ are the finitely supported $\mathbb F_2$-combinations of $i$-cells, and the boundary and coboundary maps are
--   $$\partial^-\theta_{v,S'}=\sum_{g\in S'}\big(\theta_{v,S'/g}+\theta_{gv,S'/g}\big),\qquad \partial^+\theta_{v,S'}=\sum_{g\in S/S'}\big(\theta_{v,S'\cup g}+\theta_{g^{-1}v,S'\cup g}\big).$$
--
--   The file also defines:
--   1. the restriction $z|_v$ (cells containing $v$), the positive restriction $z|_{v+}$ (cells rooted at $v$), and "rooted at $v$";
--   2. $V(z)$, and $\mathrm{Str}^0_+(v,z)=V(z)\cap\{gv:g\in S\}$ (Def. 4.5);
--   3. adjacency of distinct $i$-cells sharing an $(i-1)$-face, and the connected components of a chain;
--   4. the Hamming distance and the inner product $\langle x,y\rangle=\sum_f x_f y_f$;
--   5. the X-stabilizer space $\operatorname{im}(\partial^-:C_{i+1}\to C_i)$;
--   6. the transpose map $\phi(\theta_{v,S'})=\theta_{S'v,\,S/S'}$ (Def. 4.31) from $i$-cells to $j$-cells, $i+j=d$.
--
--   These are the objects on which every statement of the mission is phrased.
--
--   **Formalization Note** On $0$-chains $\partial^-$ is the empty sum $0$, and on $d$-chains $\partial^+$ is $0$. A cell's faces are its geometric $(i-1)$-faces (incidence), not its boundary coefficients.
-- source:
--   Ponarovsky, Local Quantum Fault Tolerance Without Expansion, arXiv:2610.38847 (version of November 3, 2026, sha256 85723eb5…), Definitions 4.1–4.2, pp.15–17; Definition 4.5, p.18; Definition 4.31, p.32

import Mathlib

namespace LocalSweepFT

/-! Ponarovsky, *Local Quantum Fault Tolerance Without Expansion*, arXiv:2610.38847 (version of
November 3, 2026, sha256 85723eb5…), Definitions 4.1–4.2 (pp.15–17), Definition 4.5 (p.18) and
Definition 4.31 (p.32): the cubical complex `T^d_n`, its chains, the boundary and coboundary maps,
restrictions, connected components, and the transpose map `ϕ`. -/

/-- Vertices of the cubical complex over the coefficient ring `R`: `ℤ_n^d` for `R = ZMod n` (the
torus `T^d_n`, Def 4.1, p.15) and `ℤ^d` for `R = ℤ` (the infinite cover `T^d_∞`, §4.2, p.21). -/
abbrev Vtx (R : Type) (d : ℕ) := Fin d → R

/-- Direction sets of size `i`: subsets `S′ ⊆ S = {1_1, …, 1_d}` with `|S′| = i`. The generator
`1_j` is identified with the index `j : Fin d`. -/
abbrev DirSet (d i : ℕ) := {S : Finset (Fin d) // S.card = i}

/-- An `i`-cell `θ_{v,S′}` (Def 4.1, p.16): a root `v` and a direction set `S′` with `|S′| = i`.
The cell is the pair itself, not its vertex set. -/
abbrev Cell (R : Type) (d i : ℕ) := Vtx R d × DirSet d i

/-- `i`-dimensional chains `C_i = (F_i; 𝔽₂)` (Def 4.2, p.16): finitely supported `𝔽₂`-valued
functions on `i`-cells. On the torus every chain is finitely supported; on `ℤ^d` a chain is a finite
sum of cells. -/
abbrev Chain (R : Type) (d i : ℕ) := Cell R d i →₀ ZMod 2

/-- The complement direction set `S/S′`, of size `d − i`. -/
def DirSet.compl {d i : ℕ} (S : DirSet d i) : DirSet d (d - i) :=
  ⟨S.1ᶜ, by rw [Finset.card_compl, Fintype.card_fin, S.2]⟩

/-- `S′` with one generator `g ∈ S′` removed (`S′/g`). -/
def DirSet.erase {d i : ℕ} (S : DirSet d i) (g : Fin d) (hg : g ∈ S.1) : DirSet d (i - 1) :=
  ⟨S.1.erase g, by rw [Finset.card_erase_of_mem hg, S.2]⟩

/-- `S′` with one generator `g ∉ S′` added (`S′ ∪ g`). -/
def DirSet.insert {d i : ℕ} (S : DirSet d i) (g : Fin d) (hg : g ∉ S.1) : DirSet d (i + 1) :=
  ⟨Insert.insert g S.1, by rw [Finset.card_insert_of_notMem hg, S.2]⟩

variable {R : Type} [CommRing R] [DecidableEq R] {d : ℕ}

/-- The generator `g = 1_j` as a translation vector (the group law is written additively). -/
def unitVec (j : Fin d) : Vtx R d := Pi.single j 1

/-- `Σ_{g ∈ I} g`, so that `I v` of the paper (`(Π_{g∈I} g) v`) is `v + stepVec I`. -/
def stepVec (I : Finset (Fin d)) : Vtx R d := ∑ j ∈ I, unitVec j

/-- The vertex set `V(θ_{v,S′}) = {(Π_{g∈I} g) v : I ⊆ S′}` (Def 4.1, p.16). -/
def cellVerts {i : ℕ} (c : Cell R d i) : Finset (Vtx R d) :=
  c.2.1.powerset.image (fun I => c.1 + stepVec I)

/-- `V(z)`: the vertices of the cells supporting `z`; "`v ∈ z`" of the paper means
`v ∈ chainVerts z` (p.17). -/
def chainVerts {i : ℕ} (z : Chain R d i) : Finset (Vtx R d) :=
  z.support.biUnion cellVerts

/-- The `(i−1)`-faces of an `i`-cell: `θ_{v,S′/g}` and `θ_{gv,S′/g}` for `g ∈ S′`. This is the
incidence relation ("`f` lies in a cell"), not the boundary coefficient (p.17). -/
def cellFaces {i : ℕ} (c : Cell R d i) : Finset (Cell R d (i - 1)) :=
  c.2.1.attach.biUnion (fun g =>
    {(c.1, c.2.erase g.1 g.2), (c.1 + unitVec g.1, c.2.erase g.1 g.2)})

/-- `∂⁻θ_{v,S′} = Σ_{g∈S′} (θ_{v,S′/g} + θ_{gv,S′/g})` (Def 4.2, p.17). -/
noncomputable def bdryCell {i : ℕ} (c : Cell R d i) : Chain R d (i - 1) :=
  ∑ g : {g // g ∈ c.2.1},
    (Finsupp.single (c.1, c.2.erase g.1 g.2) 1 + Finsupp.single (c.1 + unitVec g.1, c.2.erase g.1 g.2) 1)

/-- `∂⁺θ_{v,S′} = Σ_{g∈S/S′} (θ_{v,S′∪g} + θ_{g⁻¹v,S′∪g})` (Def 4.2, p.17). -/
noncomputable def cobdryCell {i : ℕ} (c : Cell R d i) : Chain R d (i + 1) :=
  ∑ g : {g // g ∉ c.2.1},
    (Finsupp.single (c.1, c.2.insert g.1 g.2) 1 + Finsupp.single (c.1 - unitVec g.1, c.2.insert g.1 g.2) 1)

/-- The boundary operator `∂⁻ : C_i → C_{i−1}`, extended linearly (Def 4.2, p.17).

**Formalization Note.** On `0`-chains the defining sum is empty, so `∂⁻ = 0` there (the paper
defines `∂⁻` only for `i > 0`; the value on `0`-chains is never used). -/
noncomputable def bdry {i : ℕ} : Chain R d i →ₗ[ZMod 2] Chain R d (i - 1) :=
  Finsupp.linearCombination (ZMod 2) bdryCell

/-- The coboundary operator `∂⁺ : C_i → C_{i+1}`, extended linearly (Def 4.2, p.17). On
`d`-chains the defining sum is empty. -/
noncomputable def cobdry {i : ℕ} : Chain R d i →ₗ[ZMod 2] Chain R d (i + 1) :=
  Finsupp.linearCombination (ZMod 2) cobdryCell

/-- The `i`-chains in the image of `∂⁻ : C_{i+1} → C_i`; for `i = d′` these are the binary
representations of the X-stabilizers `C_Z^⊥` (p.39). -/
noncomputable def bdryRange (R : Type) [CommRing R] [DecidableEq R] (d i : ℕ) :
    Submodule (ZMod 2) (Chain R d i) :=
  LinearMap.range (bdry (R := R) (d := d) (i := i + 1))

/-- The restriction `z|_v` retaining the cells having `v` among their vertices (p.17). -/
def restrictAt {i : ℕ} (v : Vtx R d) (z : Chain R d i) : Chain R d i :=
  z.filter (fun c => v ∈ cellVerts c)

/-- The positive restriction `z|_{v+}` retaining the cells rooted at `v` (p.17). -/
def restrictPos {i : ℕ} (v : Vtx R d) (z : Chain R d i) : Chain R d i :=
  z.filter (fun c => c.1 = v)

/-- `z` is rooted at `v`: all its supporting cells have root `v` (p.17). -/
def IsRootedAt {i : ℕ} (v : Vtx R d) (z : Chain R d i) : Prop :=
  ∀ c ∈ z.support, c.1 = v

/-- `Str⁰₊(v, z) := V(z) ∩ {gv : g ∈ S}` (Def 4.5, p.18). -/
def str0 {i : ℕ} (v : Vtx R d) (z : Chain R d i) : Finset (Vtx R d) :=
  (chainVerts z).filter (fun u => ∃ g : Fin d, u = v + unitVec g)

/-- The adjacency graph on the supporting cells of `z`: two distinct `i`-faces are adjacent if they
share an `(i−1)`-face (p.17). -/
def supportGraph {i : ℕ} (z : Chain R d i) : SimpleGraph {c // c ∈ z.support} :=
  SimpleGraph.fromRel (fun a b => ∃ f, f ∈ cellFaces a.1 ∧ f ∈ cellFaces b.1)

open Classical in
/-- The connected component of `z` containing the supporting cell `c` (as a chain): the restriction
of `z` to the cells reachable from `c` in `supportGraph z` (p.17). -/
noncomputable def componentOf {i : ℕ} (z : Chain R d i) (c : Cell R d i) : Chain R d i :=
  z.filter (fun c' => ∃ (hc : c ∈ z.support) (hc' : c' ∈ z.support),
    (supportGraph z).Reachable ⟨c, hc⟩ ⟨c', hc'⟩)

open Classical in
/-- The connected components of `z`, as chains (p.17). The zero chain has no components. -/
noncomputable def components {i : ℕ} (z : Chain R d i) : Finset (Chain R d i) :=
  z.support.image (componentOf z)

/-- The Hamming distance between two chains: the number of cells where they differ. -/
noncomputable def hamming {i : ℕ} (x y : Chain R d i) : ℕ := (x - y).support.card

/-- The standard inner product `⟨x, y⟩ = Σ_f x(f) y(f)` over `𝔽₂` (p.18). -/
noncomputable def inner {i : ℕ} (x y : Chain R d i) : ZMod 2 := x.sum (fun c a => a * y c)

/-- Reindex a cell along an equality of dimensions (root and direction set unchanged). -/
def Cell.recast {i j : ℕ} (h : i = j) (c : Cell R d i) : Cell R d j :=
  (c.1, ⟨c.2.1, h ▸ c.2.2⟩)

/-- Reindex a chain along an equality of dimensions. -/
noncomputable def Chain.recast {i j : ℕ} (h : i = j) (z : Chain R d i) : Chain R d j :=
  Finsupp.mapDomain (Cell.recast h) z

/-- The transpose map `ϕ(θ_{v,S′}) := θ_{S′v, S/S′}` (Def 4.31, p.32), from `i`-cells to
`j`-cells with `i + j = d`. -/
def phiCell {i j : ℕ} (h : i + j = d) (c : Cell R d i) : Cell R d j :=
  (c.1 + stepVec c.2.1, ⟨c.2.1ᶜ, by rw [Finset.card_compl, Fintype.card_fin, c.2.2]; omega⟩)

/-- The transpose map on chains, extended linearly (Def 4.31, p.32). -/
noncomputable def phiChain {i j : ℕ} (h : i + j = d) (z : Chain R d i) : Chain R d j :=
  Finsupp.mapDomain (phiCell h) z

end LocalSweepFT


