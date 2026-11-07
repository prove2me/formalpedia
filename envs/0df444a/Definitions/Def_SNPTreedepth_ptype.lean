-- Prove2me | Definitions.Def_SNPTreedepth_ptype
-- name    : SNPTreedepth_ptype
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T12:27:03.091604+00:00
-- url     : https://prove2.me/theorems/23cca0c9-a7f8-4852-b753-20fdcd63a23d
-- title:
--   Vertex $p$-types, $p$-abundance, $p$-routes, normalization and $p$-route patterns
-- statement:
--   Fix a relational structure $R$, a treedepth decomposition $T$ and $p\ge1$.
--
--   1. **Atomic type.** For a tuple $(v_1,\dots,v_z)$, $\mathrm{atp}_R(v_1,\dots,v_z)$ is the set of atomic formulas $E_i(x_{n_1},\dots,x_{n_a})$ and $x_n=x_{n'}$ that hold of it.
--   2. **Vertex $p$-type.** With $w_1,\dots,w_d=v$ the root path of $v$, $p\text{-type}(v)=(\delta_v,\lambda_v)$ where $\lambda_v=\mathrm{atp}_R(w_1,\dots,w_d)$ and, for a non-leaf $v$ with children $C_v$, $\delta_v(t)=|\{w\in C_v: p\text{-type}(w)=t\}|$ if this number is at most $p-1$ and $\delta_v(t)=\star$ otherwise; leaves have the empty label.
--   3. **Abundance.** $t$ is $p$-abundant in $(\delta,\lambda)$ if $\delta(t)=\star$; a vertex is $p$-abundant if its type is $p$-abundant in its parent's type.
--   4. **$p$-route.** $\mathrm{rt}(\text{root})=((p\text{-type}(\text{root}),1))$ and $\mathrm{rt}(v)=\mathrm{rt}(w)\diamond(t,i)$ when $v$ is the $i$-th smallest child of type $t$ of its parent $w$. An entry $(t_\ell,i_\ell)$ with $\ell\ge2$ is abundant if $t_\ell$ is $p$-abundant in $t_{\ell-1}$.
--   5. **Normalization and pattern.** For a finite set $S$ of routes, $I(S)$ is the set of indices of abundant entries and $\pi_S(i)=|\{i'\in I(S): i'\le i\}|$; $\nu_S$ replaces every abundant entry $(t,i)$ by $(t,\pi_S(i))$. The **$p$-route pattern** of $(v_1,\dots,v_z)$ is $(\nu_S(\mathrm{rt}(v_1)),\dots,\nu_S(\mathrm{rt}(v_z)))$ with $S=\{\mathrm{rt}(v_1),\dots,\mathrm{rt}(v_z)\}$; vertices $w_1,\dots,w_z$ with $\mathrm{rt}(w_m)$ equal to the $m$-th route of a pattern are its **realizing vertices**.
--
--   These are the equivalence notions on elements and on tuples on which purity and the extension and existence theorems rest.
--
--   **Formalization Note** A vertex $p$-type is represented by a natural number, the injective `Encodable` code of the pair $(\lambda_v,\delta_v)$, where $\delta_v$ is the finite set of pairs $(t,\min(\text{count}_t,p))$ ($p$ standing for $\star$); equal codes mean equal types, also across different structures. The recursion uses fuel $|V|$, which exceeds every subtree height. Routes are lists of (type code, index) pairs; positions are $0$-based internally.
-- source:
--   Depian, Ganian, Greilhuber, Gründel, Wietheger, A Uniform Algorithm for Strict NP on Bounded-Treedepth Structures, STOC 2027 submission (manuscript sha256 98e4e1a9…), Definitions 1, 2, 17, 4, 5, 24, pp.14–23 (PDF pp.15–24)

import Mathlib
import Definitions.Def_SNPTreedepth_Structure
import Definitions.Def_SNPTreedepth_treedepth

set_option autoImplicit false

namespace SNPTreedepth

/-- A syntactic **atomic formula** over the variables `x₀, x₁, …` (Depian et al., *A Uniform
Algorithm for Strict NP on Bounded-Treedepth Structures*, STOC 2027 submission (manuscript sha256
98e4e1a9…), Definition 1, pp.14–15): `inl (i, [n₁, …, n_a])` is `E_i(x_{n₁}, …, x_{n_a})` and
`inr (n, n')` is `x_n = x_{n'}`.

**Formalization Note** Variable positions and relation indices start at `0`. Formulas are plain
data, so atomic types of tuples in different structures over the same signature can be compared. -/
abbrev AtomF := (ℕ × List ℕ) ⊕ (ℕ × ℕ)

/-- The **atomic type** of a tuple `(v₁, …, v_z)` (Depian et al., Definition 1, p.15) in the
relational family `(V, E₁, …, E_b)` with arities `ar`: the set of atomic formulas `α` over the
positions of the tuple with `R ⊨ α(v₁, …, v_z)`, namely `E_i(x_{n₁}, …, x_{n_a})` with
`(v_{n₁}, …, v_{n_a}) ∈ E_i`, `a = ar(E_i)`, and `x_n = x_{n'}` with `v_n = v_{n'}`.

**Formalization Note** Stated for a raw family of relations (no positivity of arities needed) so
that it serves both for input structures (`atp`) and for solution relations (`solType`,
Definition 29). The tuple is a list. -/
noncomputable def atpRaw {V : Type*} {b : ℕ} (ar : Fin b → ℕ)
    (rel : (i : Fin b) → Set (Fin (ar i) → V)) (v : List V) : Finset AtomF :=
  open Classical in
  ((Finset.univ.filter
      (fun a : (i : Fin b) × (Fin (ar i) → Fin v.length) => (fun j => v.get (a.2 j)) ∈ rel a.1)).image
      (fun a => Sum.inl (a.1.val, List.ofFn (fun j => (a.2 j).val)))) ∪
  ((Finset.univ.filter (fun a : Fin v.length × Fin v.length => v.get a.1 = v.get a.2)).image
      (fun a => Sum.inr (a.1.val, a.2.val)))

/-- The atomic type `atp_R(v₁, …, v_z)` of a tuple in a relational structure
(Depian et al., Definition 1, p.15). -/
noncomputable def atp {σ : Signature} {V : Type*} (R : Structure σ V) (v : List V) : Finset AtomF :=
  atpRaw σ.ar R.rel v

section Types

variable {σ : Signature} {V : Type*} [Fintype V]

/-- Auxiliary recursion for the vertex `p`-type, with fuel `n`; see `ptype`. -/
noncomputable def ptypeAux (R : Structure σ V) (T : RootedForest V) (p : ℕ) : ℕ → V → ℕ
  | 0, v => Encodable.encode (atp R (T.rootPath v), (∅ : Finset (ℕ × ℕ)))
  | n + 1, v =>
    open Classical in
    Encodable.encode (atp R (T.rootPath v),
      (T.children v).image (fun c =>
        (ptypeAux R T p n c,
          min p ((T.children v).filter (fun c' => ptypeAux R T p n c' = ptypeAux R T p n c)).card)))

/-- The **vertex `p`-type** `p-type(v) = (δ_v, λ_v)` of `v` in `(R, T)` (Depian et al.,
Definition 2, p.17; first stated p.6). With `P = w₁, …, w_d` the path from the root of `T` to
`v = w_d`, the **ancestor label** is `λ_v = atp_R(w₁, …, w_d)`. The **subtree label** of a leaf is
the empty label `ε`; for a non-leaf `v` with children `C_v` it is the function on
`{p-type(w) | w ∈ C_v}` with
`δ_v(t) = |{w ∈ C_v | p-type(w) = t}|` if that number is at most `p − 1`, and `δ_v(t) = ⋆`
otherwise.

**Formalization Note** A `p`-type is represented by a natural number: the code, under Mathlib's
injective `Encodable.encode`, of the pair `(λ_v, δ_v)`, where `δ_v` is the finite set of pairs
`(t, min(count_t, p))` over the child types `t` (themselves codes), so the value `p` stands for `⋆`
and `ε` is the empty set. Hence two vertices, in any two structures over the same signature with
any decompositions, have equal codes exactly when they have equal `p`-types (Lemma 28 (3) compares
types across structures). The recursion runs on fuel `Fintype.card V`, which exceeds the height of
every subtree; with enough fuel a leaf gets `(λ_v, ∅)` and the value does not depend on the fuel. -/
noncomputable def ptype (R : Structure σ V) (T : RootedForest V) (p : ℕ) (v : V) : ℕ :=
  ptypeAux R T p (Fintype.card V) v

/-- The number of children of `x` in `T` whose vertex `p`-type is (the code) `t`. -/
noncomputable def typeCount (R : Structure σ V) (T : RootedForest V) (p : ℕ) (x : V) (t : ℕ) : ℕ :=
  open Classical in ((T.children x).filter (fun c => ptype R T p c = t)).card

/-- A vertex `p`-type `t` is **`p`-abundant** in the vertex `p`-type `t' = (δ, λ)` (Depian et al.,
Definition 17, p.17): `t` lies in the domain of `δ` and `δ(t) = ⋆`.

**Formalization Note** On codes: `t'` decodes to a pair `(λ, δ)` and `(t, p) ∈ δ` (the value `p`
represents `⋆`, see `ptype`). -/
def AbundantIn (p t t' : ℕ) : Prop :=
  ∃ lam : Finset AtomF, ∃ δ : Finset (ℕ × ℕ),
    (Encodable.decode t' : Option (Finset AtomF × Finset (ℕ × ℕ))) = some (lam, δ) ∧ (t, p) ∈ δ

/-- A vertex `v` with parent `w` is **`p`-abundant** (Depian et al., Definition 17, p.17) if
`p-type(v)` is `p`-abundant in `p-type(w)`. -/
def IsAbundantVertex (R : Structure σ V) (T : RootedForest V) (p : ℕ) (v : V) : Prop :=
  ∃ w, T.parent v = some w ∧ AbundantIn p (ptype R T p v) (ptype R T p w)

/-- The index `i` of the route entry of `v` (Depian et al., Definition 4, p.19): `1` at a root, and
otherwise the `i` such that `v` is the `i`-th smallest element, in the total order of `V`, among
the children of its parent of type `p-type(v)`. -/
noncomputable def routeIndex [LinearOrder V] (R : Structure σ V) (T : RootedForest V) (p : ℕ)
    (v : V) : ℕ :=
  match T.parent v with
  | none => 1
  | some w => ((T.children w).filter (fun c => ptype R T p c = ptype R T p v ∧ c ≤ v)).card

/-- The **`p`-route** `rt(v)` of a vertex `v` (Depian et al., Definition 4, p.19): `rt(u) =
((p-type(u), 1))` for the root `u`, and `rt(v) = rt(w) ⋄ (t, i)` for a non-root `v` with parent
`w`, `t = p-type(v)`, and `v` the `i`-th smallest child of `w` of type `t`. Equivalently, the list
of entries `(p-type(u_ℓ), i_ℓ)` along the root path `u₁, …, u_d = v`. -/
noncomputable def route [LinearOrder V] (R : Structure σ V) (T : RootedForest V) (p : ℕ) (v : V) :
    List (ℕ × ℕ) :=
  (T.rootPath v).map (fun u => (ptype R T p u, routeIndex R T p u))

end Types

/-- The entry at position `ℓ` (0-based) of the `p`-route `ϱ` is **abundant** (Depian et al.,
Definition 4, p.19): it is not the first entry and its type is `p`-abundant in the type of the
preceding entry. -/
def EntryAbundant (p : ℕ) (ϱ : List (ℕ × ℕ)) (ℓ : ℕ) : Prop :=
  ∃ e e' : ℕ × ℕ, ℓ ≥ 1 ∧ ϱ[ℓ]? = some e ∧ ϱ[ℓ - 1]? = some e' ∧ AbundantIn p e.1 e'.1

/-- `I(S)`, the set of indices `i` of abundant entries `(t, i)` in the routes of the finite set
`S` (Depian et al., Definition 5, p.20). -/
noncomputable def abundantIndices (p : ℕ) (S : Finset (List (ℕ × ℕ))) : Finset ℕ :=
  open Classical in
  S.biUnion (fun ϱ => ((Finset.range ϱ.length).filter (fun ℓ => EntryAbundant p ϱ ℓ)).image
    (fun ℓ => (ϱ[ℓ]?.getD (0, 0)).2))

/-- The **normalization** `ν_S(ϱ)` of a `p`-route with respect to a finite set `S` of `p`-routes
(Depian et al., Definition 5, p.20): every abundant entry `(t_ℓ, i_ℓ)` becomes `(t_ℓ, π_S(i_ℓ))`
with `π_S(i) = |{i' ∈ I(S) | i' ≤ i}|` the rank of `i` in `I(S)`, and every other entry is kept. -/
noncomputable def normalize (p : ℕ) (S : Finset (List (ℕ × ℕ))) (ϱ : List (ℕ × ℕ)) :
    List (ℕ × ℕ) :=
  open Classical in
  ϱ.mapIdx (fun ℓ e =>
    if EntryAbundant p ϱ ℓ then (e.1, ((abundantIndices p S).filter (· ≤ e.2)).card) else e)

section Patterns

variable {σ : Signature} {V : Type*} [Fintype V] [LinearOrder V]

/-- The **`p`-route pattern** of a tuple `(v₁, …, v_z)` (Depian et al., Definition 5, p.20):
`(ν_S(rt(v₁)), …, ν_S(rt(v_z)))` with `S = {rt(v₁), …, rt(v_z)}`. -/
noncomputable def pattern (R : Structure σ V) (T : RootedForest V) (p : ℕ) {z : ℕ} (v : Fin z → V) :
    Fin z → List (ℕ × ℕ) :=
  open Classical in
  let S := Finset.univ.image (fun m => route R T p (v m))
  fun m => normalize p S (route R T p (v m))

/-- A `p`-route pattern `μ` of `z` routes **occurs** in `(R, T)`: it is the `p`-route pattern of
some `z`-tuple of elements. -/
def PatternOccurs (R : Structure σ V) (T : RootedForest V) (p : ℕ) {z : ℕ}
    (μ : Fin z → List (ℕ × ℕ)) : Prop :=
  ∃ v : Fin z → V, pattern R T p v = μ

/-- `w` are **realizing vertices** of `μ = (ϱ₁, …, ϱ_z)` (Depian et al., Definition 24, p.23):
`w_i` is the vertex identified by the `p`-route `ϱ_i`, that is, `rt(w_i) = ϱ_i`, for every `i`. -/
def IsRealizing (R : Structure σ V) (T : RootedForest V) (p : ℕ) {z : ℕ}
    (μ : Fin z → List (ℕ × ℕ)) (w : Fin z → V) : Prop :=
  ∀ m, route R T p (w m) = μ m

end Patterns

end SNPTreedepth


