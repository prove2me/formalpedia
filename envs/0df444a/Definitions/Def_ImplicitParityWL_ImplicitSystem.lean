-- Prove2me | Definitions.Def_ImplicitParityWL_ImplicitSystem
-- name    : ImplicitParityWL_ImplicitSystem
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T02:12:31.119202+00:00
-- url     : https://prove2.me/theorems/aad99f10-d1e2-430d-8e8a-b8202a7f1691
-- title:
--   Equation schemas and implicit parity systems
-- statement:
--   A **ternary equation schema** is a tuple $e=(u,v,w,\mathfrak c_e,\sigma,\tau,\pi)$ of three distinct locations, a coordinate domain $\mathfrak c_e\subseteq\mathfrak c$ and block-induced permutations with $\sigma(\mathfrak c_e)\subseteq\mathfrak c_u$, $\tau(\mathfrak c_e)\subseteq\mathfrak c_v$, $\pi(\mathfrak c_e)\subseteq\mathfrak c_w$. For each allowed address $a$, those with $\mathrm{supp}(a)\subseteq\mathfrak c_e$, it gives the equation
--   $$
--   X_{u,\sigma a}+X_{v,\tau a}+X_{w,\pi a}=0.
--   $$
--   A **binary** schema $(u,v,\mathfrak c_e,\sigma,\tau)$ gives $X_{u,\sigma a}+X_{v,\tau a}=0$.
--
--   An **implicit parity system** $\mathcal I$ consists of a finite set $W$ of locations, coordinate domains $\mathfrak c_v\subseteq\mathfrak c$, a finite set $\mathcal E$ of schemas whose location sets pairwise intersect in at most one element, and an initialization $\iota:W\to\{0,1,\star\}$. It defines a parity system with the variables $X_{v,a}$ for $\mathrm{supp}(a)\subseteq\mathfrak c_v$, the equations above, and the initial facts $(X_{v,a},\iota(v))$ for $\iota(v)\in\{0,1\}$.
--
--   **Formalization Note** The standing $k\ge3$, $\ell\ge1$ are binders of each theorem. A binary schema is `third = none`. The schema family is indexed by a type $E$; the sharing condition makes different indices give different schemas. The variable type of the parity system is all of $W\times\Sigma$, and the pairs with $\mathrm{supp}(a)\not\subseteq\mathfrak c_v$ occur in no equation and no initial fact, so they change neither $K_r$ on the variables of the page nor $\tau$.
-- source:
--   Curticapean, Liu, Neuen, Seppelt, Lower Bounds for the Weisfeiler–Leman Algorithm via Implicit Parity Systems (STOC 2027 submission, manuscript of November 3, 2026, sha256 6604ccc9…), Definitions 4.7, 4.9, 4.10, pp.20–21

import Mathlib
import Definitions.Def_ImplicitParityWL_ParitySystem
import Definitions.Def_ImplicitParityWL_BlockPerm

namespace ImplicitParityWL

/-- An **equation schema** on the locations `W` (Curticapean, Liu, Neuen, Seppelt, *Lower Bounds for
the Weisfeiler–Leman Algorithm via Implicit Parity Systems*, manuscript of November 3, 2026,
Definition 4.7, p.20): the ternary tuple `(u, v, w, 𝔠_e, σ, τ, π)` or the binary tuple
`(u, v, 𝔠_e, σ, τ)`.

**Formalization Note** `third = some (w, π)` is the ternary case and `third = none` the binary one.
The conditions on the tuple are `WellFormed`. -/
structure EquationSchema (k ℓ : ℕ) (W : Type*) where
  /-- The first location. -/
  u : W
  /-- The second location. -/
  v : W
  /-- The coordinate domain `𝔠_e`. -/
  dom : Finset (Coord k ℓ)
  /-- The permutation at `u`. -/
  σ : BlockPerm k ℓ
  /-- The permutation at `v`. -/
  τ : BlockPerm k ℓ
  /-- The third location and its permutation, for a ternary schema. -/
  third : Option (W × BlockPerm k ℓ)

namespace EquationSchema

variable {k ℓ : ℕ} {W : Type*}

/-- The argument locations of a schema: its hyperedge in the schema hypergraph (Definition 4.10,
p.21). -/
def locs (e : EquationSchema k ℓ W) : Set W :=
  {x | x = e.u ∨ x = e.v ∨ ∃ π, e.third = some (x, π)}

/-- The conditions of Definition 4.7, p.20: the locations are distinct, and
`σ(𝔠_e) ⊆ 𝔠_u`, `τ(𝔠_e) ⊆ 𝔠_v`, `π(𝔠_e) ⊆ 𝔠_w`. -/
structure WellFormed (e : EquationSchema k ℓ W) (doms : W → Finset (Coord k ℓ)) : Prop where
  u_ne_v : e.u ≠ e.v
  σ_mem : ∀ c ∈ e.dom, e.σ c ∈ doms e.u
  τ_mem : ∀ c ∈ e.dom, e.τ c ∈ doms e.v
  third_ne : ∀ w π, e.third = some (w, π) → w ≠ e.u ∧ w ≠ e.v
  π_mem : ∀ w π, e.third = some (w, π) → ∀ c ∈ e.dom, π c ∈ doms w

open scoped Classical in
/-- The equation of the schema at the address `a`, as the set of its variables `(location, address)`
(Definition 4.7, p.20): `X_{u,σa} + X_{v,τa} + X_{w,πa} = 0`, or `X_{u,σa} + X_{v,τa} = 0` for a binary
schema. -/
noncomputable def equation (e : EquationSchema k ℓ W) (a : Address k ℓ) : Finset (W × Address k ℓ) :=
  match e.third with
  | none => {(e.u, e.σ.act a), (e.v, e.τ.act a)}
  | some (w, π) => {(e.u, e.σ.act a), (e.v, e.τ.act a), (w, π.act a)}

theorem equation_card {e : EquationSchema k ℓ W} {doms : W → Finset (Coord k ℓ)}
    (he : e.WellFormed doms) (a : Address k ℓ) :
    (e.equation a).card = 2 ∨ (e.equation a).card = 3 := by
  classical
  unfold equation
  rcases ht : e.third with _ | ⟨w, π⟩
  · left
    exact Finset.card_pair (fun h => he.u_ne_v (congrArg Prod.fst h))
  · right
    have h := he.third_ne w π ht
    refine Finset.card_eq_three.mpr ⟨_, _, _, ?_, ?_, ?_, rfl⟩
    · exact fun h' => he.u_ne_v (congrArg Prod.fst h')
    · exact fun h' => h.1 (congrArg Prod.fst h').symm
    · exact fun h' => h.2 (congrArg Prod.fst h').symm

end EquationSchema

/-- An **implicit parity system** with coordinate set `𝔠 = [k] × 𝔽₂^ℓ`, locations `W` and schemas
indexed by `E` (Definition 4.9, p.20).

**Formalization Note** `W` and `E` are types carrying `[Fintype]` binders where used, and the
standing `k ≥ 3`, `ℓ ≥ 1` of clause (ii) are binders of each theorem. Clause (iii) is `share`: two
schemas with different indices have at most one location in common, which also makes the schemas of
different indices different. An initialization `ι(v) = ⋆` is `init v = none`. -/
structure ImplicitSystem (k ℓ : ℕ) (W E : Type*) where
  /-- The coordinate domains `𝔠_v`. -/
  dom : W → Finset (Coord k ℓ)
  /-- The equation schemas. -/
  schema : E → EquationSchema k ℓ W
  /-- Every schema satisfies Definition 4.7. -/
  wf : ∀ e, (schema e).WellFormed dom
  /-- Clause (iii) of Definition 4.9. -/
  share : ∀ e f, e ≠ f → ((schema e).locs ∩ (schema f).locs).Subsingleton
  /-- The initialization `ι : W → {0, 1, ⋆}`. -/
  init : W → Option (ZMod 2)

namespace ImplicitSystem

variable {k ℓ : ℕ} {W E : Type*}

/-- The parity system of an implicit system (Definitions 4.7 and 4.9, pp.20–21). The equations are
those of the schemas at their allowed addresses `supp(a) ⊆ 𝔠_e`, and the initial facts are
`(X_{v,a}, ι(v))` for `ι(v) ∈ {0, 1}` and `supp(a) ⊆ 𝔠_v`.

**Formalization Note** The variable type is all of `W × Address k ℓ`. The page's variables are the
pairs with `supp(a) ⊆ 𝔠_v`; the other pairs occur in no equation and in no initial fact (by
`WellFormed`), so they never acquire a fact and change neither `K_r` on the page's variables nor `τ`. -/
noncomputable def toParity (I : ImplicitSystem k ℓ W E) : ParitySystem (W × Address k ℓ) where
  eqs := {h | ∃ (e : E) (a : Address k ℓ), a.supp ⊆ (I.schema e).dom ∧ h = (I.schema e).equation a}
  eqs_card := by
    rintro h ⟨e, a, -, rfl⟩
    exact EquationSchema.equation_card (I.wf e) a
  init := {f | I.init f.1.1 = some f.2 ∧ f.1.2.supp ⊆ I.dom f.1.1}

end ImplicitSystem

end ImplicitParityWL


