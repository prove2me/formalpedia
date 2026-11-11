-- Prove2me | Definitions.Def_WaitFreeTasks_Characterization_Task
-- name    : WaitFreeTasks_Characterization_Task
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-10T20:28:24.641034+00:00
-- url     : https://prove2.me/theorems/03413281-5f04-425b-a2bb-1f33c3c40030
-- title:
--   Finite chromatic tasks and monotone pure carriers
-- statement:
--   For $n$ processes, a chromatic task consists of finite input and output complexes $I,O$, vertex identifiers in $\operatorname{Fin}(n)$ injective on each face, and a carrier $\Delta$. For every input face $\sigma$, its allowed outputs form a subcomplex of $O$, monotonically in $\sigma$, with only colors of $\sigma$. Every allowed face extends to an allowed face of the same cardinality as $\sigma$, and such a face exists. Thus
--
--   $$\Delta(\sigma)\text{ is nonempty and pure of dimension }\dim\sigma,\qquad\operatorname{id}(\Delta(\sigma))=\operatorname{id}(\sigma).$$
--
--   The input and output complexes need not be globally pure. A map is carried if its image of every original simplex lies in the allowed output realization. Identifier $i$ of the source corresponds to $i-1$ in Lean. This shared task definition imposes only the source's standing carrier conditions.
-- source:
--   Hagit Attiya, Ami Paz, STOC 2027 submission #828 (October 2026), pp. 7–8 (PDF pp. 9–10), §§2.2–2.3

import Definitions.Def_WaitFreeTasks_Characterization_Complexes

set_option autoImplicit false

open Classical

namespace WaitFreeTasks.Characterization

/-! # Chromatic tasks (§§2.2–2.3, printed pp. 7–8, PDF pp. 9–10)

Process identifiers `[n] = {1, …, n}` are encoded by `Fin n` (identifier `i` ↦ `i - 1`).
A chromatic vertex is a pair (identifier, value); here a vertex is an element of an arbitrary
type, and its identifier (colour) is given by a colouring function. A complex with vertices
`(i, x_i)` is the special case `V = [n] × X`, colouring `Prod.fst`, and every chromatic complex
is of this form up to renaming its vertices `v ↦ (id v, v)`. -/

/-- A **chromatic task** `(I, O, Δ)` for `n` processes (§2.3, printed p. 7, lines 306–308, with
the standing assumptions on carrier maps of §2.2, printed p. 7, lines 291–297):
* `I`, `O` are finite complexes whose vertices are coloured by process identifiers (`idI`,
  `idO`), each face having pairwise distinct colours (chromatic). With colours in `Fin n` this
  forces dimension at most `n - 1`.
* `Δ` assigns to every input face `σ ∈ I` a subcomplex `Δ(σ)` of `O` (a family of faces of `O`,
  closed under nonempty subsets); it is monotone; it is chromatic (the colours of every face of
  `Δ(σ)` are colours of `σ`); and `Δ(σ)` is pure of dimension `dim σ` (every face of `Δ(σ)` lies
  in a face of `Δ(σ)` with `|σ|` vertices, and such a face exists).
No global purity, connectivity or condition `Δ(σ ∩ τ) = Δ(σ) ∩ Δ(τ)` is assumed. The value of
`Δ` on sets that are not faces of `I` is irrelevant. -/
structure Task (n : ℕ) (VI VO : Type) where
  I : Cx VI
  O : Cx VO
  idI : VI → Fin n
  idO : VO → Fin n
  chromI : ∀ σ ∈ I.faces, Set.InjOn idI (σ : Set VI)
  chromO : ∀ τ ∈ O.faces, Set.InjOn idO (τ : Set VO)
  Δ : Finset VI → Finset (Finset VO)
  sub : ∀ σ ∈ I.faces, Δ σ ⊆ O.faces
  closed : ∀ σ ∈ I.faces, ∀ τ ∈ Δ σ, ∀ τ' : Finset VO, τ'.Nonempty → τ' ⊆ τ → τ' ∈ Δ σ
  mono : ∀ σ ∈ I.faces, ∀ σ' ∈ I.faces, σ' ⊆ σ → Δ σ' ⊆ Δ σ
  colors : ∀ σ ∈ I.faces, ∀ τ ∈ Δ σ, τ.image idO ⊆ σ.image idI
  pure : ∀ σ ∈ I.faces, ∀ τ ∈ Δ σ, ∃ τ' ∈ Δ σ, τ ⊆ τ' ∧ τ'.card = σ.card
  dim_eq : ∀ σ ∈ I.faces, ∃ τ ∈ Δ σ, τ.card = σ.card

/-- A map `f : |I| → |O|` is **carried by** `Δ` (§2.2, printed p. 7, line 301,
[HKR13, p. 52]): `f(|σ|) ⊆ |Δ(σ)|` for every input face `σ ∈ I`. -/
def IsCarried {n : ℕ} {VI VO : Type} (T : Task n VI VO) (f : (VI → ℝ) → (VO → ℝ)) : Prop :=
  ∀ σ ∈ T.I.faces, ∀ x ∈ face σ, f x ∈ realOf (T.Δ σ)

end WaitFreeTasks.Characterization


