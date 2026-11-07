-- Prove2me | Definitions.Def_MinrankTW_RelTriple
-- name    : MinrankTW_RelTriple
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T12:32:53.937519+00:00
-- url     : https://prove2.me/theorems/e1260e65-b5b6-4194-a5b3-fcafe7239428
-- title:
--   Triple $(D,L,\beta)$ of a linear relation
-- statement:
--   A linear relation $R\le\mathbb F_q^a\oplus\mathbb F_q^c$ is represented by the triple
--   $$
--   D=\mathrm{dom}\,R,\qquad L=\{\lambda\in\mathbb F_q^{1\times c} : \lambda y=0 \text{ for every } y\in R(0)\},\qquad \beta(x,\lambda)=\lambda y\ \ ((x,y)\in R,\ \lambda\in L),
--   $$
--   with $\beta$ a bilinear form on $D\times L$. Conversely a triple $(D,L,\beta)$ — a subspace $D\le\mathbb F_q^a$, a subspace $L$ of row vectors and a bilinear form $\beta$ on $D\times L$ — defines
--   $$
--   R=\{(x,y) : x\in D,\ \lambda y=\beta(x,\lambda)\ \text{for all}\ \lambda\in L\}.
--   $$
--   "$T$ represents $R$" means that $T$ is the triple (16) of $R$.
--
--   **Formalization Note** Row vectors are functions on the row index set acting on $y$ by the dot product. $\beta$ is defined on $D\times L$ only.
-- source:
--   Perles–Weinstein, Efficient Algorithms for Minrank and Index Coding for Low-Treewidth Graphs, STOC 2027 submission (manuscript sha256 32a91384…), Section 4.1, p.12, Eqs. (16)–(17)

import Mathlib
import Definitions.Def_MinrankTW_LinRel

namespace MinrankTW

open Matrix

/-!
# Linear measurements: the triple `(D, L, β)` of a linear relation

Perles–Weinstein, *Efficient Algorithms for Minrank and Index Coding for Low-Treewidth Graphs*, STOC 2027 submission manuscript (sha256 32a91384…c57991), §4.1, p.12, Eq. (16): a linear relation `R ≤ F^a ⊕ F^c` is represented by
`D = dom R`, `L = {λ ∈ F^{1×c} : λy = 0 for every y ∈ R(0)}` and `β(x, λ) = λy` for
`(x, y) ∈ R`, `λ ∈ L`, a bilinear form on `D × L`; Eq. (17): conversely
`R = {(x, y) : x ∈ D, λy = β(x, λ) for all λ ∈ L}`.

**Formalization Note** Row vectors `λ ∈ F^{1×c}` are functions `γ → F` acting on `y` by
`dotProduct` (`λ ⬝ᵥ y`). A triple is a structure with a subspace `D` of `F^α`, a subspace
`L` of row vectors and a bilinear form `β : D →ₗ L →ₗ F` defined on `D × L` only.
`Represents R T` says that `T` is the triple (16) of `R`.
-/

variable {F : Type*} [Field F] {α γ : Type*} [Fintype γ]

/-- `L = {λ : λy = 0 for every y ∈ R(0)}`, the row vectors vanishing on `R(0)` (Eq. (16)). -/
def relAnn (R : Submodule F ((α → F) × (γ → F))) : Submodule F (γ → F) where
  carrier := {l | ∀ y ∈ relZero R, l ⬝ᵥ y = 0}
  zero_mem' := by intro y _; simp
  add_mem' := by
    intro a b ha hb y hy
    rw [add_dotProduct, ha y hy, hb y hy, add_zero]
  smul_mem' := by
    intro r a ha y hy
    rw [smul_dotProduct, ha y hy, smul_zero]

variable (F α γ) in
/-- A triple `(D, L, β)`: a subspace `D ≤ F^α`, a subspace `L` of row vectors in `F^{1×γ}`
and a bilinear form `β` on `D × L`. -/
structure RelTriple where
  D : Submodule F (α → F)
  L : Submodule F (γ → F)
  β : D →ₗ[F] L →ₗ[F] F

/-- The relation of a triple, Eq. (17): `{(x, y) : x ∈ D, λy = β(x, λ) for all λ ∈ L}`. -/
def tripleToRel (T : RelTriple F α γ) : Submodule F ((α → F) × (γ → F)) where
  carrier := {p | ∃ hx : p.1 ∈ T.D, ∀ l : T.L, (l : γ → F) ⬝ᵥ p.2 = T.β ⟨p.1, hx⟩ l}
  zero_mem' := by
    refine ⟨T.D.zero_mem, fun l => ?_⟩
    have h0 : (⟨(0 : (α → F) × (γ → F)).1, T.D.zero_mem⟩ : T.D) = 0 := rfl
    rw [h0, map_zero, LinearMap.zero_apply]
    simp
  add_mem' := by
    rintro ⟨x, y⟩ ⟨x', y'⟩ ⟨hx, h⟩ ⟨hx', h'⟩
    refine ⟨T.D.add_mem hx hx', fun l => ?_⟩
    have hs : (⟨((x, y) + (x', y')).1, T.D.add_mem hx hx'⟩ : T.D) = ⟨x, hx⟩ + ⟨x', hx'⟩ := rfl
    rw [hs, map_add, LinearMap.add_apply, Prod.snd_add, dotProduct_add, h l, h' l]
  smul_mem' := by
    rintro r ⟨x, y⟩ ⟨hx, h⟩
    refine ⟨T.D.smul_mem r hx, fun l => ?_⟩
    have hs : (⟨(r • (x, y)).1, T.D.smul_mem r hx⟩ : T.D) = r • ⟨x, hx⟩ := rfl
    rw [hs, map_smul, LinearMap.smul_apply, Prod.smul_snd, dotProduct_smul, h l]

/-- `Represents R T`: `T = (D, L, β)` is the triple (16) of `R`: `D = dom R`,
`L = {λ : λ = 0 on R(0)}` and `β(x, λ) = λy` whenever `(x, y) ∈ R`. -/
def Represents (R : Submodule F ((α → F) × (γ → F))) (T : RelTriple F α γ) : Prop :=
  T.D = relDom R ∧ T.L = relAnn R ∧
    ∀ (x : T.D) (l : T.L) (y : γ → F), ((x : α → F), y) ∈ R → T.β x l = (l : γ → F) ⬝ᵥ y

end MinrankTW


