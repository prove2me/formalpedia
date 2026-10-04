-- Prove2me | Definitions.Def_MSKleene_Subst
-- name    : MSKleene_Subst
-- status  : Definition
-- author  : @Cosme
-- created : 2026-09-08T12:27:27.607078+00:00
-- url     : https://prove2.me/theorems/782c6692-54b2-476c-88fd-8253d74dfd01
-- title:
--   The $z$-substitution operators
-- statement:
--   The **$z$-substitution operators** on languages of the free many-sorted algebra (Definition 3.20).
--
--   Given a sort `v`, a variable `z ∈ X_v`, and a language `L ⊆ T_Σ(X)_v`:
--
--   1. `substAssign z L` is the $S$-sorted map $\langle z/L\rangle : X \to \mathbf{T}_\Sigma(X)^{\wp}$ sending `z ↦ L` and every other variable `y ↦ {y}`;
--   2. `substHom z L` is the induced homomorphism $\langle z/L\rangle^{\sharp} : \mathbf{T}_\Sigma(X) \to \mathbf{T}_\Sigma(X)^{\wp}$;
--   3. `substP z L s K` is its completely additive extension $\langle z/L\rangle^{\sharp\mathsf{p}}_s(K) = \bigcup_{P \in K} \langle z/L\rangle^{\sharp}_s(P)$.
--
--   **Formalization Note** `substAssign` uses classical decidability for the sort- and variable-equality tests, so the definitions are `noncomputable`; this is immaterial to the mathematics.
-- source:
--   Gong, Ruiz Mora, Sanmartín Vich, Cosme Llópez, "A Kleene theorem for free many-sorted algebras", 2026, https://arxiv.org/abs/1808.08217 (predecessor CVCL20)

/-
The `z`-substitution operators on languages of the free many-sorted algebra
(Definition 3.20).

Given a sort `v`, a variable `z ∈ X_v`, and a language `L ⊆ T_Σ(X)_v`:
  * `substAssign z L` is the `S`-sorted map `X → T_Σ(X)^℘` sending `z ↦ L` and
    every other variable `y ↦ {y}`;
  * `substHom z L = (substAssign z L)^♯` is the induced homomorphism
    `T_Σ(X) → T_Σ(X)^℘`  (written `⟨z/L⟩^♯` in the paper);
  * `substP z L s K` is its completely additive extension
    `⟨z/L⟩^♯ᵖ_s (K) = ⋃_{P ∈ K} ⟨z/L⟩^♯_s(P)`.
-/
import Definitions.Def_MSKleene_Term
import Definitions.Def_MSKleene_Power
import Mathlib.Data.Set.Lattice

namespace MSKleene

universe u

variable {S : Type u} {sig : Signature S} {X : SSet S}

open scoped Classical in
/-- The substitution assignment `⟨z/L⟩ : X → T_Σ(X)^℘` (Definition 3.20):
`z ↦ L`, and `y ↦ {y}` for every other variable. -/
noncomputable def substAssign {v : S} (z : X v) (L : Set (Term sig X v)) :
    SMap X (powerAlgebra (freeAlgebra sig X)).carrier := fun t y =>
  show Set (Term sig X t) from
  if h : t = v then
    (by subst h; exact if y = z then L else {(Term.var y : Term sig X t)})
  else ({(Term.var y : Term sig X t)} : Set (Term sig X t))

/-- The homomorphism `⟨z/L⟩^♯ : T_Σ(X) → T_Σ(X)^℘` induced by `substAssign`
(Definition 3.20). -/
noncomputable def substHom {v : S} (z : X v) (L : Set (Term sig X v)) :
    Hom (freeAlgebra sig X) (powerAlgebra (freeAlgebra sig X)) :=
  evalHom (powerAlgebra (freeAlgebra sig X)) (substAssign z L)

/-- The completely additive extension `⟨z/L⟩^♯ᵖ_s : T_Σ(X)^℘_s → T_Σ(X)^℘_s`,
`K ↦ ⋃_{P ∈ K} ⟨z/L⟩^♯_s(P)` (Definition 3.20). -/
noncomputable def substP {v : S} (z : X v) (L : Set (Term sig X v)) (s : S)
    (K : Set (Term sig X s)) : Set (Term sig X s) :=
  ⋃ P ∈ K, (substHom z L).toFun s P

end MSKleene


