-- Prove2me | Definitions.Def_MSKleene_SubstGlobal
-- name    : MSKleene_SubstGlobal
-- status  : Definition
-- author  : @Cosme
-- created : 2026-09-08T12:27:41.522644+00:00
-- url     : https://prove2.me/theorems/8576077a-1550-446c-85d2-ae367aeaf454
-- title:
--   Global substitution operator
-- statement:
--   The **global substitution operator** $(((x/L_x)_{x\in X_t})_{t\in S})^{\sharp\mathsf{p}}$ of Definition 3.20, used in Proposition 3.30.
--
--   An $S$-sorted map $\rho : X \to \mathbf{T}_\Sigma(X)^{\wp}$ is exactly a family of languages $(L_x)_x$, one per variable. `substGlobalHom ρ` is the induced homomorphism $\mathbf{T}_\Sigma(X) \to \mathbf{T}_\Sigma(X)^{\wp}$, and `substGlobalP ρ s K = ⋃_{P ∈ K} (substGlobalHom ρ)_s(P)` its completely additive extension.
-- source:
--   Gong, Ruiz Mora, Sanmartín Vich, Cosme Llópez, "A Kleene theorem for free many-sorted algebras", 2026

/-
The global substitution operator `(((x/L_x)_{x∈X_t})_{t∈S})^{♯ᵖ}` of
Definition 3.20, used in Proposition 3.30 (`PRecSubs`).

An `S`-sorted map `ρ : X → T_Σ(X)^℘` is exactly a family of languages
`(L_x)_{x}` , one per variable. `substGlobalHom ρ` is the induced homomorphism
`T_Σ(X) → T_Σ(X)^℘`, and `substGlobalP ρ s` its completely additive extension.
-/
import Definitions.Def_MSKleene_Term
import Definitions.Def_MSKleene_Power
import Mathlib.Data.Set.Lattice

namespace MSKleene

universe u

variable {S : Type u} {sig : Signature S} {X : SSet S}

/-- The homomorphism `(((x/L_x))_{x})^{♯} : T_Σ(X) → T_Σ(X)^℘` induced by a
family of languages `ρ` indexed by the variables (Definition 3.20). -/
noncomputable def substGlobalHom
    (ρ : SMap X (powerAlgebra (freeAlgebra sig X)).carrier) :
    Hom (freeAlgebra sig X) (powerAlgebra (freeAlgebra sig X)) :=
  evalHom (powerAlgebra (freeAlgebra sig X)) ρ

/-- Its completely additive extension
`(((x/L_x))_{x})^{♯ᵖ}_s (K) = ⋃_{P ∈ K} (((x/L_x))_{x})^{♯}_s (P)`. -/
noncomputable def substGlobalP
    (ρ : SMap X (powerAlgebra (freeAlgebra sig X)).carrier) (s : S)
    (K : Set (Term sig X s)) : Set (Term sig X s) :=
  ⋃ P ∈ K, (substGlobalHom ρ).toFun s P

end MSKleene


