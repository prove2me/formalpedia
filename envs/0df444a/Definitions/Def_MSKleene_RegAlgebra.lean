-- Prove2me | Definitions.Def_MSKleene_RegAlgebra
-- name    : MSKleene_RegAlgebra
-- status  : Definition
-- author  : @Cosme
-- created : 2026-09-08T12:28:25.304737+00:00
-- url     : https://prove2.me/theorems/f2ef8cc0-754e-47a0-8395-0fd9de65bafa
-- title:
--   $\mathbf{T}_\Sigma(Z)^{\wp}$ as a regular algebra; interpretation
-- statement:
--   The **$\mathrm{Reg}(S,\Sigma,Z)$-algebra structure on $\mathbf{T}_\Sigma(Z)^{\wp}$** (Proposition 4.3) and the **interpretation homomorphism** $\{\cdot\}^{Z\sharp}$ (Remark 4.5).
--
--   On the carrier $s \mapsto \mathrm{Set}(\mathrm{T}_\Sigma(Z)_s)$, `regPowerAlgebra` interprets the extra symbols as
--   $$\varnothing_s \mapsto \varnothing, \quad +_s \mapsto \cup, \quad (\cdot)^{\star z} \mapsto z\text{-iteration}, \quad \langle z/\cdot\rangle^{\sharp\mathsf{p}}_s(\cdot) \mapsto z\text{-substitution},$$
--   while every $\sigma \in \Sigma$ acts as $\sigma^{\mathbf{T}_\Sigma(Z)^{\wp}}$. `interp` is the homomorphism from the free regular-expression algebra induced by the assignment `z ↦ {z}`, and `interpExpr sig Z s R` is the language $\{R\}^{Z\sharp}_s \subseteq \mathrm{T}_\Sigma(Z)_s$ denoted by a regular expression `R` of type `s`.
-- source:
--   Gong, Ruiz Mora, Sanmartín Vich, Cosme Llópez, "A Kleene theorem for free many-sorted algebras", 2026, https://arxiv.org/abs/1808.08217 (predecessor CVCL20)

/-
The `Reg(S,Σ,Z)`-algebra structure on the power algebra `T_Σ(Z)^℘`
(Proposition 4.3), and the interpretation homomorphism `{·}^{Z♯}` sending a
regular expression to the language it denotes (Remark 4.5).

Interpretation of the extra symbols on `T_Σ(Z)^℘`:
  `∅_s ↦ ∅`,  `+_s ↦ (∪)`,  `(·)^{⋆z} ↦ z`-iteration,
  `⟨z/·⟩^♯ᵖ_s(·) ↦ z`-substitution;  every `σ ∈ Σ` acts as `σ^{T_Σ(Z)^℘}`.
-/
import Definitions.Def_MSKleene_RegSig
import Definitions.Def_MSKleene_Power
import Definitions.Def_MSKleene_Subst
import Definitions.Def_MSKleene_Iteration

namespace MSKleene

universe u

variable {S : Type u} {sig : Signature S}

/-- `T_Σ(Z)^℘` as a `Reg(S,Σ,Z)`-algebra (Proposition 4.3). -/
noncomputable def regPowerAlgebra (sig : Signature S) (Z : SSet S) :
    Algebra (regSig sig Z) where
  carrier := fun s => Set (Term sig Z s)
  op := fun {w s} sym args =>
    match w, s, sym, args with
    | _, _, .base σ, args => powerOp (freeAlgebra sig Z) σ args
    | _, s, .empty _, _ => (∅ : Set (Term sig Z s))
    | _, _, .iter _ z, args => iterate z args.1
    | _, _, .plus _, args => args.1 ∪ args.2.1
    | _, _, .subst _ s z, args => substP z args.1 s args.2.1

/-- The generator assignment `{·}^Z : Z → T_Σ(Z)^℘`, `z ↦ {z}` (Remark 4.5). -/
noncomputable def regGenAssign (sig : Signature S) (Z : SSet S) :
    SMap Z (regPowerAlgebra sig Z).carrier :=
  fun s z => ({Term.var z} : Set (Term sig Z s))

/-- The interpretation homomorphism `{·}^{Z♯} : T_{Reg(S,Σ,Z)}(Z) → T_Σ(Z)^℘`
(Remark 4.5). -/
noncomputable def interp (sig : Signature S) (Z : SSet S) :
    Hom (freeAlgebra (regSig sig Z) Z) (regPowerAlgebra sig Z) :=
  evalHom (regPowerAlgebra sig Z) (regGenAssign sig Z)

/-- `{R}^{Z♯}_s` — the language of `T_Σ(Z)_s` denoted by the regular expression
`R` of type `s`. -/
noncomputable def interpExpr (sig : Signature S) (Z : SSet S) (s : S)
    (R : RegExpr sig Z s) : Set (Term sig Z s) :=
  (interp sig Z).toFun s R

end MSKleene


