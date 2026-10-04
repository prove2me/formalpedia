-- Prove2me | Definitions.Def_MSKleene_Term
-- name    : MSKleene_Term
-- status  : Definition
-- author  : @Cosme
-- created : 2026-09-08T12:26:48.859208+00:00
-- url     : https://prove2.me/theorems/c62a3a3a-6543-4adf-ba29-c25e3817beca
-- title:
--   The free many-sorted algebra $\mathbf{T}_\Sigma(X)$
-- statement:
--   The **free $\Sigma$-algebra** $\mathbf{T}_\Sigma(X)$ on an $S$-sorted set of variables $X$ (Definitions 3.1, 3.2), represented by the mutual inductive `Term` / `TermVec`: a term is a variable `var x` or an operation symbol applied to a vector of subterms of the matching arity, `app σ ts` (a constant is `app σ .nil`).
--
--   The file provides the algebra structure `freeAlgebra` (carrier `Term sig X`, operations `app`), the insertion of generators `eta` ($\eta^X$), the evaluation `Term.eval` of a term in an arbitrary $\Sigma$-algebra `A` under an assignment `ρ : X → A`, and the induced homomorphism `evalHom` with `evalHom_eta : evalHom A ρ ∘ η^X = ρ`. This is the existence half of the universal property of $\mathbf{T}_\Sigma(X)$ (Proposition 3.5).
--
--   **Formalization Note** `TermVec sig X w` is a heterogeneous list holding one subterm of sort `w[i]` per argument position; `ofArgs` / `toArgs` convert between it and the nested-product `Args`.
-- source:
--   Gong, Ruiz Mora, Sanmartín Vich, Cosme Llópez, "A Kleene theorem for free many-sorted algebras", 2026, https://arxiv.org/abs/1808.08217 (predecessor CVCL20)

/-
The free many-sorted `Σ`-algebra `T_Σ(X)` (Definitions 3.1, 3.2) as an
inductive family of terms, together with:
  * its `Algebra` structure (`freeAlgebra`);
  * the insertion of generators `η^X`;
  * evaluation of a term into any `Σ`-algebra under an assignment, and the
    induced homomorphism (the existence half of the universal property, Prop. 3.5).

Terms are represented by the mutual inductive `Term` / `TermVec`, the standard
encoding of many-sorted terms: `TermVec sig X w` is a heterogeneous list holding
one subterm of sort `w[i]` per argument position.
-/
import Definitions.Def_MSKleene_Core

namespace MSKleene

universe u

variable {S : Type u}

-- Many-sorted terms over signature `sig` with variables in `X`:
-- `var` injects a variable; `app` applies an operation symbol to a vector of
-- subterms of the matching arity (a constant is `app σ .nil`).
-- `TermVec sig X w` is a heterogeneous list holding one subterm of sort `w[i]`
-- per argument position.
mutual
inductive Term (sig : Signature S) (X : SSet S) : S → Type u where
  | var {s : S} : X s → Term sig X s
  | app {w : List S} {s : S} : sig w s → TermVec sig X w → Term sig X s
inductive TermVec (sig : Signature S) (X : SSet S) : List S → Type u where
  | nil : TermVec sig X []
  | cons {s : S} {w : List S} : Term sig X s → TermVec sig X w → TermVec sig X (s :: w)
end

/-- Convert an `Args` tuple of terms into a `TermVec`. -/
def TermVec.ofArgs {sig : Signature S} {X : SSet S} :
    {w : List S} → Args (Term sig X) w → TermVec sig X w
  | [], _ => .nil
  | _ :: _, (t, rest) => .cons t (TermVec.ofArgs rest)

/-- Convert a `TermVec` back into an `Args` tuple of terms. -/
def TermVec.toArgs {sig : Signature S} {X : SSet S} :
    {w : List S} → TermVec sig X w → Args (Term sig X) w
  | [], _ => PUnit.unit
  | _ :: _, .cons t rest => (t, TermVec.toArgs rest)

/-- The free `Σ`-algebra `T_Σ(X)`: carrier `Term sig X`, operations `app`
(Definition 3.2). -/
def freeAlgebra (sig : Signature S) (X : SSet S) : Algebra sig where
  carrier := Term sig X
  op := fun σ args => Term.app σ (TermVec.ofArgs args)

/-- Insertion of the generators, `η^X : X → T_Σ(X)` (Proposition 3.5). -/
def eta (sig : Signature S) (X : SSet S) : SMap X (freeAlgebra sig X).carrier :=
  fun _ x => Term.var x

-- Evaluate a term in the algebra `A` under the assignment `ρ : X → A`.
-- Together with `evalArgs` this is the unique-extension map of Proposition 3.5.
mutual
def Term.eval {sig : Signature S} {X : SSet S} (A : Algebra sig)
    (ρ : SMap X A.carrier) : {s : S} → Term sig X s → A.carrier s
  | _, .var x => ρ _ x
  | _, .app σ ts => A.op σ (TermVec.evalArgs A ρ ts)
def TermVec.evalArgs {sig : Signature S} {X : SSet S} (A : Algebra sig)
    (ρ : SMap X A.carrier) : {w : List S} → TermVec sig X w → Args A.carrier w
  | [], _ => PUnit.unit
  | _ :: _, .cons t ts => (Term.eval A ρ t, TermVec.evalArgs A ρ ts)
end

theorem TermVec.evalArgs_ofArgs {sig : Signature S} {X : SSet S} (A : Algebra sig)
    (ρ : SMap X A.carrier) :
    ∀ {w : List S} (args : Args (Term sig X) w),
      TermVec.evalArgs A ρ (TermVec.ofArgs args)
        = Args.map (fun s (t : Term sig X s) => Term.eval A ρ t) args
  | [], _ => rfl
  | _ :: _, (t, rest) => congrArg (Prod.mk (Term.eval A ρ t))
      (TermVec.evalArgs_ofArgs A ρ rest)

/-- The homomorphism `ρ^♯ : T_Σ(X) → A` induced by an assignment `ρ`
(the existence half of Proposition 3.5). -/
def evalHom {sig : Signature S} {X : SSet S} (A : Algebra sig)
    (ρ : SMap X A.carrier) : Hom (freeAlgebra sig X) A where
  toFun := fun _ t => Term.eval A ρ t
  map_op := by
    intro w s σ args
    show Term.eval A ρ (Term.app σ (TermVec.ofArgs args)) = _
    show A.op σ (TermVec.evalArgs A ρ (TermVec.ofArgs args)) = _
    exact congrArg (A.op σ) (TermVec.evalArgs_ofArgs A ρ args)

/-- `ρ^♯ ∘ η^X = ρ`: the induced homomorphism restricts to `ρ` on generators. -/
theorem evalHom_eta {sig : Signature S} {X : SSet S} (A : Algebra sig)
    (ρ : SMap X A.carrier) (s : S) (x : X s) :
    (evalHom A ρ).toFun s (eta sig X s x) = ρ s x := rfl

end MSKleene


