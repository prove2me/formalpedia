-- Prove2me | Definitions.Def_RobustBoolPCSP_Simulation
-- name    : RobustBoolPCSP_Simulation
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T12:24:48.405534+00:00
-- url     : https://prove2.me/theorems/1a3bd73c-53d5-4de3-93ae-1e3678897b4d
-- title:
--   Simulation by lists of signed constraints, the replacement operation, global negation
-- statement:
--   Let $\Gamma$ be a Boolean template and $(P^*,Q^*)$ a relation pair of arity $\ell$. A finite list of signed $\Gamma$-constraints on the literals $y_1,\dots,y_\ell$ (variables $y_i$, their negations and the constants) **simulates** $(P^*,Q^*)$ if every tuple of $P^*$ strongly satisfies every constraint of the list, and every tuple that weakly satisfies all constraints of the list lies in $Q^*$. $\Gamma$ simulates $(P^*,Q^*)$ if some such list exists.
--
--   Given a signed instance of a template $\Gamma'$ containing $(P^*,Q^*)$ as its pair $j^\star$, the **replacement** replaces each $(P^*,Q^*)$-constraint by the list, with the constraint's literals substituted for $y_1,\dots,y_\ell$, and keeps every other constraint and all variables; the result is a signed instance of the union template $\Gamma\cup\Gamma'$.
--
--   The **global negation** of a pair $(P,Q)$ is $(-P,-Q)$, the coordinatewise complement of both relations.
--
--   **Formalization Note** Substituting a literal into a negated position negates it ($x\leftrightarrow\neg x$, $0\leftrightarrow1$). Global negation reuses the published `SymBoolPCSP.CFixing.negRel`.
-- source:
--   Cai, Jiang, Zou, On Robust Promise CSPs: A Boolean Dichotomy, Sharp Quantitative Bounds, and Soft-Equality Transfer, STOC 2027 submission (manuscript of 2026-11-03, sha256 fd1be0d0624155f00f7a115874a4dadfb7ebb2d4187530c7d0bdd4e1406e8732), §4.4, Lemma 4.19, p.26 (simulation, replacement); p.25 (global negation); Lemma 4.20, p.26

import Mathlib
import Definitions.Def_RobustBoolPCSP_Signed

set_option autoImplicit false

namespace RobustBoolPCSP

/-- A fixed finite list of signed `Γ`-constraints on the literals `y_1, …, y_ℓ` **simulates** the
relation pair `(P*, Q*)` of arity `ℓ` (Lemma 4.19, p.26): "every tuple of P∗ strongly satisfies
every constraint of the list, and every tuple that weakly satisfies all constraints of the list lies
in Q∗." Literals of the list range over `y_1, …, y_ℓ` (`Fin ℓ`), their negations and the constants. -/
def IsSimulatingList {ι : Type} (Γ : Template ι Bool Bool) {ℓ : ℕ}
    (Pstar Qstar : Set (Fin ℓ → Bool)) (L : List (Σ j : ι, Fin (Γ.r j) → Literal ℓ)) : Prop :=
  (∀ y ∈ Pstar, ∀ c ∈ L, evalLits y c.2 ∈ Γ.P c.1) ∧
    (∀ y : Fin ℓ → Bool, (∀ c ∈ L, evalLits y c.2 ∈ Γ.Q c.1) → y ∈ Qstar)

/-- `Γ` **simulates** `(P*, Q*)` "in the sense of Lemma 4.19" (Lemma 4.20, p.26): some fixed finite
list of signed `Γ`-constraints on `y_1, …, y_ℓ` simulates it. -/
def Simulates {ι : Type} (Γ : Template ι Bool Bool) {ℓ : ℕ} (Pstar Qstar : Set (Fin ℓ → Bool)) :
    Prop :=
  ∃ L : List (Σ j : ι, Fin (Γ.r j) → Literal ℓ), IsSimulatingList Γ Pstar Qstar L

/-- The template with the pairs of `Γ` (index `inl`) and of `Γ'` (index `inr`). -/
def Template.union {ι ι' : Type} (Γ : Template ι Bool Bool) (Γ' : Template ι' Bool Bool) :
    Template (ι ⊕ ι') Bool Bool where
  r := Sum.elim Γ.r Γ'.r
  P := fun j => match j with
    | Sum.inl j => Γ.P j
    | Sum.inr j => Γ'.P j
  Q := fun j => match j with
    | Sum.inl j => Γ.Q j
    | Sum.inr j => Γ'.Q j

/-- The replacement of Lemma 4.19 (p.26): in a signed instance `I` of `Γ'`, each constraint on the
pair `j★` is replaced by the list `L` of `Γ`-constraints, with the constraint's literals substituted
for `y_1, …, y_ℓ`; every other constraint is kept. The variables are unchanged ("no auxiliary
variables are introduced", p.24). The result is a signed instance of `Γ ∪ Γ'`. -/
def replaceInst {ι ι' : Type} [DecidableEq ι'] {Γ : Template ι Bool Bool}
    {Γ' : Template ι' Bool Bool} (jstar : ι')
    (L : List (Σ j : ι, Fin (Γ.r j) → Literal (Γ'.r jstar))) (I : SignedInstance Γ') :
    SignedInstance (Γ.union Γ') where
  n := I.n
  cons := I.cons.flatMap fun c =>
    if h : c.1 = jstar then
      L.map fun d => ⟨Sum.inl d.1, fun p => Literal.subst (fun i => c.2 (Fin.cast (by rw [h]) i))
        (d.2 p)⟩
    else [⟨Sum.inr c.1, c.2⟩]

/-- Global negation of a Boolean relation (§4.4, p.25): `−P = {x̄ : x ∈ P}` (published
`SymBoolPCSP.CFixing.negRel`) when `neg = true`, and `P` itself otherwise. -/
def negIf {k : ℕ} (neg : Bool) (P : Set (Fin k → Bool)) : Set (Fin k → Bool) :=
  if neg then SymBoolPCSP.CFixing.negRel P else P

end RobustBoolPCSP


