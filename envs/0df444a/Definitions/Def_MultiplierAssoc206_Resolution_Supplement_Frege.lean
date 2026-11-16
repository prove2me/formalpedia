-- Prove2me | Definitions.Def_MultiplierAssoc206_Resolution_Supplement_Frege
-- name    : MultiplierAssoc206_Resolution_Supplement_Frege
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-15T15:33:25.370047+00:00
-- url     : https://prove2.me/theorems/da829fdc-c724-47fc-a31b-9f251abeff4a
-- title:
--   Frege systems (sound, implicationally complete rule sets), derivations, refutations, and their depth and size
-- statement:
--   An **inference rule** has the form
--   $$\frac{F_1(p_1,\dots,p_k)\quad\cdots\quad F_j(p_1,\dots,p_k)}{F(p_1,\dots,p_k)}$$
--   for fixed formulas $F_1,\dots,F_j$ (possibly $j=0$) and $F$ over the variables $p_1,\dots,p_k$; it may be applied with arbitrary formulas substituted for $p_1,\dots,p_k$. A rule is **sound** when every assignment to $p_1,\dots,p_k$ satisfying all premises satisfies the conclusion.
--
--   Given a set of rules, a **derivation** of a formula $G$ from a set of formulas $\Gamma$ is a sequence of formulas ending in $G$, each of which belongs to $\Gamma$ or follows from earlier formulas by a rule: it is $F^\tau$ for a rule with conclusion $F$ and a substitution $\tau$ of formulas for $p_1,\dots,p_k$, and every premise instance $F_i^\tau$ occurs earlier in the sequence. A **refutation** of $\Gamma$ is a derivation of $\bot$ from $\Gamma$. The **depth** of a derivation is the maximum depth of its formulas and its **size** $|\pi|$ is the total size of its formulas.
--
--   A **Frege system** is a finite set of rules that are sound and **implicationally complete**: whenever $\Gamma$ implies $G$ (every assignment satisfying all formulas of $\Gamma$ satisfies $G$), $G$ has a derivation from $\Gamma$. We write $\mathrm{size}_{\mathrm{Frege}_d}(\Phi)$ for the minimum size of a refutation of $\Phi$ of depth at most $d$.
--
--   Every statement of the bounded-depth Frege part of the paper is made for an arbitrary Frege system, fixed throughout.
--
--   **Formalization Note** A rule stores its arity $k$, its list of premises and its conclusion, all formulas over `Fin k`. A Frege system is a list of rules (hence finite) with `IsFregeSystem`: every rule sound, and implicational completeness for every variable type and every *finite* set $\Gamma$; by the compactness theorem of propositional logic this is equivalent to completeness for all $\Gamma$, and derivations use only finitely many formulas of $\Gamma$ anyway. A derivation is a list whose last entry is $G$, so it is nonempty. The minimum $\mathrm{size}_{\mathrm{Frege}_d}$ is not defined; the theorems state their bounds for every refutation of depth at most $d$.
-- source:
--   Vincent Liew, Associativity of Multiplication Is Hard for Resolution, STOC 2027 submission #206 (October 2026), source.pdf SHA-256 676dcc4be9158c52d07aec1c9d48f53fa38289ed1b4dcb34b53adc70dbdd5ead, PDF p.23 (printed p.22), §9.1 "Frege systems"

import Mathlib
import Definitions.Def_MultiplierAssoc206_Resolution_Supplement_Formula

set_option autoImplicit false

namespace MultiplierAssoc206.Resolution.Supplement

/-! # Frege systems, derivations and refutations, their depth and size

Liew, *Associativity of Multiplication Is Hard for Resolution*, §9.1 "Frege systems"
(PDF p. 23). A Frege system is a finite set of inference rules `F₁ ⋯ F_j / F` over variables
`p₁, …, p_k`, applied with arbitrary formulas substituted for the `p_i`; the rules are sound and
implicationally complete. -/

/-- An inference rule `F₁(p₁,…,p_k) ⋯ F_j(p₁,…,p_k) / F(p₁,…,p_k)`: an arity `k`, the
premises `F₁, …, F_j` (possibly none) and the conclusion `F`, formulas over `p₁, …, p_k`. -/
structure Rule where
  /-- the number `k` of rule variables `p₁, …, p_k` -/
  k : ℕ
  /-- the premises `F₁, …, F_j` -/
  premises : List (Formula (Fin k))
  /-- the conclusion `F` -/
  concl : Formula (Fin k)

/-- A rule is sound when every assignment of its variables satisfying all premises satisfies
the conclusion. -/
def Rule.Sound (r : Rule) : Prop :=
  ∀ a : Fin r.k → Bool, (∀ P ∈ r.premises, P.eval a = true) → r.concl.eval a = true

/-- A derivation of `G` from the set of formulas `Γ` in the rule system `R`: a nonempty
sequence of formulas ending in `G`, each of which belongs to `Γ` or follows from earlier
formulas by a rule: it is the conclusion `F^τ` of a rule of `R` under one substitution `τ` of
formulas for the rule variables, and every premise instance `F_i^τ` occurs earlier in the
sequence (premises may be reused). -/
def IsDerivation {α : Type} (R : List Rule) (Γ : Set (Formula α)) (G : Formula α)
    (π : List (Formula α)) : Prop :=
  π.getLast? = some G ∧
  ∀ t (ht : t < π.length),
    π[t] ∈ Γ ∨ ∃ r ∈ R, ∃ τ : Fin r.k → Formula α, π[t] = r.concl.subst τ ∧
      ∀ P ∈ r.premises, ∃ i, ∃ hi : i < t, π[i]'(lt_trans hi ht) = P.subst τ

/-- A refutation of `Γ`: a derivation of `⊥` from `Γ`. -/
def IsRefutation {α : Type} (R : List Rule) (Γ : Set (Formula α)) (π : List (Formula α)) :
    Prop :=
  IsDerivation R Γ Formula.bot π

/-- The depth of a derivation: the maximum depth of its formulas. -/
def derivDepth {α : Type} (π : List (Formula α)) : ℕ := (π.map Formula.depth).foldr max 0

/-- The size of a derivation: the total size of its formulas. -/
def derivSize {α : Type} (π : List (Formula α)) : ℕ := (π.map Formula.size).sum

/-- Implicational completeness: whenever a finite set `Γ` of formulas (over any variable type)
implies a formula `G`, i.e. every assignment satisfying all of `Γ` satisfies `G`, then `G` has
a derivation from `Γ`. -/
def ImplComplete (R : List Rule) : Prop :=
  ∀ (α : Type) (Γ : Set (Formula α)) (G : Formula α), Γ.Finite →
    (∀ a : α → Bool, (∀ F ∈ Γ, F.eval a = true) → G.eval a = true) →
      ∃ π, IsDerivation R Γ G π

/-- A Frege system: a finite list `R` of inference rules, each sound, that is implicationally
complete. -/
def IsFregeSystem (R : List Rule) : Prop := (∀ r ∈ R, r.Sound) ∧ ImplComplete R

end MultiplierAssoc206.Resolution.Supplement


