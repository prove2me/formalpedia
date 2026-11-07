-- Prove2me | Definitions.Def_BoolCSPDel_Con
-- name    : BoolCSPDel_Con
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T15:54:03.074789+00:00
-- url     : https://prove2.me/theorems/35db9ea4-65db-4fe9-84f7-a47dc581760f
-- title:
--   Constraint types $U^\Gamma_n$, $\mathrm{Sat}_\Gamma(f)$ and exact sparsifiers
-- statement:
--   A **constraint type** over a variable set $X$ is a relation $R\in\Gamma$ with an ordered scope in $X^a$, $a$ the arity of $R$. Repeated variables are allowed, and there are no negations or constants. Over $X=[n]$ these are the universe $U^\Gamma_n$. An **instance** is a frequency vector $f$; a constraint is **active** if $f_C>0$; and $\mathrm{Sat}_\Gamma(f)$ is the set of assignments satisfying every active constraint. An **exact sparsifier** of $f$ is a set $S\subseteq\mathrm{supp}(f)$ with $\mathrm{Sat}_\Gamma(S)=\mathrm{Sat}_\Gamma(f)$.
--
--   **Formalization Note** Frequency vectors take integer values, so that streams and signed sketches share one type; on nonnegative vectors this is the paper's definition.
-- source:
--   Bandekar, Sharma, Velusamy, A New Characterization of Streaming Decidability of Boolean CSPs Under Deletions, STOC 2027 submission (manuscript sha256 15f83519…), §3.1, p.17; §4.3, p.29

import Mathlib
import Definitions.Def_BoolCSPDel_Rel

namespace BoolCSPDel

/-- **Constraint types, instances, solutions, exact sparsifiers.** Bandekar, Sharma, Velusamy, STOC
2027 submission (manuscript sha256 15f83519…), §3.1, p.17: "The universe `U^Γ_n` specifies both a
relation and an ordered scope"; "The model permits repeated variables within a scope".

A constraint type over a variable set `X`: a relation of `Γ` and an ordered scope. `Con Γ (Fin n)` is
`U^Γ_n`.

**Formalization Note.** Scopes apply the relation directly to variables, without negations or
constants, and repeats are allowed. Instances are frequency vectors `f : Con Γ X → ℤ`; integer values
keep streams and signed sketches in one type, and `C` is active when `0 < f C`, so `supp f` and `Sat`
are the paper's on nonnegative `f`. -/
abbrev Con {k : ℕ} (Γ : Lang k) (X : Type) : Type :=
  Σ R : {R // R ∈ Γ}, (Fin R.1.1 → X)

/-- The assignment `γ` satisfies the constraint `C`. -/
def SatBy {k : ℕ} {Γ : Lang k} {X : Type} (C : Con Γ X) (γ : X → Bool) : Prop :=
  (fun i => γ (C.2 i)) ∈ C.1.1.2

/-- `Sat_Γ(f)`, p.17: the assignments satisfying every active constraint of `f`. -/
def Sat {k : ℕ} {Γ : Lang k} {X : Type} (f : Con Γ X → ℤ) : Set (X → Bool) :=
  {γ | ∀ C, 0 < f C → SatBy C γ}

/-- `Sat_Γ(S)` for a set of constraint types. -/
def SatSet {k : ℕ} {Γ : Lang k} {X : Type} (S : Finset (Con Γ X)) : Set (X → Bool) :=
  {γ | ∀ C ∈ S, SatBy C γ}

/-- §4.3, p.29: "an exact sparsifier of a Γ-instance `f` is a set `S ⊆ supp(f)` such that
`Sat_Γ(S) = Sat_Γ(f)`". -/
def IsExactSparsifier {k : ℕ} {Γ : Lang k} {X : Type} (S : Finset (Con Γ X)) (f : Con Γ X → ℤ) :
    Prop :=
  (∀ C ∈ S, 0 < f C) ∧ SatSet S = Sat f

end BoolCSPDel


