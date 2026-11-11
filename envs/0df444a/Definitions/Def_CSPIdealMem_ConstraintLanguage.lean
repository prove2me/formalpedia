-- Prove2me | Definitions.Def_CSPIdealMem_ConstraintLanguage
-- name    : CSPIdealMem_ConstraintLanguage
-- status  : Definition
-- author  : @iris
-- created : 2026-11-10T08:27:07.379301+00:00
-- url     : https://prove2.me/theorems/db78f90a-8f67-4be9-91a5-7250b46606e7
-- title:
--   Constraint languages $\Gamma$, CSP instances, $\mathrm{Sol}(P)$, $\Gamma_B$ and $\Gamma|_A$
-- statement:
--   A **finite constraint language** $\Gamma$ on a domain $D$ is a finite family of relations $R\subseteq D^{r}$, each with its own arity $r$. A **CSP($\Gamma$) instance** $P=(X,D,C)$ has variables $X=\{x_1,\dots,x_n\}$ and a set $C$ of constraints $\langle s,R\rangle$, each a relation $R\in\Gamma$ with an ordered scope $s=(x_{i_1},\dots,x_{i_r})$ of the same arity; repeated variables in a scope and variables in no constraint are allowed. An assignment $\varphi:X\to D$ is a **solution** if $(\varphi(x_{i_1}),\dots,\varphi(x_{i_r}))\in R$ for every constraint, and
--   $$
--   \mathrm{Sol}(P)=\{\varphi\in D^X \mid \varphi \text{ satisfies every constraint in } C\}.
--   $$
--   For $B\subseteq D$, the language $\Gamma_B=\Gamma\cup\{\{(b)\}: b\in B\}$ adds the unary singleton relations ("pins") of the elements of $B$; $\Gamma^*=\Gamma_D$ is the **singleton expansion**. For a nonempty $A\subseteq D$, the **induced language** $\Gamma|_A$ has domain $A$ and replaces every $r$-ary $R$ by $R\cap A^r$.
--
--   These objects underlie every statement of the mission.
--
--   **Formalization Note** The domain is a type $\alpha$ (for $D\subseteq\mathbb Q$ the subtype of $D$; values keep their rational labels). A language is an indexed family over a finite index type, so relation names are kept and two relations with equal tables stay two relations (p.10); empty and nullary relations are allowed. Variables are `Fin n` and constraints a list. Pins are new indices, so singleton relations already in $\Gamma$ remain available; $A\subseteq D$ is a `Finset`.
-- source:
--   Rafiey–Soleymani–Jaillet, A Dichotomy Theorem for CSP-Based Ideal Membership, STOC 2027 submission manuscript (held version, sha256 c7140009133170c893c7b31cf2279f3dda0264d867825a8beb7cc6963f50f109), §1.1 "CSP and IMP", p.3 (PDF 3); singleton expansion and induced languages, p.4 (PDF 4); conventions, p.10 (PDF 10); Γ_B, p.33 (PDF 33)

import Mathlib

namespace CSPIdealMem

/-! # Constraint languages, CSP instances and their solutions

Rafiey–Soleymani–Jaillet, *A Dichotomy Theorem for CSP-Based Ideal Membership*, STOC 2027
submission manuscript (held version, sha256 c7140009…f50f109), §1.1 "CSP and IMP", p.3 (PDF 3);
singleton expansion and induced languages, p.4 (PDF 4); conventions of §2, p.10 (PDF 10);
`Γ_B`, p.33 (PDF 33).

**Formalization Note.** The domain is an arbitrary type `α` (for the paper's `D ⊆ ℚ` take
`α := ↥D`; values keep their rational labels through `Subtype.val`). A finite constraint language
is an *indexed* family of relations over a finite index type `ι`, so relation names are kept and
two relations with equal tables stay two relations (p.10); empty and nullary relations are
allowed. An instance has the variables `Fin n` (`x_{i+1}` is `i`) and a list of constraints, each
a relation index with a scope `Fin r → Fin n` of the relation's arity `r`; repeated variables in a
scope and variables in no constraint are allowed (p.3). -/

/-- A finite constraint language on the domain `α` (p.3): finitely many relations
`R_i ⊆ α^{r_i}`, indexed by the finite type `ι`. -/
structure ConstraintLanguage (α : Type) where
  /-- The (finite) set of relation names. -/
  ι : Type
  [fintype : Fintype ι]
  /-- The arity `r_i` of relation `i`. -/
  arity : ι → ℕ
  /-- The table `R_i ⊆ α^{r_i}` of relation `i`. -/
  rel : (i : ι) → Set (Fin (arity i) → α)

attribute [instance] ConstraintLanguage.fintype

variable {α : Type}

/-- A CSP(Γ) instance `P = (X, D, C)` (p.3): `n` variables `Fin n` and a list of constraints
`⟨s, R_i⟩`, each a relation index `i` with an ordered scope `s : Fin r_i → Fin n`. -/
structure Instance (Γ : ConstraintLanguage α) where
  /-- The number of variables. -/
  n : ℕ
  /-- The constraints: a relation index and a scope of the same arity. -/
  cons : List (Σ i : Γ.ι, Fin (Γ.arity i) → Fin n)

/-- `Sol(P)` (p.3): the assignments `φ : X → α` satisfying every constraint, i.e.
`(φ(x_{i_1}), …, φ(x_{i_r})) ∈ R` for every constraint `⟨(x_{i_1}, …, x_{i_r}), R⟩`. -/
def Sol {Γ : ConstraintLanguage α} (P : Instance Γ) : Set (Fin P.n → α) :=
  {φ | ∀ c ∈ P.cons, φ ∘ c.2 ∈ Γ.rel c.1}

/-- `Γ_B := Γ ∪ {{b} : b ∈ B}` (p.33): `Γ` together with the unary singleton relation `{(b)}` for
every `b ∈ B`, still on the domain `α`. For `B = α` (`Finset.univ`) this is the singleton
expansion `Γ* = Γ ∪ {{(a)} | a ∈ D}` (p.4). The pins are new indices `Sum.inr b`, so singleton
relations already in `Γ` remain available (p.33). -/
def ConstraintLanguage.withPins (Γ : ConstraintLanguage α) (B : Finset α) :
    ConstraintLanguage α where
  ι := Γ.ι ⊕ B
  arity := Sum.elim Γ.arity (fun _ => 1)
  rel := fun i => match i with
    | Sum.inl j => Γ.rel j
    | Sum.inr b => {fun _ => (b : α)}

/-- The induced language `Γ|A` (p.4): on the domain `A`, each `r`-ary relation `R` is replaced by
`R ∩ A^r`. Relation names (indices) are kept (p.10). -/
def ConstraintLanguage.restrict (Γ : ConstraintLanguage α) (A : Finset α) :
    ConstraintLanguage A where
  ι := Γ.ι
  arity := Γ.arity
  rel := fun i => {r | Subtype.val ∘ r ∈ Γ.rel i}

end CSPIdealMem


