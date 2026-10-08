-- Prove2me | Definitions.Def_StrategyProofArrow_WeakArrow_Basic
-- name    : StrategyProofArrow_WeakArrow_Basic
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-06T15:46:13.28152+00:00
-- url     : https://prove2.me/theorems/ef8c7994-c173-4675-ae9d-05860166e950
-- title:
--   Weak and strong orders, social welfare functions, CS, IIA, NNR, dictatorship, tie-breaking functions
-- statement:
--   This file fixes the vocabulary of §2, §4 and §6 of Satterthwaite's paper for committees whose members may be indifferent between alternatives.
--
--   A committee $I_n$ of $n$ individuals chooses among a finite set $S_m$ of $m$ alternatives.
--
--   1. A **weak order** $R$ on $S_m$ is a complete and transitive relation; $x\,R\,y$ reads "$x$ is preferred or indifferent to $y$". Its **strict part** is $x\,\bar R\,y$, meaning $x\,R\,y$ and not $y\,R\,x$. The set of weak orders is $\pi_m$, and a **ballot set** $B=(B_1,\dots,B_n)$ is an element of $\pi_m^n$.
--   2. A **strong order** is a weak order with no indifference between distinct alternatives (a linear order); the strong orders form $\rho_m$ and strong ballot sets form $\rho_m^n$.
--   3. For $W\subseteq S_m$, the **choice set** is $\Psi_W(R)=\{x\in W : x\,R\,y \text{ for all } y\in W\}$, and two weak orders have the same restriction to $W$, $\theta_W(C)=\theta_W(D)$, when they agree on every pair of elements of $W$.
--   4. A **social welfare function** $u$ maps every ballot set $B\in\pi_m^n$ to a weak order $A=u(B)$, the social ordering. A **strict social welfare function** $\mu$ maps every strong ballot set $C\in\rho_m^n$ to a strong order.
--   5. **Citizens' sovereignty (CS)**: for all distinct $x,y$ some ballot set $B$ gives $x\,\bar A\,y$.
--   6. **Independence of irrelevant alternatives (IIA)**: for every $W\subseteq S_m$ and ballot sets $C,D$, if $\theta_W(C_i)=\theta_W(D_i)$ for all $i$, then $\Psi_W(A_C)=\Psi_W(A_D)$.
--   7. **Non-negative response (NNR)**: fix $x$ and let $W=S_m\setminus\{x\}$. If $C,D$ satisfy, for all $i$ and all $y\in W$, (a) $\theta_W(C_i)=\theta_W(D_i)$, (b) $x\,C_i\,y\Rightarrow x\,D_i\,y$ and (c) $x\,\bar C_i\,y\Rightarrow x\,\bar D_i\,y$, then for every $z\in W$, $x\,\bar A_C\,z$ implies $x\,\bar A_D\,z$.
--   8. $u$ is **dictatorial** (the negation of non-dictatorship) if some individual $i$ exists such that for every ballot set $B$ and all $x,y$,
--   $$x\,\bar B_i\,y \;\Longrightarrow\; x\,\bar A\,y,\qquad A=u(B).$$
--   The same four conditions are stated for strict social welfare functions, quantifying over $\rho_m^n$.
--   9. A **tie-breaking function** $\alpha$ maps every $B\in\pi_m^n$ to a strong ballot set $C=\alpha(B)$ that keeps every strict preference: $x\,\bar B_i\,y$ implies $x\,\bar C_i\,y$. It is **regular** if strong orders $Q_1,\dots,Q_n$ exist such that whenever $x$ and $y$ are tied in $B_i$, $x\,\bar C_i\,y$ iff $x\,\bar Q_i\,y$.
--   10. Breaking the ties of a single weak order $R$ by a strong order $Q$ gives the strong order in which $x$ ranks at least as high as $y$ iff $x\,\bar R\,y$, or $x,y$ are tied in $R$ and $x\,Q\,y$.
--
--   These objects carry Arrow's theorem from linear-order ballots to weak-order ballots.
--
--   **Formalization Note** Weak orders are a structure with a completeness and a transitivity field; strong orders are the subtype of weak orders with no indifference between distinct elements, and strong ballot sets are functions into that subtype, so a strict social welfare function is a function on admissible profiles only. $\theta_W(C)=\theta_W(D)$ is encoded as agreement on $W\times W$ instead of building $\pi_q$ on a subtype. The paper states CS "for every $x,y$"; we state it for $x\neq y$, since a strict social preference $x\,\bar A\,x$ is impossible. The paper's tie-breaking definition also lists the symmetric clause "$y\,\bar B_i\,x$ implies $y\,\bar C_i\,x$", which is the same condition with $x,y$ renamed. The single-ordering tie-breaker (item 10) is how we read the paper's $\gamma[u(B)]$, a profile-level $\gamma$ applied to one ordering, with its tie-breaking order $Q$ (pp. 48–49).
-- source:
--   Satterthwaite, Strategy-proofness and Arrow's Conditions, Northwestern Discussion Paper No. 122 (rev. Dec. 12, 1974), §2 pp. 6–9 (weak and strong orders, Ψ_W, θ_W), §4 pp. 28–31 (social welfare function, ND, IIA, CS, NNR, strict social welfare function), §6 pp. 38–39 (tie-breaking and regular tie-breaking functions, (34)), pp. 48–49 (γ applied to a social ordering)

import Mathlib

namespace StrategyProofArrow.WeakArrow

/-- A weak order on `A` (Satterthwaite, p. 6, the set `π_m`): a complete and transitive relation.
`R.rel x y` reads "`x` is preferred or indifferent to `y`". Completeness gives reflexivity. -/
structure WeakOrder (A : Type*) where
  /-- The weak relation: `rel x y` is "x R y". -/
  rel : A → A → Prop
  /-- Completeness (hence reflexivity). -/
  total : ∀ x y, rel x y ∨ rel y x
  /-- Transitivity. -/
  trans : ∀ x y z, rel x y → rel y z → rel x z

variable {ι A : Type*}

/-- Strict part of a weak order (p. 6): `x R̄ y` iff `x R y` and not `y R x`. -/
def WeakOrder.strict (R : WeakOrder A) (x y : A) : Prop := R.rel x y ∧ ¬ R.rel y x

/-- A **strong order** (p. 8, the set `ρ_m`): a weak order with no indifference between distinct
alternatives. -/
def WeakOrder.IsStrong (R : WeakOrder A) : Prop := ∀ x y, R.rel x y → R.rel y x → x = y

/-- The strong orders on `A` (`ρ_m`). -/
abbrev StrongOrder (A : Type*) := {R : WeakOrder A // R.IsStrong}

/-- Ballot sets of weak orders (`π^n_m`). -/
abbrev WeakProfile (ι A : Type*) := ι → WeakOrder A

/-- Ballot sets of strong orders (`ρ^n_m`): every ballot is a strong order. -/
abbrev StrongProfile (ι A : Type*) := ι → StrongOrder A

/-- A strong ballot set read as a weak ballot set (`ρ^n_m ⊂ π^n_m`). -/
def toWeak (C : StrongProfile ι A) : WeakProfile ι A := fun i => (C i).1

/-- The choice set `Ψ_W(R)` (p. 9): the elements of `W` that `R` ranks at least as high as every
element of `W`. -/
def Psi (W : Set A) (R : WeakOrder A) : Set A := {x | x ∈ W ∧ ∀ y ∈ W, R.rel x y}

/-- `θ_W(C) = θ_W(D)` (p. 9): the two weak orders agree on `W × W`. -/
def AgreeOn (W : Set A) (C D : WeakOrder A) : Prop :=
  ∀ x ∈ W, ∀ y ∈ W, (C.rel x y ↔ D.rel x y)

/-! ### Arrow's conditions for social welfare functions on weak ballot sets (pp. 28–31)

A social welfare function is a map `u : WeakProfile ι A → WeakOrder A` (domain `π^n_m`, range in
`π_m`). -/

/-- **Citizens' sovereignty (CS)** (p. 29), for distinct alternatives: for every `x ≠ y` some ballot
set makes society strictly prefer `x` to `y`. (As printed, the condition also asks this for
`x = y`, which no strict relation satisfies.) -/
def CS (u : WeakProfile ι A → WeakOrder A) : Prop :=
  ∀ x y : A, x ≠ y → ∃ B : WeakProfile ι A, (u B).strict x y

/-- **Independence of irrelevant alternatives (IIA)** (p. 29): if every ballot of `C` agrees with
the corresponding ballot of `D` on `W`, the social choice sets `Ψ_W` coincide. -/
def IIA (u : WeakProfile ι A → WeakOrder A) : Prop :=
  ∀ (W : Set A) (C D : WeakProfile ι A),
    (∀ i, AgreeOn W (C i) (D i)) → Psi W (u C) = Psi W (u D)

/-- **Non-negative response (NNR)** (p. 31): let `W = S_m - {x}`. If (a) every ballot of `D`
agrees with that of `C` on `W`, (b) `x C_i y` implies `x D_i y` and (c) `x C̄_i y` implies
`x D̄_i y`, for all `i` and `y ∈ W`, then for every `z ∈ W`, `x Ā_C z` implies `x Ā_D z`. -/
def NNR (u : WeakProfile ι A → WeakOrder A) : Prop :=
  ∀ (x : A) (C D : WeakProfile ι A),
    (∀ i, AgreeOn {y | y ≠ x} (C i) (D i)) →
    (∀ i y, y ≠ x → (C i).rel x y → (D i).rel x y) →
    (∀ i y, y ≠ x → (C i).strict x y → (D i).strict x y) →
    ∀ z, z ≠ x → (u C).strict x z → (u D).strict x z

/-- **Dictatorial** (the negation of non-dictatorship ND, p. 29): some individual `i` such that,
for every ballot set `B` and all `x, y`, `x B̄_i y` implies `x Ā y` with `A = u(B)`. Nothing is
required where `i` is indifferent. -/
def Dictatorial (u : WeakProfile ι A → WeakOrder A) : Prop :=
  ∃ i : ι, ∀ (B : WeakProfile ι A) (x y : A), (B i).strict x y → (u B).strict x y

/-! ### The same conditions for strict social welfare functions (p. 31)

A strict social welfare function is a map `μ : StrongProfile ι A → StrongOrder A` (domain `ρ^n_m`,
range in `ρ_m`). -/

/-- CS for a strict social welfare function (p. 29, on `ρ^n_m`), for distinct alternatives. -/
def StrictCS (μ : StrongProfile ι A → StrongOrder A) : Prop :=
  ∀ x y : A, x ≠ y → ∃ B : StrongProfile ι A, (μ B).1.strict x y

/-- IIA for a strict social welfare function (p. 29, on `ρ^n_m`). -/
def StrictIIA (μ : StrongProfile ι A → StrongOrder A) : Prop :=
  ∀ (W : Set A) (C D : StrongProfile ι A),
    (∀ i, AgreeOn W (C i).1 (D i).1) → Psi W (μ C).1 = Psi W (μ D).1

/-- NNR for a strict social welfare function (p. 31, on `ρ^n_m`). -/
def StrictNNR (μ : StrongProfile ι A → StrongOrder A) : Prop :=
  ∀ (x : A) (C D : StrongProfile ι A),
    (∀ i, AgreeOn {y | y ≠ x} (C i).1 (D i).1) →
    (∀ i y, y ≠ x → (C i).1.rel x y → (D i).1.rel x y) →
    (∀ i y, y ≠ x → (C i).1.strict x y → (D i).1.strict x y) →
    ∀ z, z ≠ x → (μ C).1.strict x z → (μ D).1.strict x z

/-- A strict social welfare function is dictatorial (negation of ND, p. 29, on `ρ^n_m`). -/
def StrictDictatorial (μ : StrongProfile ι A → StrongOrder A) : Prop :=
  ∃ i : ι, ∀ (B : StrongProfile ι A) (x y : A), (B i).1.strict x y → (μ B).1.strict x y

/-! ### Tie-breaking functions (p. 38) -/

/-- A **tie-breaking function** (p. 38): `α` maps weak ballot sets to strong ballot sets so that
every strict preference `x B̄_i y` of every ballot is kept, `x C̄_i y` with `C = α(B)`. The ballot
`α(B)_i` may depend on the whole ballot set `B`. -/
def IsTieBreaking (α : WeakProfile ι A → StrongProfile ι A) : Prop :=
  ∀ (B : WeakProfile ι A) (i : ι) (x y : A), (B i).strict x y → (α B i).1.strict x y

/-- A **regular tie-breaking function** (p. 38): a tie-breaking function for which strong orders
`Q = (Q_1, …, Q_n)` exist such that whenever `x` and `y` are tied in `B_i`, `x C̄_i y` iff
`x Q̄_i y`, where `C = γ(B)`. -/
def IsRegular (γ : WeakProfile ι A → StrongProfile ι A) : Prop :=
  IsTieBreaking γ ∧ ∃ Q : StrongProfile ι A, ∀ (B : WeakProfile ι A) (i : ι) (x y : A),
    (B i).rel x y → (B i).rel y x → ((γ B i).1.strict x y ↔ (Q i).1.strict x y)

/-- Breaking the ties of one weak order `R` by a strong order `Q` (the single-ordering tie-breaker
`γ[u(B)]` of Lemma 11 and Theorem 3', pp. 48–49): `x` is ranked at least as high as `y` iff
`x R̄ y`, or `x` and `y` are tied in `R` and `x Q y`. This is a regular component tie-breaking
function with tie-breaking order `Q`. -/
def breakTies (Q : StrongOrder A) (R : WeakOrder A) : StrongOrder A :=
  ⟨{ rel := fun x y => R.strict x y ∨ (R.rel x y ∧ R.rel y x ∧ Q.1.rel x y)
     total := by
       intro x y
       rcases R.total x y with hxy | hyx
       · by_cases hyx : R.rel y x
         · rcases Q.1.total x y with hq | hq
           · exact Or.inl (Or.inr ⟨hxy, hyx, hq⟩)
           · exact Or.inr (Or.inr ⟨hyx, hxy, hq⟩)
         · exact Or.inl (Or.inl ⟨hxy, hyx⟩)
       · by_cases hxy : R.rel x y
         · rcases Q.1.total x y with hq | hq
           · exact Or.inl (Or.inr ⟨hxy, hyx, hq⟩)
           · exact Or.inr (Or.inr ⟨hyx, hxy, hq⟩)
         · exact Or.inr (Or.inl ⟨hyx, hxy⟩)
     trans := by
       intro x y z h1 h2
       rcases h1 with ⟨hxy, hnyx⟩ | ⟨hxy, hyx, hq1⟩ <;>
         rcases h2 with ⟨hyz, hnzy⟩ | ⟨hyz, hzy, hq2⟩
       · exact Or.inl ⟨R.trans _ _ _ hxy hyz, fun hzx => hnyx (R.trans _ _ _ hyz hzx)⟩
       · exact Or.inl ⟨R.trans _ _ _ hxy hyz, fun hzx => hnyx (R.trans _ _ _ hyz hzx)⟩
       · exact Or.inl ⟨R.trans _ _ _ hxy hyz, fun hzx => hnzy (R.trans _ _ _ hzx hxy)⟩
       · exact Or.inr ⟨R.trans _ _ _ hxy hyz, R.trans _ _ _ hzy hyx,
           Q.1.trans _ _ _ hq1 hq2⟩ },
   by
     intro x y h1 h2
     rcases h1 with ⟨hxy, hnyx⟩ | ⟨hxy, hyx, hq1⟩
     · rcases h2 with ⟨_, h⟩ | ⟨h, _, _⟩
       · exact absurd hxy h
       · exact absurd h hnyx
     · rcases h2 with ⟨_, h⟩ | ⟨_, _, hq2⟩
       · exact absurd hxy h
       · exact Q.2 x y hq1 hq2⟩

end StrategyProofArrow.WeakArrow


