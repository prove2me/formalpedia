-- Prove2me | Definitions.Def_StrategyProofArrow_Correspondence_Basic
-- name    : StrategyProofArrow_Correspondence_Basic
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-06T15:46:14.032206+00:00
-- url     : https://prove2.me/theorems/a981cfd4-e530-413e-a6e5-c45336990a6f
-- title:
--   Strong orders and strict ballot sets, strategy-proofness, underlying/derived, CS, PO, IIA, NNR, Gibbard's $\Delta_{xy}$ and relation $P$
-- statement:
--   This file fixes the objects of §2 and §4 of Satterthwaite's paper for **strict** committees. A committee $I_n$ of $n$ individuals chooses among a finite alternative set $S_m$ of $m$ alternatives.
--
--   1. **Weak and strong orders.** A weak order $R$ on $S_m$ is a complete and transitive relation; $x\,R\,y$ reads "$x$ is preferred or indifferent to $y$", and the strict part is $x\,\bar R\,y$ iff $x\,R\,y$ and not $y\,R\,x$. A **strong order** is a weak order with no indifference between distinct alternatives; $\rho_m$ is the set of strong orders and $\rho_m^n$ the set of strict ballot sets $B=(B_1,\dots,B_n)$.
--   2. **Choice sets.** For $W\subseteq S_m$, $\Psi_W(R)=\{x\in W : x\,R\,y \text{ for all } y\in W\}$. The statement $\theta_W(C_i)=\theta_W(D_i)$ says that $C_i$ and $D_i$ agree on every pair of elements of $W$.
--   3. **Strategy-proofness.** A strict voting procedure $v:\rho_m^n\to S_m$ is strategy-proof if there are no $B\in\rho_m^n$, individual $i$ and $B_i'\in\rho_m$ with
--   $$v(B_1,\dots,B_i',\dots,B_n)\;\bar B_i\; v(B_1,\dots,B_i,\dots,B_n).$$
--   4. **Underlying / derived.** A strict social welfare function $u:\rho_m^n\to\rho_m$ *underlies* $v$, equivalently $v$ is *derived from* $u$, if $\Psi_{S_m}[u(B)]=\{v(B)\}$ for every $B\in\rho_m^n$: $v(B)$ is the top alternative of the social ordering $u(B)$.
--   5. **Arrow's conditions** on $u$, writing $A_B=u(B)$:
--      - **CS** (citizens' sovereignty): for all $x\neq y$ there is $B$ with $x\,\bar A_B\,y$;
--      - **PO** (Pareto optimality): if $x\,\bar B_i\,y$ for all $i$, then $x\,\bar A_B\,y$;
--      - **IIA**: for every $W\subseteq S_m$, if $\theta_W(C_i)=\theta_W(D_i)$ for all $i$, then $\Psi_W(A_C)=\Psi_W(A_D)$;
--      - **NNR** (non-negative response): for every $x$, with $W=S_m\setminus\{x\}$, and all $C,D$ such that for all $i$ (a) $\theta_W(C_i)=\theta_W(D_i)$, (b) $x\,C_i\,y\Rightarrow x\,D_i\,y$ and (c) $x\,\bar C_i\,y\Rightarrow x\,\bar D_i\,y$ for all $y\in W$: if $x\,\bar A_C\,z$ for some $z\in W$, then $x\,\bar A_D\,z$.
--   6. **Gibbard's construction.** Fix a strong order $Q$. For alternatives $x,y$, $\Delta_{xy}(B_i)$ is the strong order that puts $x$ and $y$ above every other alternative, orders $x$ and $y$ between themselves as $B_i$ does, and orders the remaining alternatives as $Q$ does. For a voting procedure $v$ and a ballot set $B$, Gibbard's relation $P$ is given by: for $x\ne y$, $x\,\bar P\,y$ iff $x=v[\Delta_{xy}(B_1),\dots,\Delta_{xy}(B_n)]$.
--
--   These objects are shared by every statement of the mission: the correspondence between strategy-proof voting procedures and social welfare functions satisfying CS, NNR and IIA.
--
--   **Formalization Note** Weak orders are a structure (`rel`, completeness, transitivity), and strong orders and strict ballot sets are subtypes, so that every procedure and social welfare function is defined only on admissible ballot sets; two social welfare functions are equal iff they agree on every strict ballot set. The range condition "the range of a strict social welfare function is $\rho_m$ or a subset" is built into the codomain. $\theta_W(C_i)=\theta_W(D_i)$ is encoded as agreement on $W\times W$ (`AgreeOn`). CS is stated for $x\ne y$: the paper's "for every $x,y$" cannot hold at $x=y$ for a strict relation. NNR's "for some $x$" is read as "for every $x$", as in Arrow's condition. The paper's condition (c) of $\Delta_{xy}$ is read on the pairs $w,z\notin\{x,y\}$ with $w\ne z$. The paper defines $\Delta_{xy}$ only for $x\neq y$; the Lean map is total, its value at $x=y$ (with $x$ on top and the rest ordered by $Q$) is never used, because `gibbardRel` settles the case $x=y$ directly. $\Delta_{xy}=\Delta_{yx}$, so the order of $x,y$ in the subscript is immaterial. For $W=\emptyset$, $\Psi_W(R)=\emptyset$, which makes the case $W=\emptyset$ of IIA trivially true and changes nothing. Gibbard's $P$ is encoded as the weak relation `gibbardRel`: $x\,P\,y$ iff $x=y$ or $x=v[\Delta_{xy}(B)]$, whose strict part for $x\neq y$ is the paper's $\bar P$.
-- source:
--   Satterthwaite, Strategy-proofness and Arrow's Conditions, Northwestern Discussion Paper No. 122 (rev. Dec. 12, 1974), §2 pp. 6–9 (weak/strong orders, strategy-proofness, Ψ_W, θ_W); §4 pp. 28–33 (social welfare functions, ND/IIA/CS p. 29, derived p. 30, NNR/PO/strict SWF p. 31, underlies and Δ_xy pp. 32–33, P p. 33)

import Mathlib

namespace StrategyProofArrow.Correspondence

/-- A weak order on `A` (the paper's `π_m`, p. 6): `rel x y` reads "x is preferred or
indifferent to y". Completeness gives reflexivity. -/
structure WeakOrder (A : Type*) where
  rel : A → A → Prop
  total : ∀ x y, rel x y ∨ rel y x
  trans : ∀ x y z, rel x y → rel y z → rel x z

/-- Two weak orders with the same relation are equal. -/
@[ext] theorem WeakOrder.ext {A : Type*} {R S : WeakOrder A} (h : R.rel = S.rel) : R = S := by
  cases R; cases S; cases h; rfl

/-- Strict part: `x R̄ y` means `x R y` and not `y R x` (p. 6). -/
def WeakOrder.strict {A : Type*} (R : WeakOrder A) (x y : A) : Prop := R.rel x y ∧ ¬ R.rel y x

/-- A strong order (the paper's `ρ_m`, p. 8): a weak order with no indifference between
distinct alternatives. -/
def WeakOrder.IsStrong {A : Type*} (R : WeakOrder A) : Prop :=
  ∀ x y, R.rel x y → R.rel y x → x = y

/-- The set `ρ_m` of strong orders on `A`. -/
abbrev StrongOrder (A : Type*) := {R : WeakOrder A // R.IsStrong}

/-- Strict ballot sets `ρ^n_m`: one strong order per individual. -/
abbrev StrongProfile (ι A : Type*) := ι → StrongOrder A

/-- The choice function `Ψ_W(R)` (p. 9): the `R`-maximal elements of `W`. -/
def Psi {A : Type*} (W : Set A) (R : WeakOrder A) : Set A := {x | x ∈ W ∧ ∀ y ∈ W, R.rel x y}

/-- `θ_W(C) = θ_W(D)` (p. 9): the two relations agree on `W × W`. -/
def AgreeOn {A : Type*} (W : Set A) (C D : WeakOrder A) : Prop :=
  ∀ x ∈ W, ∀ y ∈ W, (C.rel x y ↔ D.rel x y)

/-- A strict voting procedure `v : ρ^n_m → S_m` is strategy-proof (pp. 7–9): no individual `i`
at any strict ballot set `B` has a strict ballot `b` with `v(B with B_i replaced by b) B̄_i v(B)`. -/
def StrategyProof {ι A : Type*} [DecidableEq ι] (v : StrongProfile ι A → A) : Prop :=
  ∀ (B : StrongProfile ι A) (i : ι) (b : StrongOrder A),
    ¬ (B i).1.strict (v (Function.update B i b)) (v B)

/-- `u` underlies `v` (p. 32), equivalently `v` is derived from `u` (p. 30):
`Ψ_S[u(B)] = {v(B)}` for every strict ballot set `B`, where `S` is the whole alternative set. -/
def Underlies {ι A : Type*} (u : StrongProfile ι A → StrongOrder A)
    (v : StrongProfile ι A → A) : Prop :=
  ∀ B, Psi Set.univ (u B).1 = {v B}

/-- Citizens' sovereignty (p. 29), for distinct alternatives: for all `x ≠ y` some strict ballot
set has `x Ā y`. -/
def CS {ι A : Type*} (u : StrongProfile ι A → StrongOrder A) : Prop :=
  ∀ x y : A, x ≠ y → ∃ B, (u B).1.strict x y

/-- Pareto optimality (p. 31): if every individual strictly prefers `x` to `y` in `B`, then
`x Ā y` where `A = u(B)`. -/
def PO {ι A : Type*} (u : StrongProfile ι A → StrongOrder A) : Prop :=
  ∀ (B : StrongProfile ι A) (x y : A), (∀ i, (B i).1.strict x y) → (u B).1.strict x y

/-- Independence of irrelevant alternatives (p. 29): for every `W ⊆ S_m` and strict ballot sets
`C, D` with `θ_W(C_i) = θ_W(D_i)` for all `i`, `Ψ_W(A_C) = Ψ_W(A_D)`. -/
def IIA {ι A : Type*} (u : StrongProfile ι A → StrongOrder A) : Prop :=
  ∀ (W : Set A) (C D : StrongProfile ι A),
    (∀ i, AgreeOn W (C i).1 (D i).1) → Psi W (u C).1 = Psi W (u D).1

/-- Non-negative response (p. 31): for every `x`, with `W = S_m - {x}`, and strict ballot sets
`C, D` such that (a) `θ_W(C_i) = θ_W(D_i)`, (b) `x C_i y ⇒ x D_i y` and (c) `x C̄_i y ⇒ x D̄_i y`
for all `i` and all `y ∈ W`: whenever `x Ā_C z` for `z ∈ W`, also `x Ā_D z`. -/
def NNR {ι A : Type*} (u : StrongProfile ι A → StrongOrder A) : Prop :=
  ∀ (x : A) (C D : StrongProfile ι A),
    (∀ i, AgreeOn ({x}ᶜ : Set A) (C i).1 (D i).1) →
    (∀ i, ∀ y, y ≠ x → (C i).1.rel x y → (D i).1.rel x y) →
    (∀ i, ∀ y, y ≠ x → (C i).1.strict x y → (D i).1.strict x y) →
    ∀ z, z ≠ x → (u C).1.strict x z → (u D).1.strict x z

/-- The relation of Gibbard's `Δ_xy(R)` (pp. 32–33): `x` and `y` are above every other
alternative and ordered between themselves as in `R`; the other alternatives are ordered by `Q`. -/
def deltaRel {A : Type*} (Q R : WeakOrder A) (x y : A) (w z : A) : Prop :=
  ((w = x ∨ w = y) ∧ (z = x ∨ z = y) ∧ R.rel w z) ∨
  ((w = x ∨ w = y) ∧ ¬ (z = x ∨ z = y)) ∨
  (¬ (w = x ∨ w = y) ∧ ¬ (z = x ∨ z = y) ∧ Q.rel w z)

/-- Gibbard's `Δ_xy` (pp. 32–33) as a map `ρ_m → ρ_m`, for a fixed strong order `Q`. -/
def delta {A : Type*} (Q : StrongOrder A) (x y : A) (R : StrongOrder A) : StrongOrder A :=
  ⟨{ rel := deltaRel Q.1 R.1 x y
     total := by
       intro w z
       unfold deltaRel
       by_cases hw : (w = x ∨ w = y) <;> by_cases hz : (z = x ∨ z = y) <;>
         simp only [hw, hz, true_and, false_and, not_true_eq_false, not_false_eq_true, and_true,
           and_false, or_false, false_or, or_true]
       · exact R.1.total w z
       · exact Q.1.total w z
     trans := by
       intro a b c hab hbc
       unfold deltaRel at *
       by_cases ha : (a = x ∨ a = y) <;> by_cases hb : (b = x ∨ b = y) <;>
         by_cases hc : (c = x ∨ c = y) <;>
         simp only [ha, hb, hc, true_and, false_and, not_true_eq_false, not_false_eq_true,
           and_true, and_false, or_false, false_or, or_true] at hab hbc ⊢
       · exact R.1.trans _ _ _ hab hbc
       · exact Q.1.trans _ _ _ hab hbc },
   by
     intro w z h1 h2
     unfold deltaRel at h1 h2
     by_cases hw : (w = x ∨ w = y) <;> by_cases hz : (z = x ∨ z = y) <;>
       simp only [hw, hz, true_and, false_and, not_true_eq_false, not_false_eq_true, and_true,
         and_false, or_false, false_or, or_true] at h1 h2
     · exact R.2 w z h1 h2
     · exact Q.2 w z h1 h2⟩

/-- Gibbard's relation `P` for the ballot set `B` (p. 33), as a weak relation: `x P y` iff
`x = y` or `x = v[Δ_xy(B_1), …, Δ_xy(B_n)]`. For `x ≠ y` its strict part is the paper's `x P̄ y`. -/
def gibbardRel {ι A : Type*} (v : StrongProfile ι A → A) (Q : StrongOrder A)
    (B : StrongProfile ι A) (x y : A) : Prop :=
  x = y ∨ x = v (fun i => delta Q x y (B i))

end StrategyProofArrow.Correspondence


