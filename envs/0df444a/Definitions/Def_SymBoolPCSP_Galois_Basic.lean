-- Prove2me | Definitions.Def_SymBoolPCSP_Galois_Basic
-- name    : SymBoolPCSP_Galois_Basic
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-08T01:23:44.221302+00:00
-- url     : https://prove2.me/theorems/fc9d63a0-5261-49cd-8440-af87babbd564
-- title:
--   Promise families, Pol(Γ) ⊆ Pol(Γ′), Γ ∪ {EQUAL}-PCSPs, ppp-definability, S_L ⊆ T_L and S′_m ⊆ T′_m (Defs 2.1–2.4, 6.2; Prop 6.3)
-- statement:
--   This file fixes the vocabulary of §6.1 of Brakensiek–Guruswami over an arbitrary finite domain $D$.
--
--   **Promise families.** A relation of arity $k$ is a subset $P \subseteq D^k$, and a promise relation is a pair $(P, Q)$ of relations of the same arity with $P \subseteq Q$ (Definition 2.1). A family $\Gamma = \{(P_R, Q_R) : R \in \tau\}$ of promise relations, indexed by a set $\tau$ of symbols with arities $k_R$, is given by two relational structures on $D$: one holding the relations $P_R$, the other holding the relations $Q_R$. The family is a *promise family* when $P_R \subseteq Q_R$ for every $R$.
--
--   **Polymorphisms.** A function $f : D^L \to D$ is a polymorphism of $\Gamma$ if, for every symbol $R$ and all $x^{(1)}, \dots, x^{(L)} \in P_R$,
--   $$\big(f(x^{(1)}_1, \dots, x^{(L)}_1), \dots, f(x^{(1)}_{k_R}, \dots, x^{(L)}_{k_R})\big) \in Q_R$$
--   (Definition 2.4). $\mathrm{Pol}(\Gamma)$ is the set of polymorphisms of all arities $L \ge 0$, and $\mathrm{Pol}(\Gamma) \subseteq \mathrm{Pol}(\Gamma')$ means that every polymorphism of $\Gamma$, of every arity, is a polymorphism of $\Gamma'$.
--
--   **$\Gamma \cup \{\mathrm{EQUAL}\}$-PCSPs.** $\mathrm{EQUAL} = \{(i, i) : i \in D\}$ is the binary equality relation. A $\Gamma \cup \{\mathrm{EQUAL}\}$-PCSP $\Psi$ on $n$ variables is a finite list of clauses, each consisting of a symbol (either a symbol $R$ of $\Gamma$ or EQUAL) and a tuple of variables of the matching arity, repetition allowed (Definition 2.2). An assignment $z \in D^n$ satisfies $\Psi_P$ if every clause tuple lies in its $P$-relation ($P_R$, or EQUAL), and satisfies $\Psi_Q$ if every clause tuple lies in its $Q$-relation ($Q_R$, or EQUAL). $\Psi_P$ and $\Psi_Q$ are the same clause list read in two ways.
--
--   **ppp-definability (Definition 6.2).** A promise relation $(P', Q') \subseteq D^k \times D^k$ is *positive primitive promise definable* (ppp-definable) from $\Gamma$ if there are $\ell \ge 0$ and a $\Gamma \cup \{\mathrm{EQUAL}\}$-PCSP $\Psi$ on $k + \ell$ variables such that
--   1. for every $x \in P'$ there is $y \in D^\ell$ such that $(x, y)$ satisfies $\Psi_P$;
--   2. for every assignment $z \in D^{k+\ell}$ satisfying $\Psi_Q$, $(z_1, \dots, z_k) \in Q'$.
--
--   "Ppp-definable from $(P, Q)$" refers to the one-relation family $\{(P, Q)\}$.
--
--   **The relations of polymorphisms.** For $L \ge 0$,
--   $$S_L = \{f : D^L \to D : f \in \mathrm{Pol}(P_R, P_R) \text{ for all } R\}, \qquad T_L = \{f : D^L \to D : f \in \mathrm{Pol}(P_R, Q_R) \text{ for all } R\},$$
--   viewed as relations of arity $|D|^L$ by listing the values of $f$ (Proposition 6.3). Given vectors $x^1, \dots, x^m \in D^k$, let $y^1, \dots, y^k \in D^m$ with $y^i_j = x^j_i$, and for a set $S$ of functions $D^m \to D$ let $\{(f(y^1), \dots, f(y^k)) : f \in S\}$; with $S = S_m$ and $S = T_m$ this gives $S'_m$ and $T'_m$ (proof of Theorem 6.1).
--
--   These objects are shared by every statement of the mission.
--
--   **Formalization Note** The family $\Gamma$ is a pair `𝔸 𝔹 : RelStruct τ ar D` from the published `PCSPBLPAff_Symmetric_Setting`, with $P_R$ = `𝔸.rel R`, $Q_R$ = `𝔹.rel R`; `IsPolymorphism 𝔸 𝔹 f` is Definition 2.4 for the family, and `IsPolymorphism 𝔸 𝔸 f` is $f \in \mathrm{Pol}(P_R, P_R)$ for all $R$. `PolSubset` quantifies over every arity `L : ℕ`, **including $L = 0$** (constant functions); the paper never restricts the arity, and with arities $L \ge 1$ only the main theorem would be false (for $\Gamma = \{(D, D)\}$ and $\Gamma' = \{(\emptyset, \emptyset)\}$ unary). A $\Gamma \cup \{\mathrm{EQUAL}\}$-PCSP is an `Instance` of the published file over the signature `τ ⊕ Unit`, where the new symbol has arity $2$ and is read as EQUAL in both structures (`withEqual`). `PPPDefinable` asks for an instance with `Ψ.n = k + ℓ` (carried as an equation); the first $k$ variables are `Fin.castAdd ℓ`, and $(x, y)$ is `Fin.append x y`. Coordinates and variables are $0$-based. A set of functions $D^L \to D$ is turned into a relation of arity `Fintype.card (Fin L → D)` $= |D|^L$ through a chosen bijection `e : Fin N ≃ (Fin L → D)` (`asTuples`). `evalAt x S` is $\{(f(y^1), \dots, f(y^k)) : f \in S\}$ with $y^i_j$ = `x j i`.
-- source:
--   J. Brakensiek, V. Guruswami, Promise Constraint Satisfaction: Algebraic Structure and a Symmetric Boolean Dichotomy, arXiv:1704.01937v2, pp. 8–9 and 27–28, Definitions 2.1, 2.2, 2.4, the relation EQUAL and Definition 6.2 (p. 27), Proposition 6.3 and the proof of Theorem 6.1 (p. 28)

import Mathlib
import Definitions.Def_PCSPBLPAff_Symmetric_Setting

namespace SymBoolPCSP.Galois

open PCSPBLPAff.Symmetric

/-! ### Promise families, polymorphism inclusion and ppp-definability (§2.1, §6.1)

A family `Γ = {(P_R, Q_R) : R ∈ τ}` of promise relations over a finite domain `D` is a pair of
structures `𝔸 𝔹 : RelStruct τ ar D` with `P_R = 𝔸.rel R` and `Q_R = 𝔹.rel R`
(Definitions 2.1–2.2, p. 8). Its polymorphisms are `IsPolymorphism 𝔸 𝔹` (Definition 2.4, p. 9).
Coordinates and variables are 0-based (`Fin k`), the paper's are 1-based. -/

/-- `Γ = (𝔸, 𝔹)` is a family of promise relations: `P_R ⊆ Q_R` for every symbol `R`
(Definition 2.1, p. 8). -/
def IsPromiseFamily {τ : Type} {ar : τ → ℕ} {D : Type} (𝔸 𝔹 : RelStruct τ ar D) : Prop :=
  ∀ R : τ, 𝔸.rel R ⊆ 𝔹.rel R

/-- `Pol(Γ) ⊆ Pol(Γ′)`: every polymorphism of `Γ = (𝔸, 𝔹)`, of every arity `L ≥ 0`
(nullary functions included), is a polymorphism of `Γ′ = (𝔸', 𝔹')` (Definition 2.4, p. 9;
Theorem 6.1, p. 27). -/
def PolSubset {τ τ' : Type} {ar : τ → ℕ} {ar' : τ' → ℕ} {D : Type}
    (𝔸 𝔹 : RelStruct τ ar D) (𝔸' 𝔹' : RelStruct τ' ar' D) : Prop :=
  ∀ (L : ℕ) (f : (Fin L → D) → D), IsPolymorphism 𝔸 𝔹 f → IsPolymorphism 𝔸' 𝔹' f

/-- Arities of the signature `τ ⊕ Unit` of `Γ ∪ {EQUAL}`: the new symbol `inr ()` is the binary
relation EQUAL. -/
def arEq {τ : Type} (ar : τ → ℕ) : τ ⊕ Unit → ℕ
  | .inl R => ar R
  | .inr _ => 2

/-- The structure `𝔸` extended by `EQUAL = {(i, i) : i ∈ D}` (p. 27) on the symbol `inr ()`. -/
def withEqual {τ : Type} {ar : τ → ℕ} {D : Type} (𝔸 : RelStruct τ ar D) :
    RelStruct (τ ⊕ Unit) (arEq ar) D where
  rel
    | .inl R => 𝔸.rel R
    | .inr _ => {t | t (0 : Fin 2) = t (1 : Fin 2)}

/-- The assignment `σ` of the variables of `X` satisfies every clause of `X` read in `𝔸`
(`Ψ_P(σ) = 1` when `𝔸` holds the `P`-relations, `Ψ_Q(σ) = 1` when it holds the `Q`-relations;
Definition 2.2, p. 8). -/
def Satisfies {τ : Type} {ar : τ → ℕ} {D : Type} (X : Instance τ ar) (𝔸 : RelStruct τ ar D)
    (σ : Fin X.n → D) : Prop :=
  ∀ j : Fin X.m, σ ∘ X.scope j ∈ 𝔸.rel (X.sym j)

/-- **Definition 6.2** (p. 27). The promise relation `(P', Q') ⊆ D^k × D^k` is ppp-definable from
`Γ = (𝔸, 𝔹)`: there are `ℓ` and one `Γ ∪ {EQUAL}`-PCSP `Ψ` on `k + ℓ` variables (the first `k`
being `x_1, …, x_k`), read as `Ψ_P` in `𝔸 ∪ {EQUAL}` and as `Ψ_Q` in `𝔹 ∪ {EQUAL}`, such that
* every `x ∈ P'` extends by some `y ∈ D^ℓ` to a satisfying assignment `(x, y)` of `Ψ_P`;
* every satisfying assignment `z` of `Ψ_Q` has `(z_1, …, z_k) ∈ Q'`.
`Ψ.n = k + ℓ` is carried as the equation `h`; `(x, y)` is `Fin.append x y`. -/
def PPPDefinable {τ : Type} {ar : τ → ℕ} {D : Type} (𝔸 𝔹 : RelStruct τ ar D) {k : ℕ}
    (P' Q' : Set (Fin k → D)) : Prop :=
  ∃ (ℓ : ℕ) (Ψ : Instance (τ ⊕ Unit) (arEq ar)) (h : Ψ.n = k + ℓ),
    (∀ x ∈ P', ∃ y : Fin ℓ → D,
      Satisfies Ψ (withEqual 𝔸) (fun v => Fin.append x y (Fin.cast h v))) ∧
    (∀ z : Fin Ψ.n → D, Satisfies Ψ (withEqual 𝔹) z →
      (fun i : Fin k => z (Fin.cast h.symm (Fin.castAdd ℓ i))) ∈ Q')

/-- The one-relation family `{(P, Q)}` on the symbol `()`, used for "ppp-definable from
`(P, Q)`" (p. 27). `single P` is its `P`-structure, `single Q` its `Q`-structure. -/
def single {D : Type} {k : ℕ} (P : Set (Fin k → D)) : RelStruct Unit (fun _ => k) D :=
  ⟨fun _ => P⟩

/-! ### The relations `S_L ⊆ T_L` (Proposition 6.3, p. 28) and `S′_m ⊆ T′_m` (p. 28) -/

/-- `S_L = {f : D^L → D : f ∈ Pol(P, P) for all (P, Q) ∈ Γ}` (Proposition 6.3, p. 28). -/
def SL {τ : Type} {ar : τ → ℕ} {D : Type} (𝔸 : RelStruct τ ar D) (L : ℕ) :
    Set ((Fin L → D) → D) :=
  {f | IsPolymorphism 𝔸 𝔸 f}

/-- `T_L = {f : D^L → D : f ∈ Pol(P, Q) for all (P, Q) ∈ Γ}` (Proposition 6.3, p. 28). -/
def TL {τ : Type} {ar : τ → ℕ} {D : Type} (𝔸 𝔹 : RelStruct τ ar D) (L : ℕ) :
    Set ((Fin L → D) → D) :=
  {f | IsPolymorphism 𝔸 𝔹 f}

/-- A set `S` of functions `f : D^L → D`, viewed as a relation of arity `N = |D|^L` by listing
the values of `f` in the order `e : Fin N ≃ D^L` ("we identify a function `f` as a vector of
`|D|^L` variables", p. 28). -/
def asTuples {D : Type} {L N : ℕ} (e : Fin N ≃ (Fin L → D)) (S : Set ((Fin L → D) → D)) :
    Set (Fin N → D) :=
  {t | (fun a => t (e.symm a)) ∈ S}

/-- The vectors `y_1, …, y_k ∈ D^m` with `(y_i)_j = (x^j)_i`, built from `x^1, …, x^m ∈ D^k`
(proof of Theorem 6.1, p. 28). -/
def yvec {D : Type} {k m : ℕ} (x : Fin m → Fin k → D) (i : Fin k) : Fin m → D :=
  fun j => x j i

/-- `{(f(y_1), …, f(y_k)) : f ∈ S}` for a set `S` of functions `D^m → D`; with `S = S_m` this is
`S′_m`, with `S = T_m` it is `T′_m` (proof of Theorem 6.1, p. 28). -/
def evalAt {D : Type} {k m : ℕ} (x : Fin m → Fin k → D) (S : Set ((Fin m → D) → D)) :
    Set (Fin k → D) :=
  {t | ∃ f ∈ S, t = fun i => f (yvec x i)}

end SymBoolPCSP.Galois


