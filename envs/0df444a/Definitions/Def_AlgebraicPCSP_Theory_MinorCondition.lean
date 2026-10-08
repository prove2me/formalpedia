-- Prove2me | Definitions.Def_AlgebraicPCSP_Theory_MinorCondition
-- name    : AlgebraicPCSP_Theory_MinorCondition
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-08T00:20:20.261392+00:00
-- url     : https://prove2.me/theorems/fa17c9be-8a6b-4997-b39d-cd7a80fcf3e6
-- title:
--   Bipartite minor conditions, triviality, the condition Σ(A, I) and the free structure F_M(A) (Definition 3.2, §3.2, Definition 4.1)
-- statement:
--   **Bipartite minor conditions (Definition 3.2).** Let $\mathcal U$ and $\mathcal V$ be disjoint finite sets of function symbols, each with an arity. A *bipartite minor condition* $\Sigma$ over $\mathcal U$ and $\mathcal V$ is a finite set of identities
--   $$f(x_1,\dots,x_n)\approx g(x_{\pi(1)},\dots,x_{\pi(m)}),$$
--   with $f\in\mathcal U$ of arity $n$, $g\in\mathcal V$ of arity $m$, and $\pi:[m]\to[n]$. It is *satisfied* in a minion $\mathcal M$ on $(A,B)$ (more generally, in any set of functions $\mathcal M\subseteq\mathcal O(A,B)$) if there is an assignment $\zeta$ of a member of $\mathcal M$ of the right arity to each symbol of $\mathcal U\cup\mathcal V$ such that $\zeta(f)(a_1,\dots,a_n)=\zeta(g)(a_{\pi(1)},\dots,a_{\pi(m)})$ for each identity and all $a_1,\dots,a_n\in A$. It is *trivial* if it is satisfied in the projection minion $\mathcal P_{\{0,1\}}$; the paper defines triviality as satisfaction in every minion and notes that this is equivalent to satisfaction in $\mathcal P_A$ for any $A$ with $|A|\ge2$.
--
--   **The condition $\Sigma(\mathbf A,\mathbf I)$ (§3.2, p. 19).** Let $\mathbf A$ and $\mathbf I$ be similar finite structures, fix an enumeration $A=\{a_1,\dots,a_n\}$, and for each symbol $R$ an enumeration $R^{\mathbf A}=\{\mathbf r_1,\dots,\mathbf r_m\}$, $m=|R^{\mathbf A}|$. Then $\mathcal U=\{f_v\mid v\in I\}$, each of arity $n$; $\mathcal V$ has one symbol $g_C$ of arity $m=|R^{\mathbf A}|$ for each constraint $C=((v_1,\dots,v_k),R)$, i.e. each tuple $(v_1,\dots,v_k)\in R^{\mathbf I}$; and for each such $C$ and each $i\in[k]$, $\Sigma$ contains
--   $$f_{v_i}(x_1,\dots,x_n)\approx g_C(x_{\pi_i(1)},\dots,x_{\pi_i(m)}),$$
--   where $a_{\pi_i(j)}$ is the $i$-th entry of the $j$-th tuple $\mathbf r_j$ of $R^{\mathbf A}$.
--
--   **The free structure $F_{\mathcal M}(\mathbf A)$ (Definition 4.1).** For a minion $\mathcal M$ and a finite structure $\mathbf A$ with $A$ identified with $[n]$, $F_{\mathcal M}(\mathbf A)$ is the structure similar to $\mathbf A$ with universe $\mathcal M^{(n)}$, in which a $k$-tuple $(f_1,\dots,f_k)$ belongs to $R^{F}$ iff there is an $m$-ary $g\in\mathcal M$, $m=|R^{\mathbf A}|$, with
--   $$f_i(x_1,\dots,x_n)=g(x_{\mathbf r_1(i)},\dots,x_{\mathbf r_m(i)})\qquad\text{for each } i=1,\dots,k.$$
--
--   $\Sigma(\mathbf A,\mathbf I)$ turns an instance of $\mathrm{PCSP}(\mathbf A,\mathbf B)$ into a minor condition, and the free structure is the most general target of a minion homomorphism from $\mathcal M$; both appear in items (3) and (4) of Theorem 4.12.
--
--   **Formalization Note** A condition is a structure with finite types $U$, $V$ of symbols and a finite index type of identities, each identity giving its left symbol, right symbol and map $\pi$. Satisfaction is defined for an arbitrary family $n\mapsto\mathcal M^{(n)}$ (`SatisfiedIn`), as the paper allows on p. 35, and `Minion.Satisfies` applies it to a minion. The enumeration of $A$ is an explicit equivalence $e:\mathrm{Fin}\,n\simeq A$ ($a_i=e(i)$), and the enumeration of each $R^{\mathbf A}$ is an explicit equivalence $\mathrm{Fin}\,(m_R)\simeq R^{\mathbf A}$; both constructions depend on these choices, exactly as in the paper. The index $\pi_i(j)$, resp. $\mathbf r_j(i)$ read as an element of $[n]$, is $e^{-1}(\mathbf r_j(i))$. The universe of $F_{\mathcal M}(\mathbf A)$ is the subtype of $n$-ary members of $\mathcal M$. A symbol of arity $0$ in $\Sigma(\mathbf A,\mathbf I)$ (when $R^{\mathbf A}=\emptyset$ or $A=\emptyset$) can be assigned nothing, since minions have no nullary members; this is also the case in the paper.
-- source:
--   L. Barto, J. Bulín, A. Krokhin, J. Opršal, Algebraic approach to promise constraint satisfaction, arXiv:1811.00970v3, p. 15 (Definition 3.2), p. 19 (§3.2, construction of Σ(A, I)), p. 23 (Definition 4.1)

import Mathlib
import Definitions.Def_PCSPBLPAff_Symmetric_Setting
import Definitions.Def_AlgebraicPCSP_Theory_Minion

namespace AlgebraicPCSP.Theory

open PCSPBLPAff.Symmetric

/-- A bipartite minor condition `Σ` over disjoint sets of function symbols `U` and `V`
(Definition 3.2, p. 15). Symbols `u ∈ U` have arity `arU u`, symbols `v ∈ V` have arity
`arV v`. The identities are indexed by the finite type `Idx`: identity `e` reads
`f(x₁, …, xₙ) ≈ g(x_{π(1)}, …, x_{π(m)})` with `f = lhs e ∈ U` of arity `n`,
`g = rhs e ∈ V` of arity `m` and `π = map e : [m] → [n]`. `U`, `V` and the set of identities
are finite. -/
structure BipartiteMinorCondition where
  /-- The left-hand function symbols. -/
  U : Type
  /-- The right-hand function symbols. -/
  V : Type
  /-- Index set of the identities. -/
  Idx : Type
  [finU : Finite U]
  [finV : Finite V]
  [finIdx : Finite Idx]
  /-- Arities of the symbols in `U`. -/
  arU : U → ℕ
  /-- Arities of the symbols in `V`. -/
  arV : V → ℕ
  /-- The left-hand symbol `f` of each identity. -/
  lhs : Idx → U
  /-- The right-hand symbol `g` of each identity. -/
  rhs : Idx → V
  /-- The map `π : [m] → [n]` of each identity `f(x₁, …, xₙ) ≈ g(x_{π(1)}, …, x_{π(m)})`. -/
  map : (e : Idx) → Fin (arV (rhs e)) → Fin (arU (lhs e))

/-- `Σ` is satisfied in a set of functions `M = ⋃ₙ M⁽ⁿ⁾ ⊆ O(A, B)` (Definition 3.2, p. 15; the
definition makes sense for an arbitrary subset of `O(A, B)`, p. 35): there is an assignment
`ζ` of a member of `M` of the right arity to every symbol of `U ∪ V` such that
`ζ(f)(a₁, …, aₙ) = ζ(g)(a_{π(1)}, …, a_{π(m)})` for each identity and all `a₁, …, aₙ ∈ A`. -/
def SatisfiedIn {A B : Type} (S : BipartiteMinorCondition)
    (M : (n : ℕ) → Set ((Fin n → A) → B)) : Prop :=
  ∃ (ζU : (u : S.U) → (Fin (S.arU u) → A) → B) (ζV : (v : S.V) → (Fin (S.arV v) → A) → B),
    (∀ u, ζU u ∈ M (S.arU u)) ∧ (∀ v, ζV v ∈ M (S.arV v)) ∧
    ∀ e : S.Idx, ζU (S.lhs e) = fun x => ζV (S.rhs e) (x ∘ S.map e)

/-- A minion `M` satisfies `Σ` (Definition 3.2, p. 15). -/
def Minion.Satisfies {A B : Type} (M : Minion A B) (S : BipartiteMinorCondition) : Prop :=
  SatisfiedIn S M.mem

/-- `Σ` is trivial (Definition 3.2, p. 15): it is satisfied in the minion `P_{\{0,1\}}` of all
projections on a two-element set. The paper defines triviality as satisfaction in every minion
and notes that this is equivalent to satisfaction in `P_A` for any `A` with `|A| ≥ 2`. -/
def IsTrivial (S : BipartiteMinorCondition) : Prop :=
  (projMinion (Fin 2)).Satisfies S

/-- The constraints `C = ((v₁, …, v_k), R)` of an instance `𝕀`, i.e. the pairs of a relation
symbol `R` and a tuple `(v₁, …, v_k) ∈ R^𝕀`. -/
abbrev Constraint {τ : Type} {ar : τ → ℕ} {I : Type} (𝕀 : RelStruct τ ar I) : Type :=
  (R : τ) × 𝕀.rel R

/-- The bipartite minor condition `Σ(𝔸, 𝕀)` (§3.2, p. 19). The enumeration
`A = {a₁, …, aₙ}` is `e : Fin n ≃ A` (`aᵢ = e i`), and for each symbol `R` the list
`r₁, …, r_m` of all tuples of `R^𝔸` (`m = |R^𝔸|`) is `eR R : Fin (m R) ≃ R^𝔸` (`r_j = eR R j`).
* `U` is the set of symbols `f_v`, `v ∈ I`, each of arity `n = |A|`;
* `V` is the set of symbols `g_C`, one for each constraint `C = ((v₁, …, v_k), R)` of `𝕀`, of
  arity `m = |R^𝔸|`;
* for each constraint `C` and each `i ∈ [k]` there is the identity
  `f_{vᵢ}(x₁, …, xₙ) ≈ g_C(x_{πᵢ(1)}, …, x_{πᵢ(m)})`, where `a_{πᵢ(j)}` is the `i`-th entry of
  the `j`-th tuple `r_j` of `R^𝔸`, i.e. `πᵢ(j) = e⁻¹(r_j(i))`. -/
noncomputable def sigmaCondition {τ : Type} [Finite τ] {ar : τ → ℕ} {A I : Type} [Finite I]
    (𝔸 : RelStruct τ ar A) (𝕀 : RelStruct τ ar I) {n : ℕ} (e : Fin n ≃ A) (m : τ → ℕ)
    (eR : (R : τ) → Fin (m R) ≃ 𝔸.rel R) : BipartiteMinorCondition where
  U := I
  V := Constraint 𝕀
  Idx := (C : Constraint 𝕀) × Fin (ar C.1)
  arU := fun _ => n
  arV := fun C => m C.1
  lhs := fun p => p.1.2.val p.2
  rhs := fun p => p.1
  map := fun p j => e.symm ((eR p.1.1 j).val p.2)

/-- The free structure `F_M(𝔸)` of a minion `M` generated by `𝔸` (Definition 4.1, p. 23).
The paper assumes `A = [n]`; here `A` is identified with `[n]` through the enumeration
`e : Fin n ≃ A`, and `R^𝔸 = {r₁, …, r_m}` through `eR R : Fin (m R) ≃ R^𝔸`. The universe is
`M⁽ⁿ⁾`, the `n`-ary members of `M`. A `k`-tuple `(f₁, …, f_k)` is in `R^F` iff there is an
`m`-ary `g ∈ M` with `fᵢ(x₁, …, xₙ) = g(x_{r₁(i)}, …, x_{r_m(i)})` for each `i = 1, …, k`, the
index of `r_j(i) ∈ A` taken through `e`. -/
def freeStructure {τ : Type} {ar : τ → ℕ} {A C D : Type} (M : Minion C D)
    (𝔸 : RelStruct τ ar A) {n : ℕ} (e : Fin n ≃ A) (m : τ → ℕ)
    (eR : (R : τ) → Fin (m R) ≃ 𝔸.rel R) : RelStruct τ ar {f // f ∈ M.mem n} where
  rel R := {t | ∃ g ∈ M.mem (m R), ∀ i : Fin (ar R),
    (t i).val = fun x : Fin n → C => g (fun j => x (e.symm ((eR R j).val i)))}

end AlgebraicPCSP.Theory


