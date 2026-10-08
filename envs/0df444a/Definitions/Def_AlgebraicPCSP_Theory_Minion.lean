-- Prove2me | Definitions.Def_AlgebraicPCSP_Theory_Minion
-- name    : AlgebraicPCSP_Theory_Minion
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-08T00:19:21.436984+00:00
-- url     : https://prove2.me/theorems/e8e9d655-2543-4939-8ca9-765e90f60f93
-- title:
--   Minors, minions, Pol(A, B), the projection minion and minion homomorphisms (Definitions 2.15, 2.16, 2.19–2.21)
-- statement:
--   Fix two sets $A$ and $B$ and let $\mathcal O(A,B)=\{f:A^n\to B\mid n\ge 1\}$ be the set of all functions from a finite power of $A$ to $B$; nullary functions are excluded.
--
--   **Minors (Definition 2.19).** An $n$-ary function $f:A^n\to B$ is the *minor* of an $m$-ary function $g:A^m\to B$ given by a map $\pi:[m]\to[n]$ if
--   $$f(x_1,\dots,x_n)=g(x_{\pi(1)},\dots,x_{\pi(m)})\qquad\text{for all }x_1,\dots,x_n\in A.$$
--
--   **Minions (Definition 2.20).** A (function) *minion* $\mathcal M$ on $(A,B)$ is a nonempty subset of $\mathcal O(A,B)$ that is closed under taking minors. $\mathcal M^{(n)}$ denotes its $n$-ary members.
--
--   **Polymorphisms (Definition 2.15).** For similar relational structures $\mathbf A$, $\mathbf B$, an $n$-ary function $f:A^n\to B$ is a *polymorphism* from $\mathbf A$ to $\mathbf B$ if for every relation symbol $R$ and all tuples $\mathbf a^1,\dots,\mathbf a^n\in R^{\mathbf A}$ the tuple obtained by applying $f$ coordinatewise, $\big(f(a^1_1,\dots,a^n_1),\dots,f(a^1_{k},\dots,a^n_{k})\big)$, lies in $R^{\mathbf B}$. The polymorphisms of positive arity form the family $\mathrm{Pol}(\mathbf A,\mathbf B)$. When $(\mathbf A,\mathbf B)$ is a PCSP template, i.e. there is a homomorphism $\sigma:\mathbf A\to\mathbf B$, this family is a minion: it is closed under minors, and it contains the unary polymorphism $x\mapsto\sigma(x)$.
--
--   **Projections (Definition 2.16).** The minion $\mathcal P_A$ on $(A,A)$ consists of all projections $p^{(n)}_i(x_1,\dots,x_n)=x_i$, $n\ge1$, $i\in[n]$.
--
--   **Minion homomorphisms (Definition 2.21).** For minions $\mathcal M$ on $(A,B)$ and $\mathcal N$ on $(A',B')$, a map $\xi:\mathcal M\to\mathcal N$ is a *minion homomorphism* if it preserves arities and minors: for every $\pi:[m]\to[n]$ and every $g\in\mathcal M^{(m)}$,
--   $$\xi\big(g(x_{\pi(1)},\dots,x_{\pi(m)})\big)=\xi(g)(x_{\pi(1)},\dots,x_{\pi(m)}).$$
--
--   These are the algebraic objects of the paper's general theory: the existence of a minion homomorphism $\mathrm{Pol}(\mathbf A_1,\mathbf B_1)\to\mathrm{Pol}(\mathbf A_2,\mathbf B_2)$ is what Theorem 4.12 characterizes.
--
--   **Formalization Note** A minion is a structure carrying the family $n\mapsto\mathcal M^{(n)}$ of sets of functions $(\mathrm{Fin}\,n\to A)\to B$, with the axioms that $\mathcal M^{(0)}=\emptyset$, that some member exists, and closure under minors, where the minor along $\pi$ is `fun x => g (x ∘ π)`. `polFamily 𝔸 𝔹 n` is the set of $n$-ary polymorphisms with $n\ge1$ (the polymorphism condition is the one of the referenced `PCSPBLPAff.Symmetric.IsPolymorphism`, where the tuples of $R^{\mathbf A}$ are the rows of a matrix and $f$ is applied to its columns, the transpose of the paper's picture). `Pol 𝔸 𝔹 h` packages it as a minion given the template hypothesis `h`. A minion homomorphism is a family of maps $\xi_n:\mathcal M^{(n)}\to\mathcal N^{(n)}$ on the members themselves, so arity preservation is part of its type and no values outside $\mathcal M$ occur.
-- source:
--   L. Barto, J. Bulín, A. Krokhin, J. Opršal, Algebraic approach to promise constraint satisfaction, arXiv:1811.00970v3, pp. 12–13, Definitions 2.15, 2.16, 2.19, 2.20, 2.21

import Mathlib
import Definitions.Def_PCSPBLPAff_Symmetric_Setting

namespace AlgebraicPCSP.Theory

open PCSPBLPAff.Symmetric

/-- A (function) minion on the pair of sets `(A, B)` (Definition 2.20, p. 13): a nonempty
family of functions `Aⁿ → B`, `n ≥ 1`, closed under taking minors. `mem n` is the set
`M⁽ⁿ⁾` of its `n`-ary members. There are no nullary members (`O(A, B)` contains only
arities `n ≥ 1`). The minor of `g : Aᵐ → B` given by `π : [m] → [n]` is the `n`-ary
function `f(x₁, …, xₙ) = g(x_{π(1)}, …, x_{π(m)})` (Definition 2.19, p. 12), i.e.
`fun x => g (x ∘ π)`. -/
structure Minion (A B : Type) where
  /-- The `n`-ary members `M⁽ⁿ⁾`. -/
  mem : (n : ℕ) → Set ((Fin n → A) → B)
  /-- No nullary functions: `O(A, B)` consists of the functions of arity `n ≥ 1`. -/
  mem_zero : mem 0 = ∅
  /-- A minion is nonempty. -/
  nonempty : ∃ (n : ℕ) (f : (Fin n → A) → B), f ∈ mem n
  /-- Closure under minors: if `g ∈ M⁽ᵐ⁾` and `π : [m] → [n]` then
  `(x₁, …, xₙ) ↦ g(x_{π(1)}, …, x_{π(m)})` is in `M⁽ⁿ⁾`. -/
  minor_mem : ∀ {m n : ℕ} (π : Fin m → Fin n) (g : (Fin m → A) → B),
    g ∈ mem m → (fun x : Fin n → A => g (x ∘ π)) ∈ mem n

/-- The family of all polymorphisms from `𝔸` to `𝔹` (Definition 2.15, p. 12), of arity
`n ≥ 1`: `polFamily 𝔸 𝔹 n` is the set `Pol⁽ⁿ⁾(𝔸, 𝔹)`. -/
def polFamily {τ : Type} {ar : τ → ℕ} {A B : Type} (𝔸 : RelStruct τ ar A)
    (𝔹 : RelStruct τ ar B) : (n : ℕ) → Set ((Fin n → A) → B) :=
  fun n => {f | 0 < n ∧ IsPolymorphism 𝔸 𝔹 f}

/-- The polymorphism minion `Pol(𝔸, 𝔹)` of a PCSP template `(𝔸, 𝔹)` (Definitions 2.15 and
2.20, pp. 12–13). Nonemptiness uses the homomorphism `σ : 𝔸 → 𝔹`: `x ↦ σ(x₁)` is a unary
polymorphism. -/
def Pol {τ : Type} {ar : τ → ℕ} {A B : Type} (𝔸 : RelStruct τ ar A) (𝔹 : RelStruct τ ar B)
    (h : IsPromiseTemplate 𝔸 𝔹) : Minion A B where
  mem := polFamily 𝔸 𝔹
  mem_zero := by
    ext f
    simp [polFamily]
  nonempty := by
    obtain ⟨σ, hσ⟩ := h
    refine ⟨1, fun x => σ (x 0), Nat.one_pos, ?_⟩
    intro R M hM
    exact hσ R (M 0) (hM 0)
  minor_mem := by
    intro m n π g hg
    obtain ⟨hm, hpol⟩ := hg
    refine ⟨Fin.pos (π ⟨0, hm⟩), ?_⟩
    intro R M hM
    exact hpol R (fun l => M (π l)) (fun l => hM (π l))

/-- The minion `P_A` of all projections (dictators) `p_i⁽ⁿ⁾(x₁, …, xₙ) = xᵢ` on a set `A`
(Definitions 2.16, p. 12, and 3.2, p. 15). -/
def projMinion (A : Type) : Minion A A where
  mem n := {f | ∃ i : Fin n, f = fun x => x i}
  mem_zero := by
    ext f
    simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false]
    rintro ⟨i, -⟩
    exact i.elim0
  nonempty := ⟨1, fun x => x 0, 0, rfl⟩
  minor_mem := by
    rintro m n π g ⟨i, rfl⟩
    exact ⟨π i, rfl⟩

/-- A minion homomorphism `ξ : M → N` (Definition 2.21, p. 13). `ξ` maps each `m`-ary member
of `M` to an `m`-ary member of `N` (arity preservation is built into the type), and it
preserves minors: for every `π : [m] → [n]` and every `g ∈ M⁽ᵐ⁾`,
`ξ(g(x_{π(1)}, …, x_{π(m)})) = ξ(g)(x_{π(1)}, …, x_{π(m)})`. -/
def IsMinionHom {A B A' B' : Type} (M : Minion A B) (N : Minion A' B')
    (ξ : (n : ℕ) → {f // f ∈ M.mem n} → {f // f ∈ N.mem n}) : Prop :=
  ∀ {m n : ℕ} (π : Fin m → Fin n) (g : (Fin m → A) → B) (hg : g ∈ M.mem m),
    (ξ n ⟨fun x => g (x ∘ π), M.minor_mem π g hg⟩).val =
      fun x : Fin n → A' => (ξ m ⟨g, hg⟩).val (x ∘ π)

end AlgebraicPCSP.Theory


