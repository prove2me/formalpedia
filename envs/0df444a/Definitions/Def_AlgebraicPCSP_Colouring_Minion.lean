-- Prove2me | Definitions.Def_AlgebraicPCSP_Colouring_Minion
-- name    : AlgebraicPCSP_Colouring_Minion
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-07T23:11:44.964276+00:00
-- url     : https://prove2.me/theorems/8e11aafb-b1fc-47a6-8b33-1a783b1c692b
-- title:
--   Minor, minion, minion homomorphism, Pol(A, B) (Definitions 2.15, 2.19–2.21)
-- statement:
--   This module fixes the minion vocabulary of §2.2 of Barto, Bulín, Krokhin and Opršal.
--
--   1. **Minors** (Definition 2.19). An $n$-ary function $f : A^n \to B$ is the *minor* of an $m$-ary function $g : A^m \to B$ given by a map $\pi : [m] \to [n]$ if
--   $$
--   f(x_1, \dots, x_n) = g(x_{\pi(1)}, \dots, x_{\pi(m)}) \quad\text{for all } x_1, \dots, x_n \in A .
--   $$
--   2. **Minions** (Definition 2.20). Let $\mathcal O(A, B) = \{ f : A^n \to B \mid n \ge 1 \}$. A (function) *minion* $\mathscr M$ on the pair of sets $(A, B)$ is a nonempty subset of $\mathcal O(A, B)$ closed under taking minors; $\mathscr M^{(n)}$ denotes its $n$-ary members. There are no nullary members.
--   3. **Minion homomorphisms** (Definition 2.21). For minions $\mathscr M$ on $(A, B)$ and $\mathscr N$ on $(A', B')$, a map $\xi : \mathscr M \to \mathscr N$ is a *minion homomorphism* if it preserves arities and minors: for every $\pi : [m] \to [n]$ and every $g \in \mathscr M^{(m)}$,
--   $$
--   \xi(g)(x_{\pi(1)}, \dots, x_{\pi(m)}) = \xi\big(g(x_{\pi(1)}, \dots, x_{\pi(m)})\big).
--   $$
--   4. **Polymorphism minions** (Definition 2.15). For a PCSP template $(\mathbf A, \mathbf B)$, i.e. two similar relational structures with a homomorphism $\mathbf A \to \mathbf B$, the set $\mathrm{Pol}(\mathbf A, \mathbf B)$ of all polymorphisms from $\mathbf A$ to $\mathbf B$ of arity $n \ge 1$ is a minion.
--
--   These notions carry the whole mission: Theorem 6.2 characterises the minions that admit a minion homomorphism to $\mathrm{Pol}(\mathbf H_2, \mathbf H_K)$, and the goal is an instance of it.
--
--   **Formalization Note** A minion is a structure with a family `mem n` of $n$-ary functions `(Fin n → A) → B`, the axiom `mem 0 = ∅` (arities $n \ge 1$), nonemptiness, and closure under minors, where the minor of `g` by `π : Fin m → Fin n` is `fun x => g (x ∘ π)`. A minion homomorphism is a family `ξ n` of maps between $n$-ary functions, so arities are preserved by construction; the condition is that `ξ` sends `M.mem n` into `N.mem n` and commutes with minors on members of `M`. Values of `ξ` on functions outside `M` are unconstrained. `Pol 𝔸 𝔹 h` takes the homomorphism witness `h` only to prove nonemptiness; its members do not depend on `h`. Polymorphisms are the published `IsPolymorphism`, which applies `f` to the columns of an $n \times \mathrm{ar}(R)$ matrix whose rows lie in $R^{\mathbf A}$ (the paper's matrix, transposed).
-- source:
--   L. Barto, J. Bulín, A. Krokhin, J. Opršal, Algebraic approach to promise constraint satisfaction, arXiv:1811.00970v3, pp. 12–13, Definitions 2.15, 2.19, 2.20, 2.21

import Mathlib
import Definitions.Def_PCSPBLPAff_Symmetric_Setting

namespace AlgebraicPCSP.Colouring

open PCSPBLPAff.Symmetric

/-- A (function) minion on the pair of sets `(A, B)` (Definitions 2.19–2.20, arXiv:1811.00970v3,
pp. 12–13): a nonempty subset of `O(A, B) = {f : Aⁿ → B | n ≥ 1}` closed under taking minors.
`mem n` is the set `M⁽ⁿ⁾` of its `n`-ary members; there are no nullary members. The minor of an
`m`-ary `g` given by `π : [m] → [n]` is the `n`-ary `f(x₁, …, xₙ) = g(x_{π(1)}, …, x_{π(m)})`,
i.e. `fun x => g (x ∘ π)`. -/
structure Minion (A B : Type) where
  /-- `M⁽ⁿ⁾`, the `n`-ary functions of the minion. -/
  mem : (n : ℕ) → Set ((Fin n → A) → B)
  /-- Only arities `n ≥ 1` occur. -/
  mem_zero : mem 0 = ∅
  /-- The minion is nonempty. -/
  nonempty : ∃ (n : ℕ) (f : (Fin n → A) → B), f ∈ mem n
  /-- Closure under minors. -/
  minor_closed : ∀ {m n : ℕ} (π : Fin m → Fin n) (g : (Fin m → A) → B),
    g ∈ mem m → (fun x => g (x ∘ π)) ∈ mem n

/-- A minion homomorphism `ξ : M → N` (Definition 2.21, p. 13), given as a family of maps
`ξ n` sending `n`-ary functions on `(A, B)` to `n`-ary functions on `(A', B')`, so that arities
are preserved by construction. It maps `M⁽ⁿ⁾` into `N⁽ⁿ⁾` and preserves minors:
`ξ(g)(x_{π(1)}, …, x_{π(m)}) = ξ(g(x_{π(1)}, …, x_{π(m)}))` for every `π : [m] → [n]` and every
`g ∈ M⁽ᵐ⁾`. Values of `ξ` outside `M` are irrelevant and unconstrained. -/
def IsMinionHom {A B A' B' : Type} (M : Minion A B) (N : Minion A' B')
    (ξ : (n : ℕ) → ((Fin n → A) → B) → ((Fin n → A') → B')) : Prop :=
  (∀ (n : ℕ) (f : (Fin n → A) → B), f ∈ M.mem n → ξ n f ∈ N.mem n) ∧
  (∀ (m n : ℕ) (π : Fin m → Fin n) (g : (Fin m → A) → B), g ∈ M.mem m →
    ξ n (fun x => g (x ∘ π)) = fun x => ξ m g (x ∘ π))

/-- The minion `Pol(𝔸, 𝔹)` of all polymorphisms of arity `n ≥ 1` from `𝔸` to `𝔹`
(Definition 2.15, p. 12), for a PCSP template `(𝔸, 𝔹)` (Definition 2.5, p. 9: there is a
homomorphism `𝔸 → 𝔹`, which makes `Pol(𝔸, 𝔹)` nonempty). -/
def Pol {τ : Type} {ar : τ → ℕ} {A B : Type} (𝔸 : RelStruct τ ar A) (𝔹 : RelStruct τ ar B)
    (h : IsPromiseTemplate 𝔸 𝔹) : Minion A B where
  mem n := {f | 0 < n ∧ IsPolymorphism 𝔸 𝔹 f}
  mem_zero := by
    ext f
    simp
  nonempty := by
    obtain ⟨σ, hσ⟩ := h
    refine ⟨1, fun x => σ (x 0), Nat.one_pos, ?_⟩
    intro R M hM
    exact hσ R (M 0) (hM 0)
  minor_closed := by
    intro m n π g hg
    obtain ⟨hm, hpol⟩ := hg
    refine ⟨Nat.pos_of_ne_zero fun hn => ?_, ?_⟩
    · subst hn
      exact (π ⟨0, hm⟩).elim0
    · intro R M hM
      exact hpol R (fun l => M (π l)) (fun l => hM (π l))

end AlgebraicPCSP.Colouring


