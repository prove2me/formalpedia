-- Prove2me | Definitions.Def_CircTrichotomy_IsModDisjointMonomial
-- name    : CircTrichotomy_IsModDisjointMonomial
-- status  : Definition
-- author  : @iris
-- created : 2026-11-10T21:59:07.645134+00:00
-- url     : https://prove2.me/theorems/b48b3590-485a-471d-8492-1bacef6c0c8c
-- title:
--   Modular disjoint monomials
-- statement:
--   For $k\ge1$, a **$k$-modular disjoint monomial** is a language of the form
--   $$(\Gamma_0\cdots\Gamma_{k-1})^*\,U_0\,(\Gamma_0\cdots\Gamma_{k-1})^*\cdots U_{n-1}\,(\Gamma_0\cdots\Gamma_{k-1})^*,$$
--   where $n\in\mathbb N$, $\Gamma_0,\dots,\Gamma_{k-1}\subseteq\Sigma$, and each $U_i=U_{i,0}\cdots U_{i,q_ik-1}$ is a product of letter sets with $q_i\ge1$ and, for each $j$, either $U_{i,j}=\Gamma_{j\bmod k}$ or $U_{i,j}\subseteq\Sigma\setminus\Gamma_{j\bmod k}$. A modular disjoint monomial is a $k$-modular one for some $k\ge1$.
--
--   They generalize Straubing's disjoint monomials $\Gamma^*a_0\Gamma^*\cdots a_{n-1}\Gamma^*$ and generate the sublinear class.
--
--   **Formalization Note** As in the source, the language may contain the empty word (when $n=0$).
-- source:
--   Göller, Manuel, A Circuit Complexity Trichotomy For Regular Languages, arXiv:2611.03615 (version of November 3, 2026, sha256 5bef1791…), Definition B.19, p.29

import Mathlib
import Definitions.Def_CircTrichotomy_blockStar

set_option autoImplicit false

namespace CircTrichotomy

/-- The language `B* U₀ B* U₁ ⋯ U_{n−1} B*` with `B = Γ₀ ⋯ Γ_{k−1}`, for the list `Us = [U₀, …, U_{n−1}]`
of letter-set products (concatenation of languages). -/
def mdmLang {α : Type} (k : ℕ) (Γ : ℕ → Set α) (Us : List (List (Set α))) : Language α :=
  Us.foldl (fun acc U => acc * prodSets U * blockStar k Γ) (blockStar k Γ)

/-- **Modular disjoint monomial** (Göller, Manuel, *A Circuit Complexity Trichotomy For Regular Languages*, arXiv:2611.03615 (version of November 3, 2026, sha256 5bef1791…), Definition B.19, p.29): "Let k ∈ ℕ>0. A language over the
alphabet Σ is a k-modular disjoint monomial if it is of the form
(Γ₀ … Γ_{k−1})* U₀ (Γ₀ … Γ_{k−1})* … U_{n−1} (Γ₀ … Γ_{k−1})*,   (77)
where n ∈ ℕ, Γ₀, …, Γ_{k−1} ⊆ Σ and for each i ∈ [0, n − 1] the set of words U_i is a product
U_i = U_{i,0} … U_{i,q_i k−1}, where q_i ∈ ℕ>0 and U_{i,j} = Γ_{j mod k} or
U_{i,j} ⊆ Σ \ Γ_{j mod k} for each j ∈ [0, q_i k − 1]."

`IsModDisjointMonomial K`: `K` is a `k`-modular disjoint monomial for some `k ∈ ℕ>0`.

**Formalization Note** As in (77), the language may contain the empty word (`n = 0`); the theorems
intersect with `Σ⁺` or wrap it as `uKv` with `u, v ∈ Σ⁺`. -/
def IsModDisjointMonomial {α : Type} (K : Language α) : Prop :=
  ∃ k : ℕ, 0 < k ∧ ∃ Γ : ℕ → Set α, ∃ Us : List (List (Set α)),
    (∀ U ∈ Us, ∃ q : ℕ, 0 < q ∧ U.length = q * k ∧
      ∀ (j : ℕ) (A : Set α), U[j]? = some A → A = Γ (j % k) ∨ A ⊆ (Γ (j % k))ᶜ) ∧
    K = mdmLang k Γ Us

end CircTrichotomy


