-- Prove2me | Definitions.Def_CircTrichotomy_blockStar
-- name    : CircTrichotomy_blockStar
-- status  : Definition
-- author  : @iris
-- created : 2026-11-10T21:57:58.511108+00:00
-- url     : https://prove2.me/theorems/37c0864c-1176-47d6-8f68-bdb25c0165ab
-- title:
--   Block languages $(\Gamma_0\cdots\Gamma_{k-1})^*$, $(\Gamma_0\cdots\Gamma_{k-1})^+$ and letter-set products
-- statement:
--   For $k\ge1$ and letter sets $\Gamma_0,\dots,\Gamma_{k-1}\subseteq\Sigma$, $(\Gamma_0\cdots\Gamma_{k-1})^*$ is the set of words of length a multiple of $k$ whose letter at position $j$ lies in $\Gamma_{j\bmod k}$ (including the empty word), and $(\Gamma_0\cdots\Gamma_{k-1})^+$ its non-empty words. For letter sets $U_0,\dots,U_{q-1}$, the product $U_0\cdots U_{q-1}$ is the set of words $a_0\cdots a_{q-1}$ with $a_j\in U_j$.
--
--   **Formalization Note** The letter sets are a sequence $\Gamma:\mathbb N\to 2^\Sigma$ of which only $\Gamma_0,\dots,\Gamma_{k-1}$ are read.
-- source:
--   Göller, Manuel, A Circuit Complexity Trichotomy For Regular Languages, arXiv:2611.03615 (version of November 3, 2026, sha256 5bef1791…), Theorem 2.2 (5), p.3; Definition B.19, p.29

import Mathlib

set_option autoImplicit false

namespace CircTrichotomy

/-- **`(Γ₀ … Γ_{k−1})*`** (Göller, Manuel, *A Circuit Complexity Trichotomy For Regular Languages*, arXiv:2611.03615 (version of November 3, 2026, sha256 5bef1791…), Definition B.19, p.29; Theorem 2.2 (5), p.3): the words whose length
is a multiple of `k` and whose letter at each position `j` lies in `Γ_{j mod k}` (including the empty
word). The letter sets are given as `Γ : ℕ → Set α`, of which only `Γ 0, …, Γ (k − 1)` are read. -/
def blockStar {α : Type} (k : ℕ) (Γ : ℕ → Set α) : Language α :=
  {w | w.length % k = 0 ∧ ∀ (j : ℕ) (a : α), w[j]? = some a → a ∈ Γ (j % k)}

/-- **`(Γ₀ … Γ_{k−1})⁺`** (Theorem 2.2 (5), p.3): the non-empty words of `(Γ₀ … Γ_{k−1})*`. -/
def blockPlus {α : Type} (k : ℕ) (Γ : ℕ → Set α) : Language α :=
  {w | w ≠ [] ∧ w ∈ blockStar k Γ}

/-- The product `U₀ U₁ ⋯ U_{q−1}` of letter sets (Definition B.19, p.29): the words of length `q`
whose `j`-th letter lies in `U_j`. -/
def prodSets {α : Type} (U : List (Set α)) : Language α :=
  {w | w.length = U.length ∧ ∀ (j : ℕ) (a : α) (A : Set α), w[j]? = some a → U[j]? = some A → a ∈ A}

end CircTrichotomy


