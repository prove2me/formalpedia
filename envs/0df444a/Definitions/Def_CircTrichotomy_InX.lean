-- Prove2me | Definitions.Def_CircTrichotomy_InX
-- name    : CircTrichotomy_InX
-- status  : Definition
-- author  : @iris
-- created : 2026-11-10T21:59:37.174034+00:00
-- url     : https://prove2.me/theorems/67f18bb1-0f44-4ba6-b684-7fbce22c34a9
-- title:
--   The lm-pseudovariety $\mathbf X=\bigcap_k\mathbf X_k$
-- statement:
--   For $k\ge1$, a stamp $\varphi:\Sigma^+\to S$ is in $\mathbf X_k$ if it satisfies, for all $m\in[1,k]$ and $i\in[0,m-1]$, the identity
--   $$(x_0\cdots x_{m-1})^\omega\,p_0\cdots p_{i-1}\,x_i\,p_{i+1}\cdots p_{m-1}\,(y_0\cdots y_{m-1})^\omega=(x_0\cdots x_{m-1})^\omega\,p_0\cdots p_{i-1}\,y_i\,p_{i+1}\cdots p_{m-1}\,(y_0\cdots y_{m-1})^\omega,$$
--   where satisfying an identity means: for every $\ell\ge1$ and every assignment $\sigma$ of words of the **same length** $\ell$ to the variables, $\varphi(\sigma(t))=\varphi(\sigma(t'))$, with products and $\omega$-powers evaluated in $S$. The pseudovariety is $\mathbf X=\bigcap_{k\ge1}\mathbf X_k$.
--
--   A regular language has sublinear circuit complexity exactly when its syntactic morphism is in $\mathbf X$.
--
--   **Formalization Note** Only the variables that occur are assigned. Products of $m\ge1$ elements are `FanInSemigroup.tupleProd` (published definition `FanInSemigroup_wordProd`). The two $\omega$-powers are any elements $e,f$ with `IsOmegaPow`; in a finite semigroup they are unique, so this is the identity as stated.
-- source:
--   Göller, Manuel, A Circuit Complexity Trichotomy For Regular Languages, arXiv:2611.03615 (version of November 3, 2026, sha256 5bef1791…), Definition 2.3, p.4

import Mathlib
import Definitions.Def_CircTrichotomy_IsOmegaPow
import Definitions.Def_FanInSemigroup_wordProd

set_option autoImplicit false

namespace CircTrichotomy

/-- **`φ ∈ X_k`** (Göller, Manuel, *A Circuit Complexity Trichotomy For Regular Languages*, arXiv:2611.03615 (version of November 3, 2026, sha256 5bef1791…), Definition 2.3, p.4): "For each k ∈ ℕ>0 let X_k denote the
lm-pseudovariety of stamps satisfying the following identities, where m ∈ [1, k] and
i ∈ [0, m − 1]:
(x₀ ⋯ x_{m−1})^ω p₀ ⋯ p_{i−1} x_i p_{i+1} ⋯ p_{m−1} (y₀ ⋯ y_{m−1})^ω
= (x₀ ⋯ x_{m−1})^ω p₀ ⋯ p_{i−1} y_i p_{i+1} ⋯ p_{m−1} (y₀ ⋯ y_{m−1})^ω   (1)",
where (p.4) "A stamp φ : Σ⁺ → S satisfies the identity t = t′ over the set of variables V if
φ(σ(t)) = φ(σ(t′)) for every ℓ ∈ ℕ>0 and every morphism defined by a map σ : V → Σ^ℓ", and
φ(σ(t₁t₂)) = φ(σ(t₁))φ(σ(t₂)), φ(σ(t^ω)) = φ(σ(t))^ω.

Here `m ∈ [1, k]`, `i : Fin m` is `i ∈ [0, m − 1]`, and `p j, x j, y j` (`j < m`) are the images
`σ(p_j), σ(x_j), σ(y_j)` of the variables that occur, all words of the same length `ℓ ≥ 1`. The
two sides are evaluated in `S`: `e` and `f` are the ω-powers of `φ(σ(x₀)) ⋯ φ(σ(x_{m−1}))` and
`φ(σ(y₀)) ⋯ φ(σ(y_{m−1}))`, and the middle factor is the product of `φ(σ(p_j))` with the `i`-th
factor replaced by `φ(σ(x_i))`, resp. `φ(σ(y_i))`. Ordered products of `m ≥ 1` elements are
`FanInSemigroup.tupleProd` (published definition `FanInSemigroup_wordProd`).

**Formalization Note**
* Variables that do not occur in an identity do not affect it, so `σ` is given on the occurring
  variables only.
* `e`, `f` range over all elements satisfying `IsOmegaPow`; in a finite semigroup there is exactly
  one such element (the ω-power), so this is the paper's identity. -/
def InXk {α S : Type} [Semigroup S] (φ : FreeSemigroup α →ₙ* S) (k : ℕ) : Prop :=
  ∀ m : ℕ, ∀ hm : 1 ≤ m, m ≤ k → ∀ i : Fin m, ∀ ℓ : ℕ, 0 < ℓ →
    ∀ p x y : Fin m → FreeSemigroup α,
      (∀ j, (p j).length = ℓ ∧ (x j).length = ℓ ∧ (y j).length = ℓ) →
      ∀ e f : S, IsOmegaPow (FanInSemigroup.tupleProd hm (fun j => φ (x j))) e →
        IsOmegaPow (FanInSemigroup.tupleProd hm (fun j => φ (y j))) f →
        e * FanInSemigroup.tupleProd hm (fun j => φ (if j = i then x j else p j)) * f =
          e * FanInSemigroup.tupleProd hm (fun j => φ (if j = i then y j else p j)) * f

/-- **`φ ∈ X`** (Göller, Manuel, *A Circuit Complexity Trichotomy For Regular Languages*, arXiv:2611.03615 (version of November 3, 2026, sha256 5bef1791…), Definition 2.3, p.4): "Let X = ⋂_{k≥1} X_k." -/
def InX {α S : Type} [Semigroup S] (φ : FreeSemigroup α →ₙ* S) : Prop :=
  ∀ k : ℕ, 0 < k → InXk φ k

end CircTrichotomy


