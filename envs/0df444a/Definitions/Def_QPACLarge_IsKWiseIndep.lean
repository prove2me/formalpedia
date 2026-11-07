-- Prove2me | Definitions.Def_QPACLarge_IsKWiseIndep
-- name    : QPACLarge_IsKWiseIndep
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T16:05:12.585205+00:00
-- url     : https://prove2.me/theorems/10ac2eea-bfa4-4a6a-9d53-3eb17ce89824
-- title:
--   $k$-wise independent family
-- statement:
--   Let $A$ be a finite seed set and $\{h_a : X \to \{0,1\}\}_{a \in A}$ a family of Boolean functions. For an integer $k \ge 1$ the family is **$k$-wise independent** if for every $1 \le \ell \le k$, all distinct $x^{(1)}, \dots, x^{(\ell)} \in X$ and every $v \in \{0,1\}^\ell$,
--
--   $$
--   \Pr_{a \sim A}\big[(h_a(x^{(1)}), \dots, h_a(x^{(\ell)})) = v\big] = 2^{-\ell}.
--   $$
--
--   The quadratic family of Lemma 3.1 is 4-wise independent; this is what drives the moment computations of Lemma 3.4.
-- source:
--   Oliveira, Unconditional Quantum PAC Learning Advantage in the Large Error Regime, arXiv:2610.23268 (held file sha256 e749e7c9…), Section 2.5, p.17

import Mathlib

namespace QPACLarge

/-- **`k`-wise independent family of Boolean functions.**
Oliveira, *Unconditional Quantum PAC Learning Advantage in the Large Error Regime*, arXiv:2610.23268 (held file sha256 e749e7c9…), Section 2.5, p.17: "the family `H` is called `k`-wise independent if, for every
`1 ≤ ℓ ≤ k`, every set of distinct points `x⁽¹⁾, …, x⁽ℓ⁾ ∈ X`, and every vector `v ∈ {0,1}^ℓ`,
`Pr_{a∼A}[(h_a(x⁽¹⁾), …, h_a(x⁽ℓ⁾)) = v] = 2^{−ℓ}`."

The family is `h : A → X → Bool` (`h a = h_a`) over a finite seed set `A` with the uniform
distribution; distinct points are an injective `xs : Fin ℓ → X`.

**Formalization Note.** The probability is the fraction of seeds. -/
def IsKWiseIndep {A X : Type*} [Fintype A] (h : A → X → Bool) (k : ℕ) : Prop :=
  ∀ ℓ : ℕ, 1 ≤ ℓ → ℓ ≤ k → ∀ xs : Fin ℓ → X, Function.Injective xs → ∀ v : Fin ℓ → Bool,
    (open Classical in
      ((Finset.univ.filter fun a => ∀ i, h a (xs i) = v i).card : ℝ) / Fintype.card A) =
      ((2 : ℝ) ^ ℓ)⁻¹

end QPACLarge


