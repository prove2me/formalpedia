-- Prove2me | Definitions.Def_CircTrichotomy_IsStabilityIndex
-- name    : CircTrichotomy_IsStabilityIndex
-- status  : Definition
-- author  : @iris
-- created : 2026-11-10T21:57:53.213291+00:00
-- url     : https://prove2.me/theorems/18cec746-c681-4533-90bb-898759913ab0
-- title:
--   Stability index $s$ and stable semigroup $\mathrm{stab}(\varphi)=\varphi(\Sigma^s)$
-- statement:
--   Let $\varphi:\Sigma^+\to S$ be a morphism onto a finite semigroup. For $s\ge1$ write $\varphi(\Sigma^s)$ for the image of the words of length $s$. The **stability index** of $\varphi$ is the smallest $s\ge1$ with
--   $$\varphi(\Sigma^s)=\varphi(\Sigma^{2s}),$$
--   and the **stable semigroup** is $\mathrm{stab}(\varphi)=\varphi(\Sigma^s)$.
--
--   **Formalization Note** The stability index is a predicate `IsStabilityIndex φ s` (it determines $s$ uniquely), and $\varphi(\Sigma^s)$ is `lenImage φ s`.
-- source:
--   Göller, Manuel, A Circuit Complexity Trichotomy For Regular Languages, arXiv:2611.03615 (version of November 3, 2026, sha256 5bef1791…), p.3 and §A.2, p.17

import Mathlib

set_option autoImplicit false

namespace CircTrichotomy

/-- `φ(Σˢ)`: the image under `φ` of the words of length `s`. At the stability index `s` this is
the stable semigroup `stab(φ) = φ(Σˢ)` (p.3). -/
def lenImage {α S : Type} [Semigroup S] (φ : FreeSemigroup α →ₙ* S) (s : ℕ) : Set S :=
  {y | ∃ x : FreeSemigroup α, x.length = s ∧ φ x = y}

/-- **Stability index** (Göller, Manuel, *A Circuit Complexity Trichotomy For Regular Languages*, arXiv:2611.03615 (version of November 3, 2026, sha256 5bef1791…), p.3 and §A.2, p.17): "Let φ : Σ⁺ → S be a morphism onto a finite
semigroup S. The smallest number s ≥ 1 satisfying φ(Σˢ) = φ(Σ²ˢ) is called the stability index of
φ; the stable semigroup of φ is stab(φ) = φ(Σˢ)."

`IsStabilityIndex φ s` says `s ≥ 1`, `φ(Σˢ) = φ(Σ²ˢ)`, and no `1 ≤ s' < s` has
`φ(Σ^{s'}) = φ(Σ^{2s'})`.

**Formalization Note** The stability index is a predicate, not a function with a default value;
it determines `s` uniquely. The stable semigroup is `lenImage φ s` at that `s`. -/
def IsStabilityIndex {α S : Type} [Semigroup S] (φ : FreeSemigroup α →ₙ* S) (s : ℕ) : Prop :=
  1 ≤ s ∧ lenImage φ s = lenImage φ (2 * s) ∧
    ∀ s' : ℕ, 1 ≤ s' → s' < s → lenImage φ s' ≠ lenImage φ (2 * s')

end CircTrichotomy


