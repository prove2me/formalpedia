-- Prove2me | Definitions.Def_CircTrichotomy_IsStamp
-- name    : CircTrichotomy_IsStamp
-- status  : Definition
-- author  : @iris
-- created : 2026-11-10T21:57:49.260016+00:00
-- url     : https://prove2.me/theorems/0f00a5cc-6b01-481b-873e-5b0663fa6cf0
-- title:
--   Stamps $\varphi:\Sigma^+\to S$
-- statement:
--   A **stamp** is a surjective semigroup morphism $\varphi:\Sigma^+\to S$ from the free semigroup over a finite alphabet $\Sigma$ onto a finite semigroup $S$.
--
--   Stamps are the objects classified by lm-pseudovarieties such as $\mathbf X$.
--
--   **Formalization Note** Finiteness of the alphabet is a separate `Fintype α` hypothesis of each theorem.
-- source:
--   Göller, Manuel, A Circuit Complexity Trichotomy For Regular Languages, arXiv:2611.03615 (version of November 3, 2026, sha256 5bef1791…), §A.2, p.16

import Mathlib

set_option autoImplicit false

namespace CircTrichotomy

/-- **Stamp** (Göller, Manuel, *A Circuit Complexity Trichotomy For Regular Languages*, arXiv:2611.03615 (version of November 3, 2026, sha256 5bef1791…), §A.2, p.16): "A semigroup stamp is a surjective semigroup morphism of the
form φ : Σ⁺ → S, where Σ is a finite alphabet and S is finite."

**Formalization Note** `φ` is a semigroup morphism (`MulHom`) from the free semigroup
`FreeSemigroup α` (= α⁺); finiteness of the alphabet `α` is a separate `Fintype α` hypothesis of the
theorems. -/
def IsStamp {α S : Type} [Semigroup S] (φ : FreeSemigroup α →ₙ* S) : Prop :=
  Function.Surjective φ ∧ Finite S

end CircTrichotomy


