-- Prove2me | Definitions.Def_FuchsThesis_Daroczy_IsSymmetric
-- name    : FuchsThesis_Daroczy_IsSymmetric
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T15:21:32.54091+00:00
-- url     : https://prove2.me/theorems/55ed0243-23fb-46b9-9b86-1a218b6102eb
-- title:
--   Symmetry of an information function $H:\Gamma\to\mathbb R$
-- statement:
--   A function $H : \Gamma \to \mathbb R$ on all discrete probability distributions is **symmetric in all its arguments** if, for every $n$, every distribution $(p_1,\dots,p_n) \in \Gamma_n$ and every permutation $\sigma$ of $\{1,\dots,n\}$,
--
--   $$
--   H(p_{\sigma(1)},\dots,p_{\sigma(n)}) = H(p_1,\dots,p_n).
--   $$
--
--   This is Fuchs's "requirement of symmetry": the expected information gained in sampling a distribution depends only on the probabilities of the outcomes, not on how the outcomes are labelled.
--
--   **Formalization Note** A function on $\Gamma = \bigcup_n \Gamma_n$ is a family of functions $H_n$ on real $n$-vectors; only their values on $\Gamma_n$ matter, so invariance is required only there.
-- source:
--   Fuchs, Distinguishability and Accessible Information in Quantum Theory, arXiv:quant-ph/9601020v1, §2.4.1, p.31 (PDF p.40), and Theorem 2.7, p.32 (PDF p.41)

import Mathlib
import Definitions.Def_FuchsThesis_Daroczy_IsDist

namespace FuchsThesis.Daroczy

/-- Fuchs, *Distinguishability and Accessible Information in Quantum Theory*,
arXiv:quant-ph/9601020v1, §2.4.1, p.31 (PDF p.40) and Theorem 2.7, p.32 (PDF p.41): a function
`H : Γ → ℝ` on all discrete probability distributions is **symmetric in all its arguments**: for
every `n`, `H(p₁, …, pₙ)` is invariant under permutations of its arguments ("the requirement of
symmetry", p.31).

**Formalization Note.** A function on `Γ = ⋃ₙ Γₙ` is a family `H n : (Fin n → ℝ) → ℝ`; its
values off `Γₙ` are irrelevant, so invariance is required only on `Γₙ` (`IsDist p`). A
permutation of the arguments is `p ∘ σ` for `σ` a permutation of `Fin n`. -/
def IsSymmetric (H : (n : ℕ) → (Fin n → ℝ) → ℝ) : Prop :=
  ∀ (n : ℕ) (σ : Equiv.Perm (Fin n)) (p : Fin n → ℝ), IsDist p → H n (p ∘ σ) = H n p

end FuchsThesis.Daroczy


