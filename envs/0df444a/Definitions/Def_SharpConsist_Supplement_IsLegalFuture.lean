-- Prove2me | Definitions.Def_SharpConsist_Supplement_IsLegalFuture
-- name    : SharpConsist_Supplement_IsLegalFuture
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T06:21:04.897642+00:00
-- url     : https://prove2.me/theorems/3c9febde-5e98-41c9-99a5-0136f403e7ee
-- title:
--   Legal future (Definition 2.1)
-- statement:
--   Fix a current set $X$ and the objective $f$ on $2^X$, with marginals $f(i\mid S)=f(S\cup\{i\})-f(S)$. A function $h:2^X\to\mathbb R_{\ge0}$ is a **legal future** if
--
--   1. $h$ is monotone and submodular;
--   2. $h(S)\ge f(S)$ for all $S\subseteq X$;
--   3. for all $S\subseteq X$ and $i\in X\setminus S$,
--   $$0\le h(S\cup\{i\})-h(S)\le f(i\mid S).\tag{2.1}$$
--
--   The value $h(\emptyset)$ may be positive. The motivating example is $h_R(S)=f(S\cup R)$ for a fixed future set $R\subseteq V\setminus X$. Robust cores (Theorem 4.3) are required to be good against every legal future at once.
--
--   **Formalization Note** Submodularity is the published lattice form `NonmonotoneSubmod.Shared.Submodular`, equivalent on a finite ground set to the marginal form; monotonicity is $S\subseteq T\Rightarrow h(S)\le h(T)$.
-- source:
--   Fu–Zhang–Tao, A Sharp Barrier of Consistent Submodular Maximization, arXiv:2609.09986 (held version, sha256 874ec76c…), §2.1, Definition 2.1, Eq. (2.1), p.4

import Mathlib
import Definitions.Def_NonmonotoneSubmod_Shared_Submodular

namespace SharpConsist.Supplement

/-- **Legal future** (Definition 2.1). Fu–Zhang–Tao, *A Sharp Barrier of Consistent Submodular Maximization*, arXiv:2609.09986 (held version, sha256 874ec76c…), §2.1, Definition 2.1, Eq. (2.1), p.4.

For the objective `f` on the current set `X`, a function `h : 2^X → ℝ≥0` is a legal future if it
is monotone and submodular, `h(S) ≥ f(S)` for all `S ⊆ X`, and
`0 ≤ h(S ∪ {i}) − h(S) ≤ f(i | S) = f(S ∪ {i}) − f(S)` for `S ⊆ X`, `i ∈ X \ S`.

**Formalization Note.** `h(∅)` may be positive (the page: "`h_R(∅) = f(R)` possibly positive"), so
`h` is not required to be normalized. Nonnegativity is the codomain `ℝ≥0` of the page.
Submodularity is the published lattice form `NonmonotoneSubmod.Shared.Submodular`, equivalent on a
finite ground set to the page's marginal form; monotonicity is `S ⊆ T → h S ≤ h T`. -/
def IsLegalFuture {X : Type} [Fintype X] [DecidableEq X] (f h : Finset X → ℝ) : Prop :=
  (∀ S, 0 ≤ h S) ∧ NonmonotoneSubmod.Shared.Submodular h ∧ (∀ S T, S ⊆ T → h S ≤ h T) ∧
    (∀ S, f S ≤ h S) ∧
    ∀ (S : Finset X) (i : X), i ∉ S →
      0 ≤ h (insert i S) - h S ∧ h (insert i S) - h S ≤ f (insert i S) - f S

end SharpConsist.Supplement


