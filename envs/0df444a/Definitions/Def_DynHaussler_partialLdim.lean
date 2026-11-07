-- Prove2me | Definitions.Def_DynHaussler_partialLdim
-- name    : DynHaussler_partialLdim
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T12:34:48.611434+00:00
-- url     : https://prove2.me/theorems/7a7baf6c-ecbb-49e6-9baf-62e0b942dd23
-- title:
--   Littlestone dimension of a partial binary class $A\subseteq\{0,1,*\}^Z$
-- statement:
--   Let $Z$ be a domain. A **partial binary class** is a set $A\subseteq\{0,1,*\}^Z$. It **shatters** a binary instance tree $z_t:\{0,1\}^{t-1}\to Z$, $t\in[s]$, if
--   $$
--   \forall b\in\{0,1\}^s\ \exists\phi\in A\ \forall t\in[s]:\ \phi\bigl(z_t(b_{<t})\bigr)=b_t .
--   $$
--   Thus the undefined symbol $*$ realizes neither edge of the tree. $\mathrm{Ldim}(A)$ is the largest shattered depth, and $\infty$ if these depths are unbounded.
--
--   The partial error classes of Eq. (39) are partial binary classes; their Littlestone dimension controls the number of causal completion rules (Lemma 16) and the adaptive sampling estimate (Lemma 17).
--
--   **Formalization Note** A partial concept is a map $Z\to$ `Option Bool` (`none` is $*$); shattering is the published `GradSuffice.IsLittlestoneTree`. The value lies in `ℕ∞`; the empty class gets $0$ instead of $-1$, so for an integer $r\ge0$ the paper's "$\mathrm{Ldim}(A)\le r$" is exactly `partialLdim A ≤ r`, also when $A=\emptyset$.
-- source:
--   Shao–Tao, A Sharp Dynamic Haussler Lemma, arXiv:2610.29898 (held version, sha256 b9ad736f…), Section 4.3, p.22 (PDF p.24)

import Mathlib
import Definitions.Def_GradSuffice_IsLittlestoneTree

set_option autoImplicit false

namespace DynHaussler

/-- The **Littlestone dimension of a partial binary class** `A ⊆ {0,1,∗}^Z`: the largest depth `s`
of a binary instance tree `z_t : {0,1}^{t−1} → Z` shattered by `A`, i.e. such that
`∀ b ∈ {0,1}^s ∃ ϕ ∈ A ∀ t ∈ [s] : ϕ(z_t(b_{<t})) = b_t` (so `∗` realizes neither edge); `∞` if
these depths are unbounded.
Shao–Tao, *A Sharp Dynamic Haussler Lemma*, arXiv:2610.29898 (held version, sha256 b9ad736f…),
Section 4.3, p.22 (PDF p.24).

**Formalization Note** A partial concept is `Z → Option Bool` (`none` is `∗`, `some false` /
`some true` are `0` / `1`); shattering is the published `GradSuffice.IsLittlestoneTree`. The value
lies in `ℕ∞`; the empty class gets `0` rather than `−1`, so for an integer `r ≥ 0` the paper's
"`Ldim(A) ≤ r`" is exactly `partialLdim A ≤ r` also when `A = ∅`. -/
noncomputable def partialLdim {Z : Type*} (A : Set (Z → Option Bool)) : ℕ∞ :=
  ⨆ (n : ℕ) (_ : ∃ z : NondualOpt.Tree Z n, GradSuffice.IsLittlestoneTree A z), (n : ℕ∞)

end DynHaussler


