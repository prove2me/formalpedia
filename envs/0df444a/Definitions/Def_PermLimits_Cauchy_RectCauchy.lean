-- Prove2me | Definitions.Def_PermLimits_Cauchy_RectCauchy
-- name    : PermLimits_Cauchy_RectCauchy
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-27T21:21:53.576986+00:00
-- url     : https://prove2.me/theorems/64e5f4a4-87ca-45ea-b5c1-b714263fbfb7
-- title:
--   Rectangular distance on all finite permutations, and $d_\square$-Cauchy sequences
-- statement:
--   Let $\mathcal S=\bigcup_{n\ge1}S_n$ be the set of all finite permutations and, for $\sigma\in\mathcal S$, let $Z_\sigma$ be its step limit permutation.
--
--   1. **Rectangular distance on $\mathcal S$.** For $\sigma,\pi\in\mathcal S$, possibly of different lengths,
--   $$d_\square(\sigma,\pi):=d_\square(Z_\sigma,Z_\pi),$$
--   where on the right $d_\square$ is the rectangular distance between limit permutations.
--   2. **Cauchy sequence.** A permutation sequence $(\sigma_n)_{n\in\mathbb N}$ is a *Cauchy sequence with respect to $d_\square$* if for every $\varepsilon>0$ there is $n_0=n_0(\varepsilon)$ such that
--   $$d_\square(\sigma_n,\sigma_m)<\varepsilon\qquad\text{for all } n,m\ge n_0 .$$
--
--   For two permutations of the same length $n$ the source first defines $d_\square(\sigma_1,\sigma_2)=\frac1n\max_{S,T}\big||\sigma_1(S)\cap T|-|\sigma_2(S)\cap T|\big|$, the maximum over intervals $S,T$ of $[n]$, and remarks that it equals $d_\square(Z_{\sigma_1},Z_{\sigma_2})$; item 1 is the resulting extension to permutations of different lengths, which is the one needed for sequences.
--
--   **Formalization Note** Item 1 is the definition for every pair of lengths. A permutation of arbitrary length is a pair $\langle n,\pi\rangle$ with $\pi$ a permutation of $\{0,\dots,n-1\}$. The type admits the empty permutation ($n=0$, not a permutation in the source), whose step limit permutation is taken to be the uniform one $Z_u(x,y)=y$. The Cauchy condition is written with explicit quantifiers and the strict inequality of the source; it places no condition on the lengths.
-- source:
--   Hoppen, Kohayakawa, Moreira, Ráth, Sampaio, Limits of permutation sequences, arXiv:1103.5844v2, https://arxiv.org/abs/1103.5844v2, pp. 12–13, Sect. 4.1 (extension of Definition 4.1 via d□(σ, π) := d□(Z_σ, Z_π)), and p. 5 (definition of a Cauchy sequence)

import Mathlib
import Definitions.Def_PermLimits_Shared_StepLimit
import Definitions.Def_PermLimits_Shared_RectDist
open PermLimits.Shared

/-!
# The rectangular distance between permutations of arbitrary lengths, and Cauchy sequences

C. Hoppen, Y. Kohayakawa, C. G. Moreira, B. Ráth, R. M. Sampaio, *Limits of permutation
sequences*, arXiv:1103.5844v2: the extension `d□(σ, π) := d□(Z_σ, Z_π)` (Sect. 4.1, pp. 12–13)
and the notion of a Cauchy sequence with respect to `d□` (Sect. 1, p. 5).

A definition bundle: `d□` on the set `𝒮` of all finite permutations, and `d□`-Cauchy
permutation sequences.
-/

namespace PermLimits.Cauchy

open unitInterval

/-- **Rectangular distance between two permutations of arbitrary lengths** (Hoppen et al.,
arXiv:1103.5844v2, Sect. 4.1, pp. 12–13): for permutations `σ, π ∈ 𝒮`,
`d□(σ, π) := d□(Z_σ, Z_π)`, where `Z_σ` is the limit permutation of Definition 3.4 and `d□` on
limit permutations is Eq. (32).

**Formalization Note.** The paper first defines `d□(σ₁, σ₂)` for `σ₁, σ₂ ∈ S_n` by Eq. (31) (a
normalized maximum over intervals of `[n]`), observes that it equals `d□(Z_{σ₁}, Z_{σ₂})`, and
then uses the right side to extend `d□` to permutations of different lengths; Theorem 1.8 uses
this extension, since the terms of a permutation sequence have varying lengths. It is the
definition here, for every pair of lengths. A permutation of arbitrary length is a dependent
pair `⟨n, π⟩ : Σ n : ℕ, Equiv.Perm (Fin n)`. For `n ≥ 1`, `stepLimit π` is a limit permutation;
for the empty permutation (`n = 0`, not a permutation in the paper) `stepLimit` returns the
uniform limit permutation. -/
noncomputable def permRectDist (p q : Σ n : ℕ, Equiv.Perm (Fin n)) : ℝ :=
  rectDist (stepLimit p.2) (stepLimit q.2)

/-- **Cauchy sequence with respect to `d□`** (Hoppen et al., arXiv:1103.5844v2, Sect. 1, p. 5):
a permutation sequence `(σ_n)` is a Cauchy sequence with respect to the metric `d□` if, for every
`ε > 0`, there exists `n₀ = n₀(ε)` such that `d□(σ_n, σ_m) < ε` for every `n, m ≥ n₀`.

**Formalization Note.** Stated with the explicit `ε`–`n₀` quantifiers and the strict inequality of
the paper, using `d□` on permutations of arbitrary lengths (`permRectDist`). No condition on the
lengths `|σ_n|` is part of this definition. -/
def IsRectCauchy (s : ℕ → Σ n : ℕ, Equiv.Perm (Fin n)) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ n₀ : ℕ, ∀ n m : ℕ, n₀ ≤ n → n₀ ≤ m → permRectDist (s n) (s m) < ε

end PermLimits.Cauchy


