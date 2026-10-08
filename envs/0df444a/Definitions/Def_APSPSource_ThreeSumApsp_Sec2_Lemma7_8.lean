-- Prove2me | Definitions.Def_APSPSource_ThreeSumApsp_Sec2_Lemma7_8
-- name    : APSPSource_ThreeSumApsp_Sec2_Lemma7_8
-- status  : Definition
-- author  : @wurtle
-- created : 2026-10-06T07:49:12.698869+00:00
-- url     : https://prove2.me/theorems/219e7fb1-d5e2-4ad3-9144-8a9fa8e6ac00
-- title:
--   Leaf encodings with a general coefficient family
-- statement:
--   Let $A$ be a finite alphabet, let $\Lambda$ be the term alphabet of the algebraic construction, and let $c:\Lambda\times A\to\mathbb Z$ be a coefficient family. For an integer array $a$ on length-$L$ strings over $A$ and a leaf $\tau\in\Lambda^L$, define
--
--   $$E_c(\tau,a)=\sum_{u\in A^L}a[u]\prod_{\ell=1}^{L}c(\tau_\ell,u_\ell).$$
--
--   The empty product at $L=0$ is $1$. Using the left coefficient family gives $\Phi_\tau(a)$, and using the right family gives $\Psi_\tau(a)$.
--
--   This common expression lets later encoding identities be stated uniformly for both sides of the algebraic construction.
--
--   References:
--
--   1. [Source formalization, lines 84–87](https://github.com/anthropics/formal-math/blob/e1a4e6508154ea59f030480661590a9fe3018011/3sum-apsp/ThreeSumApsp/Sec2/Lemma7_8.lean#L84-L87).
-- source:
--   https://github.com/anthropics/formal-math/blob/e1a4e6508154ea59f030480661590a9fe3018011/3sum-apsp/ThreeSumApsp/Sec2/Lemma7_8.lean#L84-L87

/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/

import Definitions.Def_APSPSource_PaperStatements
import Definitions.Def_TrulySubcubicAPSP_SourceSpecification
import Mathlib.Algebra.MvPolynomial.Basic
import Mathlib.Algebra.MvPolynomial.CommRing
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Data.Finset.Sort
import Mathlib.LinearAlgebra.Finsupp.LinearCombination
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.NumberTheory.PrimeCounting
import Mathlib.Probability.Independence.Basic
import Mathlib.Tactic.DeriveFintype
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NoncommRing
import Mathlib.Tactic.Ring

set_option autoImplicit false
set_option relaxedAutoImplicit false


/-!
# Lemmas 7 and 8: what `Full` computes

Section 2.3.2. Lemma 7: at the leaf `τ`, `Full(a, b)` multiplies `Φ_τ(a)` by
`Ψ_τ(b)`, and it returns `Mult(a, b)`, whose entry at `w` is the sum of these products over the
leaves contributing to `w` (equation (2)). Lemma 8:
`Mult(a, b)[w] = ∑_{u,v} γ(u₁, v₁, w₁) ⋯ γ(u_L, v_L, w_L) a[u] b[v]`, with the `γ` of equation (3).

* `Φ_τ` and `Ψ_τ` are the same expression for two families of linear forms (`encodeWith`), so what
  holds for both is proved once.
* Lemma 7 is proved by induction on `L`, as in the paper. Step (2) is the encoding:
  `Φ_{λτ'}(a) = Φ_{τ'}(A_λ)` and `Ψ_{λτ'}(b) = Ψ_{τ'}(B_λ)` (`Phi_cons`, `Psi_cons`). Step (4) is
  the decoding: the leaves contributing to `z w'` are the `λτ'` with `λ` contributing to `z` and
  `τ'` to `w'` (`Leaf.contributes_succ`), so `Full` and `Mult` both satisfy
  `c[z w'] = ∑_{λ contributing to z} C_λ[w']` (`Full_succ`, `Mult_succ`).
* Lemma 8: the leaves contributing to `w` choose a term contributing to `w_ℓ` independently at each
  level `ℓ` (`Leaf.filter_contributes_eq_piFinset`), so the sum over these leaves of a product over
  the levels is a product of sums (`prod_gamma_eq_sum_contributes`).
-/

@[expose] public section

open Finset

namespace ThreeSumApsp

/-! ### Which leaves contribute to an output string -/









































/-! ### The two encodings at once -/

section encodeWith

variable {α : Type} [Fintype α] (c : Term → α → ℤ) {L : ℕ}

/-- The number `∑_u a[u] ∏_ℓ c_{τ_ℓ}(u_ℓ)`, for an array `a` on the strings over a finite alphabet
and the coefficients `c` of a family of linear forms, one for each term. By definition it is
`Φ_τ(a)` for `c = φ` and `Ψ_τ(b)` for `c = ψ`. -/
def encodeWith (τ : Leaf L) (a : (Fin L → α) → ℤ) : ℤ := ∑ u, a u * ∏ ℓ, c (τ ℓ) (u ℓ)














end encodeWith

/-! ### Lemma 7 -/





































































/-! ### Lemma 8 -/


























end ThreeSumApsp


