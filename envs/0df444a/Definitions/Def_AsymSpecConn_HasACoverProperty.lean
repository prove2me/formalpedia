-- Prove2me | Definitions.Def_AsymSpecConn_HasACoverProperty
-- name    : AsymSpecConn_HasACoverProperty
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T06:39:46.973134+00:00
-- url     : https://prove2.me/theorems/6d79f3fa-79ce-40f1-a5cd-4b187bb25d8b
-- title:
--   The $\mathcal A$-cover property
-- statement:
--   Spectral points $g_1,\dots,g_r\in\Delta$ have the **$\mathcal A$-cover property** if for every $a\in\mathcal A$ there are numbers $\kappa_a(n)\ge1$ with $\kappa_a(n)^{1/n}\to1$ such that for every $n\in\mathbb N$ and all $s_1,\dots,s_r\in\mathcal S$ with $a^n\le s_1+\dots+s_r$,
--   $$\kappa_a(n)^{-1}\le\sum_{i=1}^r\frac{g_i(s_i)}{g_i(a)^n}.$$
--   A mixed, asymptotic subadditivity of this kind is what makes geometric averages of spectral points $\mathcal A$-good. A pair $f_0,f_1$ is the family $(f_0,f_1)$.
--
--   **Formalization Note** The module also names the displayed inequality for one $a$ and one sequence $\kappa$ (`CoverBound`), so that an explicit $\kappa$ can be stated. The inequality is in $\mathbb R$, and $n=0$ is included because the source's $\mathbb N$ contains $0$ (p.12). In the limit, $1/n$ is real division; the value at $n=0$ does not affect the limit.
-- source:
--   Vrana and Zuiddam, The asymptotic spectrum of tensors is connected, preprint (STOC 2027 submission, version of November 2, 2026, sha256 85a0b2ac…), Definition 2.7, p.17

import Mathlib
import Definitions.Def_AsymSpecConn_Spectrum

set_option autoImplicit false

open scoped NNReal Topology
open Filter

namespace AsymSpecConn

variable {S : Type*} [CommSemiring S] {P : Preorder S}

/-- The inequality of Definition 2.7 (p.17 of Vrana and Zuiddam, *The asymptotic spectrum of tensors is connected*, preprint (STOC 2027 submission, version of November 2, 2026, sha256 85a0b2ac…)) for one `a` and one
sequence `κ = κ_a`: for every `n ∈ ℕ` and all `s₁, …, s_r ∈ S`, if `aⁿ ≤ s₁ + ⋯ + s_r` then
`κ(n)⁻¹ ≤ Σ_i g_i(s_i) / g_i(a)ⁿ` (computed in `ℝ`). -/
def CoverBound (P : Preorder S) {r : ℕ} (g : Fin r → ↥(Spectrum S P)) (a : S) (κ : ℕ → ℝ) :
    Prop :=
  ∀ (n : ℕ) (s : Fin r → S), P.le (a ^ n) (∑ i, s i) →
    (κ n)⁻¹ ≤ ∑ i, (((g i).1 (s i) : ℝ≥0) : ℝ) / (((g i).1 a : ℝ≥0) : ℝ) ^ n

/-- **A-cover property** (Definition 2.7, p.17 of Vrana and Zuiddam, *The asymptotic spectrum of tensors is connected*, preprint (STOC 2027 submission, version of November 2, 2026, sha256 85a0b2ac…)): `g₁, …, g_r ∈ Δ`
have the A-cover property if for every `a ∈ A` there are numbers `1 ≤ κ_a(n)` with
`κ_a(n)^{1/n} → 1` such that the inequality `CoverBound` holds. A pair `f₀, f₁` is the family
`![f₀, f₁]`.

**Formalization Note** `κ_a` depends only on `a`; `n` ranges over all of `ℕ` (including `0`).
In the limit, `1/n` is real division (at `n = 0` the term is `κ(0)^0 = 1`, which does not affect
the limit). -/
def HasACoverProperty (P : Preorder S) (A : Set S) {r : ℕ} (g : Fin r → ↥(Spectrum S P)) :
    Prop :=
  ∀ a ∈ A, ∃ κ : ℕ → ℝ, (∀ n, 1 ≤ κ n) ∧
    Tendsto (fun n : ℕ => κ n ^ ((1 : ℝ) / n)) atTop (𝓝 1) ∧ CoverBound P g a κ

end AsymSpecConn


