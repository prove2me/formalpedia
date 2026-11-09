-- Prove2me | Definitions.Def_RSSubspaceDesign_IsConjugateSet
-- name    : RSSubspaceDesign_IsConjugateSet
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T22:25:33.912625+00:00
-- url     : https://prove2.me/theorems/eec31b2c-7e93-4321-b64d-8dca3fa05ec7
-- title:
--   Lemma 2.20 — the properties of a downward-closed set $B$ of independent conjugates
-- statement:
--   Let $F/K$ be a field extension, $\sigma_1,\dots,\sigma_g$ automorphisms of $F/K$ and $u_1,\dots,u_d\in F[X]$. For $\omega\in\mathbb Z_{\ge0}^g$ write $\sigma^\omega=\sigma_1^{\omega_1}\cdots\sigma_g^{\omega_g}$, acting on $F[X]$ coefficientwise and fixing $X$. A set $B\subseteq\mathbb Z_{\ge0}^g$ has the **properties of Lemma 2.20** if $|B|=d$, $B$ is downward closed under the coordinatewise order, and
--
--   1. the polynomial $P(X)=\det\big(\sigma^\omega(u_a)(X)\big)_{\omega\in B,\,1\le a\le d}$ is nonzero;
--   2. for any distinct points $\alpha_1,\dots,\alpha_n\in F$,
--   $$\sum_{i=1}^n|\{\omega\in B:\sigma^\omega(\alpha_i)\ne\alpha_i\}|\;\le\;d\log_2 d\cdot\max_{\sigma\in\{\sigma_1,\dots,\sigma_g\}}|\{\alpha_i:\sigma(\alpha_i)\ne\alpha_i\}|.\qquad(2.2)$$
--
--   These are the two conclusions of Lemma 2.20, used in Proposition 4.3.
--
--   **Formalization Note** Rows of the determinant are indexed through an enumeration of $B$, and (i) is required for every enumeration (a reordering changes only the sign). The maximum over the generators is a maximum over their indices.
-- source:
--   O. Alrabiah, R. Goyal, V. Guruswami, Explicit Reed-Solomon Subspace Designs: Optimal List and Line Decoding, arXiv:2610.36215 (held version, sha256 cf26424b…), Lemma 2.20, pp.14–15 (PDF pp.16–17), display (2.2)

import Mathlib
import Definitions.Def_RSSubspaceDesign_ratFuncAlgebra

open Polynomial

namespace RSSubspaceDesign

open Classical in
/-- **The properties of the set `B` in Lemma 2.20.** Alrabiah–Goyal–Guruswami, arXiv:2610.36215
(held version, sha256 cf26424b…f36206), Lemma 2.20, pp.14–15, with display (2.2).

For automorphisms `σ₁, …, σ_g` of `F/K` and `u₁, …, u_d ∈ F[X]`, write
`σ^ω = σ₁^{ω₁} ⋯ σ_g^{ω_g}` for `ω ∈ ℤ^g_{≥0}`. A set `B ⊆ ℤ^g_{≥0}` has the properties of
Lemma 2.20 if it has size `d`, is downward closed under the coordinatewise order, and
(i) `P(X) = det(σ^ω(u_a)(X))_{ω ∈ B, 1 ≤ a ≤ d}` is nonzero;
(ii) for any distinct `α₁, …, αₙ ∈ F`,
`∑ᵢ |{ω ∈ B : σ^ω(αᵢ) ≠ αᵢ}| ≤ d log₂ d · max_{σ ∈ {σ₁,…,σ_g}} |{αᵢ : σ(αᵢ) ≠ αᵢ}|` (2.2).

**Formalization Note.** `σ` acts on `F[X]` coefficientwise, fixing `X` (`Polynomial.map`).
Exponent vectors are `Fin g → ℕ` with the pointwise order; `σ^ω` is the ordered product
`σ₀^{ω₀} ⋯ σ_{g−1}^{ω_{g−1}}` in `F ≃ₐ[K] F`. The rows of the determinant are indexed through an
enumeration `e : Fin d ≃ B`; nonvanishing does not depend on the enumeration, and (i) is required
for every one. The max over `σ ∈ {σ₁, …, σ_g}` is the max over the index `j` (`0` when `g = 0`);
for distinct points `|{αᵢ : …}|` counts indices. The determinant is taken in `F[X]`. -/
def IsConjugateSet (K : Type*) {F : Type*} [Field K] [Field F] [Algebra K F] {g d : ℕ}
    (σ : Fin g → (F ≃ₐ[K] F)) (u : Fin d → F[X]) (B : Finset (Fin g → ℕ)) : Prop :=
  B.card = d ∧ (∀ ω ∈ B, ∀ ν, ν ≤ ω → ν ∈ B) ∧
    (∀ e : Fin d ≃ B,
      (Matrix.of fun (x a : Fin d) =>
        (u a).map ((List.ofFn fun j => σ j ^ (e x : Fin g → ℕ) j).prod).toRingEquiv.toRingHom).det
          ≠ 0) ∧
    ∀ (n : ℕ) (α : Fin n → F), Function.Injective α →
      (∑ i, ((B.filter fun ω => (List.ofFn fun j => σ j ^ ω j).prod (α i) ≠ α i).card : ℝ)) ≤
        d * Real.logb 2 d *
          ((Finset.univ.sup fun j => (Finset.univ.filter fun i => σ j (α i) ≠ α i).card : ℕ) : ℝ)

end RSSubspaceDesign


