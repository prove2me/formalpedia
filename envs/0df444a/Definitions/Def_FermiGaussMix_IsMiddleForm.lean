-- Prove2me | Definitions.Def_FermiGaussMix_IsMiddleForm
-- name    : FermiGaussMix_IsMiddleForm
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T20:58:37.081242+00:00
-- url     : https://prove2.me/theorems/e08d2608-f8ec-42e9-a5fa-ff8cded31296
-- title:
--   The middle operator $C=(\mathbf 1+\alpha\Gamma)\sigma$ and the terms $T_k$, $H_k$ of a label removal
-- statement:
--   Relative to a set $S$ of labels, a middle operator is $C=(\mathbf 1+\alpha\Gamma)\sigma$ with $\alpha\ge 0$, where $\Gamma=\varepsilon P_{R_0}$, $\varepsilon=\pm1$, is a Hermitian even monomial, and
--   $$
--   \sigma=c\prod_{e=(a,b)\in M}\bigl(\mathbf 1+s_e\,i\gamma_a\gamma_b\bigr),\qquad c\ge 0,\quad s_e\in\{\pm1\},
--   $$
--   with $M$ a collection of disjoint pairs in $S^c$ and $\Gamma$ disjoint from these pairs.
--
--   A realization of the random operator $Z$ is $Z=0$ or $Z=\zeta r2^{-|R|}P_R$ with $R\subseteq S$ even and $|\zeta|=1$. Given $Z_1,Z_2$, the seven terms are
--   $$
--   T_1=\alpha\Gamma,\ T_2=Z_1,\ T_3=Z_2,\ T_4=Z_1\alpha\Gamma,\ T_5=\alpha\Gamma Z_2,\ T_6=Z_1Z_2,\ T_7=Z_1\alpha\Gamma Z_2,
--   $$
--   with probabilities $p_1=\frac12$, $p_2=\dots=p_7=\frac1{12}$, and $H_k=\operatorname{Herm}(p_k^{-1}T_k)$, where $\operatorname{Herm}(Y)=(Y+Y^\dagger)/2$.
--
--   **Formalization Note** $\Gamma$ may be a scalar $\pm\mathbf 1$ ($R_0=\varnothing$), as the page needs when it reduces $\Gamma$ by quadratic factors. The pairs form a list so that the product is defined; the factors commute.
-- source:
--   Han, Zhao, Liu, Weakly interacting fermionic Gibbs states are Gaussian mixtures and classically simulable, arXiv:2609.35159v1, eqs. (B.23)–(B.24), (B.33), p. 14; (B.38)–(B.39), p. 15; (B.44), (B.46), p. 16

import Mathlib
import Definitions.Def_FermiGaussMix_P

open scoped BigOperators
open Matrix FermiCap.Gaussian

namespace FermiGaussMix

/-- The labels used by a list of pairs `e = (a, b)`. -/
def pairLabels {n : ℕ} (M : List (Fin (2 * n) × Fin (2 * n))) : Finset (Fin (2 * n)) :=
  (M.map (fun e => ({e.1, e.2} : Finset (Fin (2 * n))))).foldr (· ∪ ·) ∅

/-- The Gaussian part `σ = c Π_{e=(a,b)∈M} (1 + s_e iγ_aγ_b)` of eq. (B.24), p.14 (Han, Zhao, Liu,
arXiv:2609.35159v1).

**Formalization Note** `M` is a list so that the product is defined; its factors commute once the pairs are
disjoint (`IsMiddleForm`), so the order does not matter. -/
noncomputable def sigmaOp {n : ℕ} (c : ℝ) (M : List (Fin (2 * n) × Fin (2 * n)))
    (s : Fin (2 * n) × Fin (2 * n) → ℝ) : Op n :=
  (c : ℂ) • (M.map (fun e =>
    (1 : Op n) + ((s e : ℂ) * Complex.I) • (majorana n e.1 * majorana n e.2))).prod

/-- The form (B.23)–(B.24), p.14 (Han, Zhao, Liu, arXiv:2609.35159v1), of the data of a middle operator
`C = (1 + αΓ)σ` relative to `S`: `α ≥ 0`; `Γ = ε P_{R₀}` is a Hermitian even Majorana monomial; `c ≥ 0`; `s_e = ±1`;
`M` is a collection of disjoint pairs in `Sᶜ`; and `Γ` is disjoint from these pairs.

**Formalization Note** `Γ` carries a sign `ε = ±1` and may be a scalar (`R₀ = ∅`), as p.17 needs ("replace `Γ` by
`-Γ₋`", "reduces `Γ` to `±1`"). -/
def IsMiddleForm {n : ℕ} (S : Finset (Fin (2 * n))) (α ε : ℝ) (R₀ : Finset (Fin (2 * n))) (c : ℝ)
    (M : List (Fin (2 * n) × Fin (2 * n))) (s : Fin (2 * n) × Fin (2 * n) → ℝ) : Prop :=
  0 ≤ α ∧ (ε = 1 ∨ ε = -1) ∧ Even R₀.card ∧ 0 ≤ c ∧
  (∀ e ∈ M, s e = 1 ∨ s e = -1) ∧
  (∀ e ∈ M, e.1 ≠ e.2) ∧
  M.Pairwise (fun e f => e.1 ≠ f.1 ∧ e.1 ≠ f.2 ∧ e.2 ≠ f.1 ∧ e.2 ≠ f.2) ∧
  Disjoint (pairLabels M) S ∧
  Disjoint (pairLabels M) R₀

/-- A realization of the random operator `Z` of eqs. (B.33), p.14, and (B.46), p.16 (Han, Zhao, Liu,
arXiv:2609.35159v1), relative to `S` and the constant `r`: either `Z = 0` or `Z = ζ r 2^{-|R|} P_R`, where `R ⊆ S` is
even and `|ζ| = 1`. -/
def IsZRealization {n : ℕ} (S : Finset (Fin (2 * n))) (r : ℝ) (Z : Op n) : Prop :=
  Z = 0 ∨ ∃ (ζ : ℂ) (R : Finset (Fin (2 * n))),
    ‖ζ‖ = 1 ∧ R ⊆ S ∧ Even R.card ∧ Z = (ζ * (r : ℂ) * (2 : ℂ)⁻¹ ^ R.card) • P n R

/-- The seven terms `T₁ = αΓ, T₂ = Z₁, T₃ = Z₂, T₄ = Z₁αΓ, T₅ = αΓZ₂, T₆ = Z₁Z₂, T₇ = Z₁αΓZ₂`, eq. (B.38), p.15
(Han, Zhao, Liu, arXiv:2609.35159v1). Here `Γ = ε P_{R₀}`. -/
noncomputable def termT {n : ℕ} (α ε : ℝ) (R₀ : Finset (Fin (2 * n))) (Z₁ Z₂ : Op n) : Fin 7 → Op n :=
  let αΓ : Op n := ((α : ℂ) * (ε : ℂ)) • P n R₀
  ![αΓ, Z₁, Z₂, Z₁ * αΓ, αΓ * Z₂, Z₁ * Z₂, Z₁ * αΓ * Z₂]

/-- The probabilities `p₁ = 1/2, p₂ = ⋯ = p₇ = 1/12`, eq. (B.44), p.16 (Han, Zhao, Liu, arXiv:2609.35159v1). -/
noncomputable def pk : Fin 7 → ℝ := ![1 / 2, 1 / 12, 1 / 12, 1 / 12, 1 / 12, 1 / 12, 1 / 12]

/-- `H_k = Herm(p_k^{-1} T_k)`, with `Herm(Y) = (Y + Y†)/2`, eq. (B.39), p.15 (Han, Zhao, Liu,
arXiv:2609.35159v1). -/
noncomputable def hOp {n : ℕ} (α ε : ℝ) (R₀ : Finset (Fin (2 * n))) (Z₁ Z₂ : Op n) (k : Fin 7) : Op n :=
  let Y : Op n := ((pk k)⁻¹ : ℂ) • termT α ε R₀ Z₁ Z₂ k
  (2 : ℂ)⁻¹ • (Y + Yᴴ)

end FermiGaussMix


