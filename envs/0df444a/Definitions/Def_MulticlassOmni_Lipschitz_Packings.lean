-- Prove2me | Definitions.Def_MulticlassOmni_Lipschitz_Packings
-- name    : MulticlassOmni_Lipschitz_Packings
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-09T22:09:36.220262+00:00
-- url     : https://prove2.me/theorems/6e0ac8be-e796-4754-82f9-56928d0dd41f
-- title:
--   Lemmas B.1–B.2 and §4.1, §5.1 — zero-sum sphere packings, simplex packings and the truncated packing domain
-- statement:
--   Norms and inner products are Euclidean, written as sums; $\bar v=(1/k,\dots,1/k)$ (`vbar`).
--
--   - `IsZeroSumPacking k ε X` (geometry of Lemma B.1): every $x\in X$ lies in $[-1,1]^k$, $\sum_yx_y=0$, $\|x\|_2^2=k/4$, and $\langle x,x'\rangle\le(k/4)(1-8000\varepsilon)$ for distinct $x,x'\in X$.
--   - `IsSimplexPacking Cpack k ε X` (conclusion of Lemma B.2 with constant $C_{\mathrm{pack}}$): $|X|\ge2^{-C_{\mathrm{pack}}k}\varepsilon^{-(k-2)/2}$ (143); $X\subseteq\Delta_k$; $\tfrac7{8k}\le x_y\le\tfrac9{8k}$ and $x_1\le\tfrac{15}{16k}$ (144); $\|x-\bar v\|_2^2=\tfrac1{256k}$ (145); $\langle x-\bar v,x'-\bar v\rangle\le\tfrac{1-8000\varepsilon}{256k}$ for distinct points (146).
--   - `IsSection41Packing Cpack k η x` (the domain of §4.1): $x:\mathrm{Fin}\,N\to\mathbb R^k$ enumerates without repetition $N=\min(|X_0|,\lfloor\eta^{-(k-2)/2}\rfloor)$ points of a set $X_0$ with `IsSimplexPacking Cpack k (16η/125) X₀` (the Lemma B.2 packing at scale $16\eta/125$, truncated to $\lfloor\eta^{-(k-2)/2}\rfloor$ points if larger).
--   - `IsGLMPacking k ε x` (the domain of §5.1): $x:\mathrm{Fin}\,N\to\mathbb R^k$ is injective, its range satisfies `IsZeroSumPacking k ε`, $4\mid N$ and $N\ge512$.
-- source:
--   Hu, Luo, Schneider, Yang (2026), Sample Complexity of Multiclass Omniprediction, supplied PDF (SHA-256 aaa73474…584f0, citation basis published; STOC 2027 submission), Lemma B.1 (p. 54), Lemma B.2 (p. 55), §4.1 (p. 16), Lemma B.3's proof (p. 56), §5.1 (pp. 26–27)

import Mathlib
import Definitions.Def_MulticlassOmni_Lipschitz_ProperLosses

namespace MulticlassOmni.Lipschitz

/-! # The packings of Lemmas B.1 and B.2 and the domain of Section 4.1

Hu, Luo, Schneider, Yang (2026), *Sample Complexity of Multiclass Omniprediction*, supplied PDF,
Lemma B.1 (p. 54), Lemma B.2 (p. 55), §4.1 (p. 16), §5.1 (pp. 26–27).

All norms and inner products are the Euclidean ones written as explicit sums. The source's label
`1` is the index `0 : Fin k`. -/

/-- The uniform distribution `v̄ = (1/k, …, 1/k)`. -/
noncomputable def vbar (k : ℕ) : Fin k → ℝ := fun _ => 1 / (k : ℝ)

/-- The geometric properties of a zero-sum sphere packing at scale `ε` (Lemma B.1, p. 54): every
`x ∈ X` lies in `[-1, 1]^k`, has `∑_y x_y = 0` and `‖x‖₂² = k/4`, and distinct points satisfy
`⟨x, x'⟩ ≤ (k/4)(1 - 8000 ε)`. (No cardinality condition.) -/
def IsZeroSumPacking (k : ℕ) (ε : ℝ) (X : Finset (Fin k → ℝ)) : Prop :=
  (∀ x ∈ X, ∀ y, x y ∈ Set.Icc (-1 : ℝ) 1) ∧
  (∀ x ∈ X, ∑ y, x y = 0) ∧
  (∀ x ∈ X, ∑ y, x y ^ 2 = (k : ℝ) / 4) ∧
  (∀ x ∈ X, ∀ x' ∈ X, x ≠ x' → dot x x' ≤ ((k : ℝ) / 4) * (1 - 8000 * ε))

/-- The conclusion of Lemma B.2 (p. 55) for the constant `Cpack` at scale `ε`: `X ⊆ Δ_k` is a
finite set with `|X| ≥ 2^{-Cpack k} ε^{-(k-2)/2}` (143) whose points satisfy the coordinate
bounds `7/(8k) ≤ x_y ≤ 9/(8k)` and `x_1 ≤ 15/(16k)` (144), lie on the sphere
`‖x - v̄‖₂² = 1/(256k)` (145), and are separated: `⟨x - v̄, x' - v̄⟩ ≤ (1 - 8000ε)/(256k)` for
distinct `x, x'` (146). -/
def IsSimplexPacking (Cpack : ℝ) (k : ℕ) (ε : ℝ) (X : Finset (Fin k → ℝ)) : Prop :=
  (2 : ℝ) ^ (-Cpack * k) * ε ^ (-((k : ℝ) - 2) / 2) ≤ (X.card : ℝ) ∧
  (∀ x ∈ X, x ∈ stdSimplex ℝ (Fin k)) ∧
  (∀ x ∈ X, ∀ y, 7 / (8 * (k : ℝ)) ≤ x y ∧ x y ≤ 9 / (8 * (k : ℝ))) ∧
  (∀ x ∈ X, ∀ y : Fin k, (y : ℕ) = 0 → x y ≤ 15 / (16 * (k : ℝ))) ∧
  (∀ x ∈ X, ∑ y, (x y - vbar k y) ^ 2 = 1 / (256 * (k : ℝ))) ∧
  (∀ x ∈ X, ∀ x' ∈ X, x ≠ x' →
    dot (x - vbar k) (x' - vbar k) ≤ (1 - 8000 * ε) / (256 * (k : ℝ)))

/-- The domain `X = {x_1, …, x_N}` of the Section 4.1 construction (p. 16; Lemma B.3's proof,
p. 56), enumerated without repetition by `x : Fin N → ℝ^k`: there is a set `X₀` satisfying the
conclusion of Lemma B.2 with constant `Cpack` at scale `τ = 16η/125`, and `X` consists of
`N = min(|X₀|, ⌊η^{-(k-2)/2}⌋)` distinct points of `X₀` (the packing, truncated to
`⌊η^{-(k-2)/2}⌋` points if it is larger). -/
def IsSection41Packing (Cpack : ℝ) (k : ℕ) (η : ℝ) {N : ℕ} (x : Fin N → Fin k → ℝ) : Prop :=
  ∃ X₀ : Finset (Fin k → ℝ), IsSimplexPacking Cpack k (16 * η / 125) X₀ ∧
    Function.Injective x ∧ (∀ i, x i ∈ X₀) ∧
    N = min X₀.card ⌊η ^ (-((k : ℝ) - 2) / 2)⌋₊

/-- The domain of the Section 5.1 (GLM) construction (pp. 26–27), enumerated without repetition
by `x : Fin N → ℝ^k`: its range is a zero-sum sphere packing at scale `ε` (Lemma B.1's geometric
properties), and `N` is a multiple of four with `N ≥ 512`. -/
def IsGLMPacking (k : ℕ) (ε : ℝ) {N : ℕ} (x : Fin N → Fin k → ℝ) : Prop :=
  Function.Injective x ∧ IsZeroSumPacking k ε (Finset.univ.image x) ∧ 4 ∣ N ∧ 512 ≤ N

end MulticlassOmni.Lipschitz


