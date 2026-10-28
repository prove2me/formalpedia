-- Prove2me | Definitions.Def_KLSModular_FunctionalInequalities_KLS_BKL_CumulantEnergy_Basic
-- name    : KLSModular_FunctionalInequalities_KLS_BKL_CumulantEnergy_Basic
-- status  : Definition
-- author  : @Lazyfill
-- created : 2026-10-25T16:00:53.189489+00:00
-- url     : https://prove2.me/theorems/4f12a1ef-12d3-46f5-b544-7dda9d084086
-- title:
--   Cumulant energies and localization drift terms
-- statement:
--   For a measure $\nu$ on $\mathrm{EuclideanSpace}\,\mathbb{R}\,(\mathrm{Fin}\,n)$, `cumulantEnergy ν r u` is the finite sum over $J:\mathrm{Fin}\,r\to\mathrm{Fin}\,n$ of squared cumulants of order $r+1$, with first slot $u$ and remaining slots given by the inverse-square-root covariance operator applied to standard basis vectors. `lowerDrift ν h i₀` sums the covariance-inverse pairings of cumulant vectors over Boolean masks containing slot $i₀$ and having at least two selected and at least two unselected slots. The auxiliary definitions `maskCount`, `sigmaBasis`, `maskTerm`, `middleMasks`, and `pairTerm` expose the corresponding mask counts, whitened basis vectors, individual summands, admissible masks, and squared pair terms.
--
--   **Original module imports**
--
--   ```lean
--   import FunctionalInequalities.Analysis.BakryEmery.Cumulant.Leibniz
--   import FunctionalInequalities.Analysis.Operator.InverseSqrt
--   ```
--
--   **Original declaration excerpt**
--
--   Shown in the original module context.
--
--   ```lean
--   def lowerDrift (ν : Measure (EuclideanSpace ℝ (Fin n))) {m : ℕ} (h : Fin m → EuclideanSpace ℝ (Fin n))
--       (i₀ : Fin m) : ℝ :=
--     ∑ q ∈ Finset.univ.filter (fun q : Fin m → Bool =>
--         q i₀ = true ∧ 2 ≤ (selected h q).length ∧ 2 ≤ (selected h (fun i => !(q i))).length),
--       ⟪cumulantVector ν (selected h q),
--         Ring.inverse (Covariance.operator ν) (cumulantVector ν (selected h (fun i => !(q i))))⟫
--   ```
--
--   **Module navigation**
--
--   Direct project imports: [`Analysis/BakryEmery/Cumulant/Leibniz`](https://prove2.me/theorems/dc69b9b3-3173-4efb-aee3-b6d1282be46f), [`Analysis/Operator/InverseSqrt`](https://prove2.me/theorems/2794bd57-af01-4015-a91a-cb7827d3a533).
--
--   Theorems in source order:
--
--   - [`sum_selected_eq`](https://prove2.me/theorems/fa7bea17-a11a-4926-a7d5-5e7c584f47ec)
--   - [`sqrt_sum_sq_sum_le`](https://prove2.me/theorems/f159c409-0b24-4a71-8718-4a4409e0445e)
--   - [`sum_sq_pairTerm_ofFn_le`](https://prove2.me/theorems/dd204f83-a393-4ef0-af4b-7c00fc22f487)
--   - [`sqrt_sum_lowerDrift_sq_le_aux`](https://prove2.me/theorems/6205a939-9cd4-490f-9fe8-892a2e4d1cda)
--
--   Project result: [The KLS conjecture](https://prove2.me/theorems/c4e9e57c-586c-4945-927e-7f33933f1111).
--
--   [Original module](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/FunctionalInequalities/KLS/BKL/CumulantEnergy/Basic.lean) · `FunctionalInequalities.KLS.BKL.CumulantEnergy.Basic` · Frozen source `408915f`.
-- source:
--   Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/KLS/BKL/CumulantEnergy/Basic.lean#L22-L380 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.KLS.BKL.CumulantEnergy.Basic`, definition bundle `KLSModular_FunctionalInequalities_KLS_BKL_CumulantEnergy_Basic`; the repository is private at upload time).

import Definitions.Def_KLSModular_FunctionalInequalities_Analysis_BakryEmery_Cumulant_Leibniz
import Definitions.Def_KLSModular_FunctionalInequalities_Analysis_Operator_InverseSqrt

noncomputable section
open MeasureTheory
open FunctionalInequalities.Analysis FunctionalInequalities.Analysis.BakryEmery
open scoped RealInnerProductSpace
namespace FunctionalInequalities
namespace KLS
namespace BKL
variable {n : ℕ}
/-- The middle term `L_m` of BKL arXiv:2610.05474v1, (72), at a fixed law `ν` with covariance `A`:
`L_m(h) = Σ_{J ∋ i₀, 2 ≤ |J|, |Jᶜ| ≥ 2} ⟪κ_{|J|+1}(h_J, ·), A⁻¹ κ_{m−|J|+1}(h_{Jᶜ}, ·)⟫` (slot `i₀ = 0`). -/
def lowerDrift (ν : Measure (EuclideanSpace ℝ (Fin n))) {m : ℕ} (h : Fin m → EuclideanSpace ℝ (Fin n))
    (i₀ : Fin m) : ℝ :=
  ∑ q ∈ Finset.univ.filter (fun q : Fin m → Bool =>
      q i₀ = true ∧ 2 ≤ (selected h q).length ∧ 2 ≤ (selected h (fun i => !(q i))).length),
    ⟪cumulantVector ν (selected h q),
      Ring.inverse (Covariance.operator ν) (cumulantVector ν (selected h (fun i => !(q i))))⟫
/-- The cumulant energy `E_{r+1} = |κ_{r+1}(u)|²_A = Σ_J κ_{r+1}(u, σ e_{J_1}, …, σ e_{J_r})²`, `σ = A^{-1/2}`
(BKL (75)–(76)). -/
def cumulantEnergy (ν : Measure (EuclideanSpace ℝ (Fin n))) (r : ℕ) (u : EuclideanSpace ℝ (Fin n)) : ℝ :=
  ∑ J : Fin r → Fin n, cumulant ν (r + 1)
    (Fin.cons u fun k => inverseSqrt (Covariance.operator ν) (EuclideanSpace.basisFun (Fin n) ℝ (J k))) ^ 2
end BKL
end KLS
end FunctionalInequalities
section S4Section6Pointwise
open MeasureTheory
open FunctionalInequalities.Analysis FunctionalInequalities.Analysis.BakryEmery
open scoped RealInnerProductSpace
namespace FunctionalInequalities
namespace KLS
namespace BKL
variable {n : ℕ}
section Masks
/-- number of selected slots -/
def maskCount {k : ℕ} (q : Fin k → Bool) : ℕ := (Finset.univ.filter fun i => q i = true).card
end Masks
section Algebra
/-- `σ e_j` -/
def sigmaBasis (ν : Measure (EuclideanSpace ℝ (Fin n))) (j : Fin n) : EuclideanSpace ℝ (Fin n) :=
  inverseSqrt (Covariance.operator ν) (EuclideanSpace.basisFun (Fin n) ℝ j)
/-- One mask summand of `lowerDrift`. -/
def maskTerm (ν : Measure (EuclideanSpace ℝ (Fin n))) {m : ℕ} (h : Fin m → EuclideanSpace ℝ (Fin n))
    (q : Fin m → Bool) : ℝ :=
  ⟪cumulantVector ν (selected h q),
    Ring.inverse (Covariance.operator ν) (cumulantVector ν (selected h (fun i => !(q i))))⟫
/-- The masks of the middle allocations: slot `0` selected, at least two slots on each side. -/
def middleMasks (k : ℕ) : Finset (Fin (k + 1) → Bool) :=
  Finset.univ.filter fun q => q 0 = true ∧ 2 ≤ maskCount q ∧ 2 ≤ maskCount (fun i => !(q i))
/-- The squared pair term `⟪κ(u, l₁, ·), A⁻¹ κ(l₂, ·)⟫²` as a function of the two selected lists. -/
def pairTerm (ν : Measure (EuclideanSpace ℝ (Fin n))) (u : EuclideanSpace ℝ (Fin n))
    (l₁ l₂ : List (EuclideanSpace ℝ (Fin n))) : ℝ :=
  ⟪cumulantVector ν (u :: l₁), Ring.inverse (Covariance.operator ν) (cumulantVector ν l₂)⟫ ^ 2
end Algebra
end BKL
end KLS
end FunctionalInequalities
end S4Section6Pointwise


