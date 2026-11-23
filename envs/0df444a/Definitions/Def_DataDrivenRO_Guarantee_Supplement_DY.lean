-- Prove2me | Definitions.Def_DataDrivenRO_Guarantee_Supplement_DY
-- name    : DataDrivenRO_Guarantee_Supplement_DY
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-23T19:48:56.507811+00:00
-- url     : https://prove2.me/theorems/3285afc4-ebc7-4495-a5a7-8220ca89218b
-- title:
--   Theorem 12, p. 27 — the box moment region, set (36), and printed SDP
-- statement:
--   Fix a coordinatewise box $[l,h]\subset\mathbb R^d$, a mean $\hat\mu$, a symmetric positive definite covariance $\hat\Sigma$, nonnegative thresholds $g_1,g_2$, and $C^TC=\hat\Sigma^{-1}$. The region $\mathcal P^{DY}$ consists of box-supported probability measures with
--   $$
--   (\mathbb E_P[u]-\hat\mu)^T\hat\Sigma^{-1}(\mathbb E_P[u]-\hat\mu)\le g_1,
--   \qquad \mathbb E_P[(u-\hat\mu)(u-\hat\mu)^T]\preceq g_2\hat\Sigma.
--   $$
--   The bundle also defines the lifted set (36) and the set of feasible objective values $t$ of the printed SDP in Theorem 12, keeping every decision variable and both block matrix constraints. This provides a direct interface for comparing the set's support with the SDP value.
--
--   **Formalization Note** A positive semidefinite matrix is Mathlib's `Matrix.PosSemidef`, which includes symmetry over the reals. The block matrix uses `Unit ⊕ Fin d`. Euclidean norms are square roots of dot products; the weighted norm is explicitly $\|x\|_M=\sqrt{x^TMx}$. Thus the SDP uses $\hat\Sigma^{-1}$ exactly as required by the brief. The paper never separately defines this subscript convention; the resulting counterexample is conditional on this explicit reading. Support in the box means its complement has measure zero. All coordinates and products are integrable on this bounded support; nonprobability or unsupported measures never qualify. No infimum is computed by a default-valued real operation: `sdpPrinted` is the set of feasible objective values, to be used with `IsGLB`.
-- source:
--   Bertsimas, Gupta & Kallus, Data-Driven Robust Optimization, arXiv:1401.0212v2, §8.2, Theorem 11 region, p. 26; Theorem 12, (36) and SDP, p. 27; (EC.12)–(EC.14), pp. ec8–ec9 (PDF 46–47)

import Mathlib
import Definitions.Def_DataDrivenRO_Guarantee_Setting

open MeasureTheory

namespace DataDrivenRO.Guarantee.Supplement

/-- Box support of §5.1, used in Theorem 11 and (36). -/
def box {d : ℕ} (lo hi : Fin d → ℝ) : Set (Fin d → ℝ) :=
  {u | ∀ i, lo i ≤ u i ∧ u i ≤ hi i}

/-- The quadratic norm with weight M. All uses below have M positive definite. -/
noncomputable def weightedNorm {d : ℕ} (M : Matrix (Fin d) (Fin d) ℝ)
    (x : Fin d → ℝ) : ℝ := Real.sqrt (x ⬝ᵥ M.mulVec x)

/-- The symmetric block matrix used in (36) and the SDP. -/
def momentBlock {d : ℕ} (s : ℝ) (x : Fin d → ℝ)
    (A : Matrix (Fin d) (Fin d) ℝ) : Matrix (Unit ⊕ Fin d) (Unit ⊕ Fin d) ℝ :=
  Matrix.fromBlocks (fun _ _ => s) (fun _ j => x j) (fun i _ => x i) A

/-- Theorem 11's region with the bootstrap thresholds of Theorem 12. -/
def regionDY {d : ℕ} (lo hi mu : Fin d → ℝ)
    (Sigma : Matrix (Fin d) (Fin d) ℝ) (g1 g2 : ℝ) :
    Set (Measure (Fin d → ℝ)) :=
  {P | IsProbabilityMeasure P ∧ P (box lo hi)ᶜ = 0 ∧
    let m : Fin d → ℝ := fun i => ∫ u, u i ∂P
    (m - mu) ⬝ᵥ (Sigma⁻¹).mulVec (m - mu) ≤ g1 ∧
    (g2 • Sigma - (Matrix.of (fun i j => ∫ u, (u i - mu i) * (u j - mu j) ∂P))).PosSemidef}

/-- (36), with Euclidean norms written as square roots of dot products. -/
def UDY {d : ℕ} (lo hi mu : Fin d → ℝ)
    (Sigma C : Matrix (Fin d) (Fin d) ℝ) (g1 g2 ε : ℝ) : Set (Fin d → ℝ) :=
  {u | u ∈ box lo hi ∧ ∃ (lam : ℝ) (w m : Fin d → ℝ)
      (A Ah : Matrix (Fin d) (Fin d) ℝ),
    A.PosSemidef ∧ Ah.PosSemidef ∧ lam ≤ 1 / ε ∧
    (∀ i, (lam - 1) * lo i ≤ m i ∧ m i ≤ (lam - 1) * hi i) ∧
    (momentBlock (lam - 1) m A).PosSemidef ∧
    (momentBlock 1 u Ah).PosSemidef ∧
    lam • mu = m + u + w ∧
    Real.sqrt (C.mulVec w ⬝ᵥ C.mulVec w) ≤ lam * Real.sqrt g1 ∧
    (lam • (g2 • Sigma + Matrix.vecMulVec mu mu) - A - Ah -
      Matrix.vecMulVec w mu - Matrix.vecMulVec mu w).PosSemidef}

/-- Feasible objective values of the *printed* SDP in Theorem 12.
The weighted norm uses Sigma⁻¹, as printed and as specified in the brief. -/
def sdpPrinted {d : ℕ} (lo hi mu : Fin d → ℝ)
    (Sigma : Matrix (Fin d) (Fin d) ℝ) (g1 g2 ε : ℝ) (v : Fin d → ℝ) : Set ℝ :=
  {t | ∃ (r s theta : ℝ) (q yp1 ym1 yp2 ym2 : Fin d → ℝ)
      (Z : Matrix (Fin d) (Fin d) ℝ),
    Z.IsHermitian ∧ 0 ≤ theta ∧
    (∀ i, 0 ≤ yp1 i ∧ 0 ≤ ym1 i ∧ 0 ≤ yp2 i ∧ 0 ≤ ym2 i) ∧
    r + s ≤ theta * ε ∧
    (momentBlock (r + yp1 ⬝ᵥ lo - ym1 ⬝ᵥ hi)
      ((1 / 2 : ℝ) • (q - (yp1 - ym1))) Z).PosSemidef ∧
    (momentBlock (r + yp2 ⬝ᵥ lo - ym2 ⬝ᵥ hi + t - theta)
      ((1 / 2 : ℝ) • (q - (yp2 - ym2) - v)) Z).PosSemidef ∧
    (∑ i, ∑ j, (g2 * Sigma i j + mu i * mu j) * Z i j) + mu ⬝ᵥ q +
      Real.sqrt g1 * weightedNorm (Sigma⁻¹) (q + 2 • Z.mulVec mu) ≤ s}

end DataDrivenRO.Guarantee.Supplement


