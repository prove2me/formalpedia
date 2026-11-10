-- Prove2me | Definitions.Def_RandomDimReduction_Channel_Algorithm
-- name    : RandomDimReduction_Channel_Algorithm
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-09T11:24:35.605245+00:00
-- url     : https://prove2.me/theorems/02e27c6e-371c-4b9f-bdf7-2bc96765a8e4
-- title:
--   Algorithm 5.2 as a composition of channel operations
-- statement:
--   Apply the input Schur transform, measure the partition label and retain each unnormalized branch. A label of height greater than $k$ terminates with the maximally mixed state on the output tensor register. Otherwise preserve the Specht factor, take the partial trace over its Weyl factor, append a maximally mixed output Weyl factor, include that block in the output Schur space, and conjugate by the inverse output Schur transform. The full channel sums the branches.
--
--   The replacement step is
--   $$ Y\longmapsto\operatorname{tr}_{V_\lambda^d}(Y)\otimes\frac{I_{V_\lambda^k}}{\dim V_\lambda^k}. $$
--   This operational definition is independent of the integral-defined reduction and of the displayed identity in Theorem 5.3.
-- source:
--   Angus Lowe, Xinyu Tan, Random dimension reduction and learning symmetric properties of quantum states, STOC 2027 submission #994 (October 2026), Algorithm 5.2, p.16. https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/994.pdf

import Definitions.Def_RandomDimReduction_Channel_Schur

set_option autoImplicit false

noncomputable section
open Matrix
open scoped Matrix ComplexConjugate Matrix.Norms.Elementwise

namespace RandomDimReduction.Channel
attribute [local instance] Classical.propDecidable Classical.decEq

/-- Step 2: the unnormalized post-measurement lam branch of the Schur register. -/
def measureLabel {n d : ℕ} (Y : Op (SchurIndex n d)) (lam : Shape n) :
    Op (Fin (spechtDim lam) × Fin (weylDim d lam)) :=
  fun i j => Y ⟨lam, i⟩ ⟨lam, j⟩

/-- Inclusion of one block into the direct sum; its adjoint extracts that block. -/
def includeLabel {n k : ℕ} (lam : Shape n) :
    Matrix (SchurIndex n k) (Fin (spechtDim lam) × Fin (weylDim k lam)) ℂ :=
  fun i j => if i = ⟨lam, j⟩ then 1 else 0

/-- Step 3: discard the old Weyl register, append a fresh maximally mixed one. -/
def replaceWeyl {n : ℕ} (k d : ℕ) (lam : Shape n)
    (Y : Op (Fin (spechtDim lam) × Fin (weylDim d lam))) :
    Op (Fin (spechtDim lam) × Fin (weylDim k lam)) :=
  Matrix.kronecker (WildeQIT.partialTraceRight Y)
    (((weylDim k lam : ℂ)⁻¹) • (1 : Op (Fin (weylDim k lam))))

/-- Steps 2–4 on one measured branch; the high-label branch terminates
with I/k^n. The low branch preserves Specht, replaces Weyl, and applies U_k†. -/
def finishBranch {n k d : ℕ} {κ : SpechtModel n} (Sk : SchurTransform κ k)
    (lam : Shape n) (Y : Op (Fin (spechtDim lam) × Fin (weylDim d lam))) :
    Op (Word n k) :=
  if k < height lam then (Y.trace / (k ^ n : ℕ)) • 1 else
    Sk.Uᴴ * (includeLabel (k := k) lam * replaceWeyl k d lam Y * (includeLabel (k := k) lam)ᴴ) * Sk.U

/-- Algorithm 5.2 defined by composition of its four operations, independently
of Eq.(3) and independently of the closed block formula in Theorem 5.3. -/
def algorithm52 {n k d : ℕ} {κ : SpechtModel n}
    (Sd : SchurTransform κ d) (Sk : SchurTransform κ k)
    (X : Op (Word n d)) : Op (Word n k) :=
  let afterStep1 := Sd.U * X * Sd.Uᴴ
  ∑ lam : Shape n, finishBranch Sk lam (measureLabel afterStep1 lam)

end RandomDimReduction.Channel


