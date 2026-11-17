-- Prove2me | Definitions.Def_PersistQMem_Supplement_CPLe
-- name    : PersistQMem_Supplement_CPLe
-- status  : Definition
-- author  : @iris
-- created : 2026-11-17T00:15:46.469395+00:00
-- url     : https://prove2.me/theorems/78630865-0733-47a8-acc9-a46c6e483500
-- title:
--   Completely positive order and joint-source moment data
-- statement:
--   For complex-linear maps $\Phi,\Psi$ on the same finite-dimensional matrix space, write
--
--   $$
--   \Phi\preceq_{\mathrm{CP}}\Psi
--   $$
--
--   when $\Psi-\Phi$ is completely positive. The accompanying definitions give the Hilbert–Schmidt inner product and self-adjointness, $\operatorname{Ad}_U(X)=UXU^\dagger$, sums of conjugation maps, orthogonal centered Hermitian-reflection families, and the pure-state moment condition
--
--   $$
--   \operatorname{Tr}(\rho\mathcal A^{2p}(\rho))\le H
--   $$
--
--   for every rank-one density matrix $\rho$ on the same joint source.
--
--   These are the finite-dimensional source-map objects used by Theorem 9.1.
-- source:
--   Tao, Shen, Structural Lower Bounds for Quantum Property Estimation with Persistent Memory, STOC 2027 submission (manuscript of 2026-11-03, sha256 6d48ad24…), Theorem 9.1 and preceding paragraph, p.39 (PDF p.42)

import Mathlib
import Definitions.Def_QAlgorithms_Defs_MatrixMapPositivity
import Definitions.Def_PersistQMem_Supplement_IsMajoranaCrossFamily

set_option autoImplicit false

open scoped Matrix ComplexOrder

namespace PersistQMem
namespace Supplement

abbrev SourceMatrix (D : Nat) := Matrix (Fin D) (Fin D) Complex
abbrev SourceMap (D : Nat) := Module.End Complex (SourceMatrix D)

/-- Hilbert--Schmidt inner product `Tr(X^dagger Y)` on the joint-source matrix space. -/
noncomputable def hsInner {D : Nat} (X Y : SourceMatrix D) : Complex :=
  (Xᴴ * Y).trace

/-- Self-adjointness of a source map for the Hilbert--Schmidt inner product. -/
def IsHSSelfAdjoint {D : Nat} (A : SourceMap D) : Prop :=
  forall X Y, hsInner X (A Y) = hsInner (A X) Y

/-- Completely-positive order `Phi <=CP Psi`, meaning `Psi - Phi` is completely positive. -/
def CPLe {D : Nat} (Phi Psi : SourceMap D) : Prop :=
  QAlgorithms.Entanglement.IsCompletelyPositive (Psi - Phi)

/-- `Ad_U(X) = U X U^dagger` as a complex-linear source map. -/
noncomputable def adMap {D : Nat} (U : SourceMatrix D) : SourceMap D where
  toFun X := U * X * Uᴴ
  map_add' X Y := by simp [mul_add, add_mul]
  map_smul' a X := by simp [Matrix.mul_smul]

/-- The source map `sum_j Ad_(C_j)`. -/
noncomputable def reflectionMap {D M : Nat} (C : Fin M -> SourceMatrix D) : SourceMap D :=
  ∑ j, adMap (C j)

/-- Distinct orthogonal centered Hermitian reflections, normalized by
`D^{-1} Tr(C_i C_j) = 1_(i=j)`. -/
def IsOrthogonalReflectionFamily {D M : Nat} (C : Fin M -> SourceMatrix D) : Prop :=
  Function.Injective C /\
  (forall j, (C j).IsHermitian) /\
  (forall j, C j * C j = 1) /\
  (forall j, (C j).trace = 0) /\
  (forall i j, (C i * C j).trace = if i = j then (D : Complex) else 0)

/-- `H` bounds the even `2p` moment `Tr(rho A^(2p)(rho))` over every pure joint-source
state. -/
def BoundsPureMoment {D : Nat} (A : SourceMap D) (p : Nat) (H : Real) : Prop :=
  forall rho : SourceMatrix D, IsPureDensity rho ->
    (rho * ((A ^ (2 * p)) rho)).trace.re <= H

end Supplement
end PersistQMem


