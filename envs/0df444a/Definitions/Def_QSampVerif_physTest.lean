-- Prove2me | Definitions.Def_QSampVerif_physTest
-- name    : QSampVerif_physTest
-- status  : Definition
-- author  : @iris
-- created : 2026-11-11T08:28:32.867573+00:00
-- url     : https://prove2.me/theorems/a47b04d4-d4ce-4eae-8a5a-a7f4700cd708
-- title:
--   The physical tests $p_{b,z,w}$ of (391)
-- statement:
--   For operators $A,B:\mathcal H_0\to\mathcal H_1$, $C,D:\mathcal H_2\to\mathcal H_3$, a map $\Phi:\mathcal L(\mathcal H_1)\to\mathcal L(\mathcal H_2)$, an operator $\xi$ on $\mathcal H_0$, an operator $M$ on $\mathcal H_3$ and phases $z,w$, set $A_z=(A+zB)/2$, $C_w=(C+wD)/2$ and
--
--   $$p_{z,w}=\mathrm{Tr}\bigl[M\,C_w\,\Phi(A_z\xi A_z^\dagger)\,C_w^\dagger\bigr].\qquad(391)$$
--
--   With $\Phi=\Phi_b$ this is the paper's $p_{b,z,w}$.
-- source:
--   Chung, Cojocaru, Lee, Lin, Classical Verification of Quantum Sampling with Negligible Error, STOC 2027 submission (held version, sha256 dbc19d8f…7ee7), (391), p.142 (PDF 143)

import Definitions.Def_QSampVerif_zPhase
import Definitions.Def_QAlgorithms_Defs_Channel

set_option autoImplicit false

namespace QSampVerif

open QAlgorithms
open scoped Matrix

/-- Chung, Cojocaru, Lee, Lin, STOC 2027 submission (held version, sha256 dbc19d8f…7ee7), (391),
p.142 (PDF 143): the physical tests `A_z = (A + zB)/2`, `C_w = (C + wD)/2` and
`p_{b,z,w} = Tr[M C_w Φ_b(A_z ξ A_z†) C_w†]`, for `z, w ∈ Z`. -/
noncomputable def physTest {ι₀ ι₁ ι₂ ι₃ : Type*} [Fintype ι₃]
    (M : Matrix ι₃ ι₃ ℂ) (C D : Matrix ι₃ ι₂ ℂ) (Φ : Superop ι₁ ι₂) (A B : Matrix ι₁ ι₀ ℂ)
    (ξ : Matrix ι₀ ι₀ ℂ) [Fintype ι₀] [Fintype ι₁] [Fintype ι₂] (z w : ℂ) : ℂ :=
  Matrix.trace (M * ((2⁻¹ : ℂ) • (C + w • D)) *
    Φ (((2⁻¹ : ℂ) • (A + z • B)) * ξ * ((2⁻¹ : ℂ) • (A + z • B))ᴴ) *
    ((2⁻¹ : ℂ) • (C + w • D))ᴴ)

end QSampVerif


