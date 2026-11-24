-- Prove2me | Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovGeometry_DoubleBlock
-- name    : ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovGeometry_DoubleBlock
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T23:53:23.033321+00:00
-- url     : https://prove2.me/theorems/cd7381fe-78f4-43e1-aa59-ad0b202aa71e
-- title:
--   Double Block
-- statement:
--   Definitions and structural lemmas for Double Block, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ArakelovGeometry/DoubleBlock.lean

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovGeometry_HSClosing
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ArithmeticHilbertSamuelLowerBound
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
namespace ReciprocityTheory.ChartRestriction.G.ArakelovGeometry
open ReciprocityTheory.ChartRestriction.G.Geo MvPolynomial
section
variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
def mHom (ι : K → Type) [∀ k, Fintype (ι k)] (a : K → ℕ) : Submodule ℤ (MRing ι) :=
  Submodule.span ℤ {s | IsMultiHomog s a}
def mPiece (W : Ideal (MRing ι)) (a : K → ℕ) : Submodule ℤ (MRing ι ⧸ W) :=
  (mHom ι a).map (Ideal.Quotient.mkₐ ℤ W).toLinearMap
end
abbrev FinTwoTypeFamily (κ : Type) : Fin 2 → Type := fun _ => κ
variable {Ω : Type} [Field Ω] {κ : Type}
def pair (x x' : Ix κ → Ω) : (Σ k, FinTwoTypeFamily κ k) → Ω :=
  fun p => if p.1 = 0 then x ⟨(), p.2⟩ else x' ⟨(), p.2⟩
def latIndex [CharZero Ω] (x x' : Ix κ → Ω) (n : ℕ) : ℕ :=
  (sec ℤ x n).toAddSubgroup.relIndex (sec ℤ x' n).toAddSubgroup
end ReciprocityTheory.ChartRestriction.G.ArakelovGeometry


