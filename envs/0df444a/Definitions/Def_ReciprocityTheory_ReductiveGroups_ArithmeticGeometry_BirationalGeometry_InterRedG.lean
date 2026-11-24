-- Prove2me | Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterRedG
-- name    : ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterRedG
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T00:07:08.092693+00:00
-- url     : https://prove2.me/theorems/adb15ad8-1f20-4d70-bbe5-98eff2370c76
-- title:
--   Inter Red G
-- statement:
--   Definitions and structural lemmas for Inter Red G, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/BirationalGeometry/InterRedG.lean

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterRedF
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
namespace ReciprocityTheory.ChartRestriction.G.Geo
open MvPolynomial ReciprocityTheory.AnForm.M
section Alg
variable {K : Type*} [Fintype K] {ι : K → Type*} [∀ k, Fintype (ι k)]
def secOf (i : ∀ k, ι k) (b : K → ℕ) : MRing ι := ∏ k, X ⟨k, i k⟩ ^ b k
def eLine : HermLine ι := HermLine.ofWeight (fun _ => -1) (fun _ _ _ => rfl)
end Alg
def GeoCutStatement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (P : Ideal (MRing ι)) (n : ℕ)
    (s : MRing ι) (b : K → ℕ) (a : Fin n → K → ℤ) (p : ℕ),
    IsArithVar P (n + 2) → IsMultiHomog s b → s ∉ P → p.Prime →
    ∑ᶠ V ∈ divSupp P (C (p : ℤ)), (multAt (P ⊔ Ideal.span {C (p : ℤ)}) V : ℝ) *
        (geoNum (n + 1) V (Fin.snoc a fun k => (b k : ℤ)) : ℝ) =
      ∑ᶠ (W) (_ : W ∈ divSupp P s ∧ IsHorizontal W), (multAt (P ⊔ Ideal.span {s}) W : ℝ) *
        ∑ᶠ V ∈ divSupp W (C (p : ℤ)), (multAt (W ⊔ Ideal.span {C (p : ℤ)}) V : ℝ) *
          (geoNum n V a : ℝ)
def DegreeBaseStatement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (P : Ideal (MRing ι))
    (L : Fin 0 → HermLine ι) (p : ℕ), IsArithVar P 1 → p.Prime →
    ptsIntegral P (pot L) (fun _ => 1) =
      ∑ᶠ V ∈ divSupp P (C (p : ℤ)),
        (multAt (P ⊔ Ideal.span {C (p : ℤ)}) V : ℝ) * (geoNum 0 V (fun j => (L j).a) : ℝ)
end ReciprocityTheory.ChartRestriction.G.Geo


