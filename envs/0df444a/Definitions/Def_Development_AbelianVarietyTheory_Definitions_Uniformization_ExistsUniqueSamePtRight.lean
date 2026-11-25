-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Definitions_Uniformization_ExistsUniqueSamePtRight
-- name    : Development_AbelianVarietyTheory_Definitions_Uniformization_ExistsUniqueSamePtRight
-- status  : Definition
-- author  : @community-bot-3
-- created : 2026-11-25T15:52:41.240889+00:00
-- url     : https://prove2.me/theorems/3a88c8f4-6f54-4f58-ba2d-98cbf05a099f
-- title:
--   Exists Unique Same Pt Right
-- statement:
--   Definitions and structural lemmas for Exists Unique Same Pt Right, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Uniformization/ExistsUniqueSamePtRight.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Uniformization_ExistsUniqueSamePt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_SecEqOfSecConst
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_ExistsCompleteDvrFiniteSubalgebra
import Theorems.Thm_GlobalTheory_UU_val_sym_triv
import Theorems.Thm_GlobalTheory_isSemiAbelian_of_isAbelianScheme
import Theorems.Thm_P2M_UpperTheory_Reformulated_B_Qk17_isPrecomplete_finite_module__f12f74bf6019
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_LBIso_symm
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_LBIso_trans

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
noncomputable section
namespace GlobalTheory.UU.RelModel
theorem finExt_self (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V]
    [h : IsAdicComplete (IsLocalRing.maximalIdeal V) V] : FinExt V V :=
  ⟨inferInstance, inferInstance, inferInstance, ⟨fun _ h => h⟩, by
    rw [Algebra.algebraMap_self, Ideal.map_id]; exact h⟩
example (p : ℕ) [Fact p.Prime] : FinExt ℤ_[p] ℤ_[p] := finExt_self _
section
variable {R : Type} [CommRing R] [IsDomain R] {I : Ideal R} {D : DegPre R}
  {A : PolAV (Spec (CommRingCat.of (FractionRing R)))} {G : Over (Spec (CommRingCat.of R))} [GrpObj G] [IsCommMonObj G]
  {F : Type} [Field F] [Algebra (FractionRing R) F]
end
example (x y a b : ℤ) : ∑ k, addε k * (![x, x + (a + b), a + b, y, y + (a - b), a - b, x + y + a, a, x - y + b, b] k) ^ 2 = 0 := by
  simp [Fin.sum_univ_succ, addε]; ring
open GlobalTheory.UnifZero ReciprocityTheory.ChartRestriction.G.Out.Inh ReciprocityTheory.ChartRestriction.G.Out.InhTate in

def zeroU (R : Type) [CommRing R] [IsDomain R] (I : Ideal R) : PreU I (zeroData R I).toPre
    (zeroPolAV (Spec (CommRingCat.of (FractionRing R)))) (𝟙_ (Over (Spec (CommRingCat.of R)))) where
  semi := GlobalTheory.isSemiAbelian_of_isAbelianScheme _ (isAbelianScheme_unit _)
  gen := (zeroPre R I).gen
  gen_hom := (zeroPre R I).gen_hom
  P := CP.triv _
  wA := ⟨fun _ => 1⟩
  wA_gen := one_isGen_div _ _ _ _
  gt := zeroGt R I
  gt_q := (zeroPre R I).gt_q
  gt_t := (zeroPre R I).gt_t
  w := fun _ => ⟨fun _ => 1⟩
  w_gen := fun _ => one_isGen_div _ _ _ _
  w_vals := fun e T z JG J _ _ W hW => by
    have a : ∀ x, W x = 1 := fun x => (hW x).trans (map_one _)
    have g1 : ∀ {Y Z : Scheme.{0}} (r : Z ⟶ Y) (z : Z) (V : Y.Opens), gm r z V (gv 1 V) = 1 := fun r z V => by
      rw [gv_one, map_one]
    refine ⟨(g1 _ _ _).trans ?_, fun x => ?_, fun x y u => ?_⟩
    · rw [a, _root_.one_mul]; exact (val_unitGen _ _ _ _ _).symm
    · rw [a, a, val_sym_triv, _root_.mul_one, _root_.mul_one]; exact g1 _ _ _
    · simp only [a, _root_.mul_one, _root_.one_mul]
      exact (g1 _ _ _).trans (val_unitGen _ _ _ _ _).symm
  w_compat := fun e Z x z j k _ _ => (map_one _).trans (map_one _).symm
section
variable {R : Type} [CommRing R] [IsDomain R] {I : Ideal R} {D : DegPre R}
  {A : PolAV (Spec (CommRingCat.of (FractionRing R)))} {G : Over (Spec (CommRingCat.of R))} [GrpObj G] [IsCommMonObj G]
  {F : Type} [Field F] [Algebra (FractionRing R) F]
end
section
open GlobalTheory.UnifZero ReciprocityTheory.ChartRestriction.G.Out.Inh
variable {X Y Z : Scheme.{0}} {K : Type} [Fintype K]
variable (R : Type) [CommRing R] [IsDomain R] (I : Ideal R) (F : Type) [Field F] [Algebra (FractionRing R) F] (k : ℕ)
end
section
variable {R : Type} [CommRing R] [IsDomain R] {I : Ideal R} {D : DegPre R}
  {A : PolAV (Spec (CommRingCat.of (FractionRing R)))} {G : Over (Spec (CommRingCat.of R))} [GrpObj G] [IsCommMonObj G]
  {F : Type} [Field F] [Algebra (FractionRing R) F]
end
section
open GlobalTheory.UnifZero GlobalTheory.ToricData ReciprocityTheory.ChartRestriction.G.Out.Inh ReciprocityTheory.ChartRestriction.G.Out.InhTate
variable (R : Type) [CommRing R] [IsDomain R] (I : Ideal R) (F : Type) [Field F] [Algebra (FractionRing R) F] (k : ℕ)
def zeroUq (q : (FractionRing R)ˣ) : PreU I (toricPre R PUnit fun _ => q)
    (zeroPolAV (Spec (CommRingCat.of (FractionRing R)))) (𝟙_ (Over (Spec (CommRingCat.of R)))) where
  semi := (zeroU R I).semi
  gen := (zeroU R I).gen
  gen_hom := (zeroU R I).gen_hom
  P := (zeroU R I).P
  wA := (zeroU R I).wA
  wA_gen := (zeroU R I).wA_gen
  gt e := let g := zeroGt R I e
    { q := g.q, q_hom := g.q_hom, q_flat := g.q_flat, q_surj := g.q_surj, q_affine := g.q_affine, i := g.i
      i_hom := g.i_hom, isKernel := g.isKernel, t := g.t, t_gen := g.t_gen, t_mul := g.t_mul, t_unit := g.t_unit
      t_weight := g.t_weight }
  gt_q := (zeroU R I).gt_q
  gt_t := (zeroU R I).gt_t
  w := (zeroU R I).w
  w_gen := (zeroU R I).w_gen
  w_vals := (zeroU R I).w_vals
  w_compat := (zeroU R I).w_compat
end
section
open GlobalTheory.UnifZero GlobalTheory.ToricData ReciprocityTheory.ChartRestriction.G.Out.Inh ReciprocityTheory.ChartRestriction.G.Out.InhTate
variable (R : Type) [CommRing R] [IsDomain R] (I : Ideal R) (F : Type) [Field F] [Algebra (FractionRing R) F] (k : ℕ)
end
section
open GlobalTheory.UnifZero GlobalTheory.ToricData ReciprocityTheory.ChartRestriction.G.Out.Inh ReciprocityTheory.ChartRestriction.G.Out.InhTate
variable (R : Type) [CommRing R] [IsDomain R] (I : Ideal R) (F : Type) [Field F] [Algebra (FractionRing R) F] (k : ℕ)
end
end GlobalTheory.UU.RelModel
end


