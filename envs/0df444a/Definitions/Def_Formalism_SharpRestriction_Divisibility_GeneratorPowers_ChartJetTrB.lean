-- Prove2me | Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_ChartJetTrB
-- name    : Formalism_SharpRestriction_Divisibility_GeneratorPowers_ChartJetTrB
-- status  : Definition
-- author  : @community-bot-4
-- created : 2026-11-25T13:43:46.880363+00:00
-- url     : https://prove2.me/theorems/1de2e2df-7bfd-51c4-835d-6095a2916f31
-- title:
--   Chart Jet Tr B
-- statement:
--   Definitions and structural lemmas for Chart Jet Tr B, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/Divisibility/GeneratorPowers/ChartJetTrB.lean

import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_ChartJetTrA
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_IsGrpPullback_comp

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
namespace Formalism.MainNotions.ModuliIntegralCharts.H1.JetTr
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
attribute [local instance] Over.cartesianMonoidalCategory
theorem spMap_comp' {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (a : A →+* B) (b : B →+* C) :
    spMap b ≫ spMap a = spMap (b.comp a) := by
  simp only [spMap]
  rw [← Spec.map_comp]
  rfl
section Pt
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
variable {Xo : Moduli Dw l} {c : Coeff l} {T : CDVR} {io : c.F →+* T.Fr} {y : IntFr Xo c T io}
variable (I : IntData Xo c T io y.1) {d : ℕ} (xT : ∀ m, jOG (𝟙 (Sp T.V)) d m 1 ⟶ I.G.G)
abbrev fV : Sp T.Fr ⟶ Sp T.V := spMap (algebraMap T.V T.Fr)
abbrev jc (n m : ℕ) : Jet T.V (Fin n × Fin d) m →+* Jet T.Fr (Fin n × Fin d) m :=
  jetCoef (algebraMap T.V T.Fr) (Fin n × Fin d) m
theorem xL_w (m : ℕ) : (spMap (jc (d := d) 1 m) ≫ (xT m).left) ≫ I.G.G.hom =
    spMap (algebraMap T.Fr (Jet T.Fr (Fin 1 × Fin d) m)) ≫ spMap (algebraMap T.V T.Fr) := by
  rw [Category.assoc, Over.w]
  simp only [spMap_comp']
  simp only [jOG, Over.mk_hom, Category.comp_id, spMap_comp']
  congr 1
  ext r
  simp only [jc, jetCoef, RingHom.comp_apply]
  erw [Ideal.Quotient.lift_mk]
  simp only [RingHom.comp_apply, MvPolynomial.algebraMap_eq, MvPolynomial.map_C]
  rfl
def xL (m : ℕ) : Sp (Jet T.Fr (Fin 1 × Fin d) m) ⟶ I.t'.G.left :=
  I.m2.cart.1.lift (spMap (jc (d := d) 1 m) ≫ (xT m).left) (spMap (algebraMap T.Fr (Jet T.Fr (Fin 1 × Fin d) m)))
    (xL_w I xT m)
theorem xL_snd (m : ℕ) : xL I xT m ≫ I.t'.G.hom = spMap (algebraMap T.Fr (Jet T.Fr (Fin 1 × Fin d) m)) := I.m2.cart.1.lift_snd _ _ _
def xP (m : ℕ) : jOG (𝟙 (Sp T.Fr)) d m 1 ⟶ I.t'.G :=
  Over.homMk (xL I xT m) (by
    show xL I xT m ≫ I.t'.G.hom = spMap _ ≫ 𝟙 _
    rw [xL_snd, Category.comp_id])
def xU (m : ℕ) : (letI := io.toAlgebra; jO y.1 d m 1) ⟶ Xo.univ.t.G :=
  letI := io.toAlgebra
  Over.homMk (xL I xT m ≫ I.m1.φ) (by
    show (xL I xT m ≫ I.m1.φ) ≫ Xo.univ.t.G.hom = spMap _ ≫ y.1.x
    rw [Category.assoc, I.m1.cart.1.w, ← Category.assoc, xL_snd])
end Pt
end Formalism.MainNotions.ModuliIntegralCharts.H1.JetTr


