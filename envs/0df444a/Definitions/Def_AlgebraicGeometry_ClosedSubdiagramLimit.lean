-- Prove2me | Definitions.Def_AlgebraicGeometry_ClosedSubdiagramLimit
-- name    : AlgebraicGeometry_ClosedSubdiagramLimit
-- status  : Definition
-- author  : @tomasz
-- created : 2026-11-22T07:13:13.977734+00:00
-- url     : https://prove2.me/theorems/63b128a5-e556-4505-8961-be66761da93e
-- title:
--   Limits of compatible closed subschemes
-- statement:
--   Compatible closed subschemes of a diagram have limit cut out by the sum of the pulled-back ideals.

import Mathlib.AlgebraicGeometry.AffineTransitionLimit

noncomputable section

section

section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry.Scheme.IdealSheafData


namespace PhilipponClosedSubdiagramLimit

universe u

variable {I : Type u} [Category.{u} I] (D : I ⥤ Scheme.{u})
    (K : ∀ i, (D.obj i).IdealSheafData)
    (hK : ∀ {i j : I} (f : i ⟶ j), K j ≤ (K i).map (D.map f))

/-- The closed subschemes attached to compatible ideal sheaves form a diagram. -/
def diagram : I ⥤ Scheme.{u} where
  obj i := (K i).subscheme
  map f := subschemeMap _ _ (D.map f) (hK f)
  map_id i := by simp [← cancel_mono (subschemeι (K i))]
  map_comp f g := by simp [← cancel_mono (subschemeι (K _))]

/-- The inclusions of the closed subschemes commute with the diagram maps. -/
def inclusion : diagram D K hK ⟶ D where
  app i := subschemeι (K i)
  naturality i j f := subschemeMap_subschemeι (K i) (K j) (D.map f) (hK f)

theorem affine_transition [∀ {i j : I} (f : i ⟶ j), IsAffineHom (D.map f)]
    {i j : I} (f : i ⟶ j) : IsAffineHom ((diagram D K hK).map f) := by
  let q := (K j).subschemeι
  let : IsClosedImmersion q := inferInstanceAs (IsClosedImmersion (K j).subschemeι)
  have : IsAffineHom ((diagram D K hK).map f ≫ q) := by
    change IsAffineHom (subschemeMap _ _ (D.map f) (hK f) ≫ (K j).subschemeι)
    rw [subschemeMap_subschemeι]
    infer_instance
  exact IsAffineHom.of_comp ((diagram D K hK).map f) q

variable {c : Cone D}

/-- The limit ideal is the supremum of all the pullbacks of the stage ideals. -/
abbrev limitIdeal (c : Cone D) := ⨆ i, (K i).comap (c.π.app i)

private theorem ideal_le_map (i : I) : K i ≤ (limitIdeal D K c).map (c.π.app i) :=
  le_map_iff_comap_le.mpr (le_iSup (fun j => (K j).comap (c.π.app j)) i)

/-- The closed subscheme cut out by the limit ideal has the induced cone. -/
def cone (c : Cone D) : Cone (diagram D K hK) where
  pt := (limitIdeal D K c).subscheme
  π :=
    { app i := subschemeMap _ _ (c.π.app i) (ideal_le_map D K i)
      naturality i j f := by simp [diagram, ← cancel_mono (subschemeι (K j))] }

/-- Taking a compatible family of closed subschemes commutes with the limit
after summing the pulled-back defining ideals. -/
def isLimit (hc : IsLimit c) : IsLimit (cone D K hK c) where
  lift t := IsClosedImmersion.lift (limitIdeal D K c).subschemeι
    (hc.lift ((Cone.postcompose (inclusion D K hK)).obj t)) (by
      have hLe (i : I) : K i ≤ (t.π.app i ≫ (K i).subschemeι).ker := by
        simpa only [ker_subschemeι] using Scheme.Hom.le_ker_comp (t.π.app i) (K i).subschemeι
      rw [ker_subschemeι, limitIdeal, iSup_le_iff]
      intro i
      rw [← le_map_iff_comap_le, ← Scheme.Hom.ker_comp, hc.fac]
      exact hLe i)
  fac t i := by simp [← cancel_mono (subschemeι (K i)), cone, inclusion]
  uniq t m hm := by
    rw [← cancel_mono (subschemeι (limitIdeal D K c))]
    refine hc.hom_ext fun i => ?_
    simp [inclusion, cone, ← hm]

end PhilipponClosedSubdiagramLimit

end

end


