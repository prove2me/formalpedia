-- Prove2me | Definitions.Def_LPCA_Solutions_LPCA_LocalizationTelescope_Defs
-- name    : LPCA_Solutions_LPCA_LocalizationTelescope_Defs
-- status  : Definition
-- author  : @kaiyue
-- created : 2026-10-21T21:20:39.846106+00:00
-- url     : https://prove2.me/theorems/a01d95eb-91be-461d-a3cd-723828653dff
-- title:
--   Localization Telescope for localized persistent commutative algebra
-- statement:
--   This bundle supplies localization Telescope for localized persistent commutative algebra. The bundle contains the selected declarations used by this attachment checkpoint, with the hypotheses of their Lean statements retained. Its role as a dependency does not assert a stronger comparison, scalar compatibility or persistence theorem than those declarations state.
--
--   The included constructions and necessary compatibility results are:
--
--   - The module telescope whose successive transitions multiply by x.
--   - Stage n maps r to r/x^(n+1), matching the positive coordinate-power diagram.
--   - The map from the telescope colimit is bijective even when x is a zero divisor or nilpotent. Injectivity uses an eventual annihilating power, never cancellation.
-- source:
--   https://arxiv.org/abs/2609.02858v1, formalization dependencies for Sections 2–4. Certified Lean source: Solutions/LPCA_LocalizationTelescope.lean, selected declarations in lines 15–137; source SHA-256 213a2d6e94d7c297046485b91ff28ee1e573e2e72ea0ed181f930a6140a8d1af; source certificate Sapelo2 job 49172236.

import Mathlib.Algebra.Category.ModuleCat.FilteredColimits
import Mathlib.RingTheory.Localization.Away.Basic
import Mathlib.Tactic

set_option autoImplicit false

namespace LPCA

open CategoryTheory CategoryTheory.Limits

universe u

variable {R : Type u} [CommRing R]

/-- The module telescope whose successive transitions multiply by x. -/
noncomputable abbrev localizationTelescope (x : R) : ℕ ⥤ ModuleCat R where
  obj _ := ModuleCat.of R R
  map {n m} _ := ModuleCat.ofHom {
    toFun := fun r => x ^ (m - n) * r
    map_add' := mul_add _
    map_smul' := fun c r => by simp only [smul_eq_mul, RingHom.id_apply]; ring }
  map_id n := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro r
    change x ^ (n - n) * r = r
    simp
  map_comp {n m l} f g := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro r
    change x ^ (l - n) * r = x ^ (l - m) * (x ^ (m - n) * r)
    have hnm : n ≤ m := f.down.down
    have hml : m ≤ l := g.down.down
    have hexp : l - n = (l - m) + (m - n) := by omega
    rw [← mul_assoc, ← pow_add, hexp]

/-- Stage n maps r to r/x^(n+1), matching the positive coordinate-power diagram. -/
noncomputable def localizationTelescopeStage (x : R) (n : ℕ) :
    R →ₗ[R] Localization.Away x where
  toFun r := r • IsLocalization.mk' (M := Submonoid.powers x)
    (Localization.Away x) 1 ⟨x ^ (n + 1), ⟨n + 1, rfl⟩⟩
  map_add' r s := add_smul r s _
  map_smul' c r := mul_smul c r _

theorem localizationTelescopeStage_eq (x : R) (n : ℕ) (r : R) :
    localizationTelescopeStage x n r =
      IsLocalization.mk' (M := Submonoid.powers x)
        (Localization.Away x) r ⟨x ^ (n + 1), ⟨n + 1, rfl⟩⟩ :=
  IsLocalization.smul_mk'_one (S := Localization.Away x) r _

noncomputable def localizationTelescopeCocone (x : R) : Cocone (localizationTelescope x) where
  pt := ModuleCat.of R (Localization.Away x)
  ι := {
    app := fun n => ModuleCat.ofHom (localizationTelescopeStage x n)
    naturality := by
      intro n m f
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro r
      change localizationTelescopeStage x m (x ^ (m - n) * r) =
        localizationTelescopeStage x n r
      rw [localizationTelescopeStage_eq, localizationTelescopeStage_eq]
      apply IsLocalization.mk'_eq_of_eq
      change x ^ (m + 1) * r = x ^ (n + 1) * (x ^ (m - n) * r)
      have hnm : n ≤ m := f.down.down
      have hexp : m + 1 = n + 1 + (m - n) := by omega
      rw [← mul_assoc, ← pow_add, hexp] }

noncomputable def localizationTelescopeDesc (x : R) :
    ModuleCat.FilteredColimits.colimit (localizationTelescope x) ⟶
      ModuleCat.of R (Localization.Away x) :=
  ModuleCat.FilteredColimits.colimitDesc (localizationTelescope x) (localizationTelescopeCocone x)

theorem localizationTelescopeDesc_mk (x : R) (n : ℕ) (r : R) :
    localizationTelescopeDesc x
        (ModuleCat.FilteredColimits.M.mk (localizationTelescope x) ⟨n, r⟩) =
      IsLocalization.mk' (M := Submonoid.powers x)
        (Localization.Away x) r ⟨x ^ (n + 1), ⟨n + 1, rfl⟩⟩ := by
  have h := congrArg
    (fun f : (localizationTelescope x).obj n ⟶ ModuleCat.of R (Localization.Away x) => f r)
    (ModuleCat.FilteredColimits.ι_colimitDesc
      (localizationTelescope x) (localizationTelescopeCocone x) n)
  exact h.trans (localizationTelescopeStage_eq x n r)

/-- The map from the telescope colimit is bijective even when x is a zero divisor
or nilpotent. Injectivity uses an eventual annihilating power, never cancellation. -/
theorem localizationTelescopeDesc_bijective (x : R) :
    Function.Bijective (localizationTelescopeDesc x) := by
  have hzero : ∀ z, localizationTelescopeDesc x z = 0 → z = 0 := by
    intro z hz
    obtain ⟨n, r, rfl⟩ := ModuleCat.FilteredColimits.M.mk_surjective (localizationTelescope x) z
    rw [localizationTelescopeDesc_mk] at hz
    obtain ⟨s, hs⟩ := (IsLocalization.mk'_eq_zero_iff r
      (⟨x ^ (n + 1), ⟨n + 1, rfl⟩⟩ : Submonoid.powers x)).mp hz
    obtain ⟨l, hl⟩ := s.2
    have hkill : x ^ l * r = 0 := by simpa only [hl] using hs
    let f : n ⟶ n + l := homOfLE (Nat.le_add_right n l)
    have hmap : (localizationTelescope x).map f r = 0 := by
      change x ^ (n + l - n) * r = 0
      simpa only [Nat.add_sub_cancel_left] using hkill
    calc
      ModuleCat.FilteredColimits.M.mk (localizationTelescope x) ⟨n, r⟩ =
          ModuleCat.FilteredColimits.M.mk (localizationTelescope x)
            ⟨n + l, (localizationTelescope x).map f r⟩ :=
        (ModuleCat.FilteredColimits.M.mk_map (localizationTelescope x) f r).symm
      _ = ModuleCat.FilteredColimits.M.mk (localizationTelescope x) ⟨n + l, 0⟩ := by rw [hmap]
      _ = 0 := (ModuleCat.FilteredColimits.colimit_zero_eq (localizationTelescope x) (n + l)).symm
  constructor
  · intro z w h
    have hsub : localizationTelescopeDesc x (z - w) = 0 := by
      rw [map_sub, h, sub_self]
    exact sub_eq_zero.mp (hzero (z - w) hsub)
  · intro z
    obtain ⟨r, s, hs⟩ := IsLocalization.exists_mk'_eq (Submonoid.powers x) z
    obtain ⟨n, hn⟩ := s.2
    refine ⟨ModuleCat.FilteredColimits.M.mk (localizationTelescope x) ⟨n, x * r⟩, ?_⟩
    rw [localizationTelescopeDesc_mk, ← hs]
    apply IsLocalization.mk'_eq_of_eq
    change x ^ (n + 1) * r = ↑s * (x * r)
    rw [← hn, pow_succ]
    ring

noncomputable def localizationTelescopeIso (x : R) :
    ModuleCat.FilteredColimits.colimit (localizationTelescope x) ≅
      ModuleCat.of R (Localization.Away x) :=
  (LinearEquiv.ofBijective (localizationTelescopeDesc x).hom
    (localizationTelescopeDesc_bijective x)).toModuleIso

noncomputable def localizationTelescopeIsColimit (x : R) :
    IsColimit (localizationTelescopeCocone x) :=
  IsColimit.ofIsoColimit
    (ModuleCat.FilteredColimits.colimitCoconeIsColimit (localizationTelescope x))
    (Cocone.ext (localizationTelescopeIso x) (by
      intro n
      exact ModuleCat.FilteredColimits.ι_colimitDesc
        (localizationTelescope x) (localizationTelescopeCocone x) n))

end LPCA


