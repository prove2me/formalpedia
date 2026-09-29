-- Prove2me | solution 1 for AlgebraicGeometry.tendsto_appLE_mapPt_complex
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.553648+00:00
-- url     : https://prove2.me/submissions/51fc9e83-3c3e-5a94-9d8b-edb6de697253

import Mathlib
import Definitions.Def_CerednikDrinfeld_QMModuli
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_tendsto_appLE_mapPt_complex

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian CerednikDrinfeld.QM Filter Topology

theorem solution
    {X Y : Scheme.{0}} {f : X ⟶ Spec (CommRingCat.of ℂ)} {g : Y ⟶ Spec (CommRingCat.of ℂ)}
    (φ : X ⟶ Y) (hφ : φ ≫ g = f)
    (P : ℕ → SchemeHomOver (𝟙 (Spec (CommRingCat.of ℂ))) f) (Q : SchemeHomOver (𝟙 (Spec (CommRingCat.of ℂ))) f)
    (hP : ∀ (U : X.Opens), IsAffineOpen U → ∀ (hx : ⊤ ≤ Q.1 ⁻¹ᵁ U),
        ∃ n₀ : ℕ, ∃ hP : ∀ n, n₀ ≤ n → ⊤ ≤ (P n).1 ⁻¹ᵁ U,
          ∀ s : Γ(X, U),
            Tendsto (fun n : ℕ => if h : n₀ ≤ n then
                (Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom (((P n).1.appLE U ⊤ (hP n h)) s) else 0)
              atTop (𝓝 ((Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom ((Q.1.appLE U ⊤ hx) s)))) :
    ∀ (U : Y.Opens), IsAffineOpen U → ∀ (hx : ⊤ ≤ (mapPt φ hφ Q).1 ⁻¹ᵁ U),
        ∃ n₀ : ℕ, ∃ hP : ∀ n, n₀ ≤ n → ⊤ ≤ (mapPt φ hφ (P n)).1 ⁻¹ᵁ U,
          ∀ s : Γ(Y, U),
            Tendsto (fun n : ℕ => if h : n₀ ≤ n then
                (Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom (((mapPt φ hφ (P n)).1.appLE U ⊤ (hP n h)) s) else 0)
              atTop (𝓝 ((Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom (((mapPt φ hφ Q).1.appLE U ⊤ hx) s))) := by
  intro V hV hQV
  let p₀ : ↥(Spec (CommRingCat.of ℂ)) := default
  have hmem : Q.1.base p₀ ∈ (φ ⁻¹ᵁ V : X.Opens) := by
    have := hQV (show p₀ ∈ (⊤ : (Spec (CommRingCat.of ℂ)).Opens) from trivial)
    exact this
  obtain ⟨_, ⟨U, hU, rfl⟩, hxU, hUV⟩ := X.isBasis_affineOpens.exists_subset_of_mem_open hmem (φ ⁻¹ᵁ V).2
  have hUV' : (U : X.Opens) ≤ φ ⁻¹ᵁ V := hUV
  have hQU : ⊤ ≤ Q.1 ⁻¹ᵁ (U : X.Opens) := by
    intro p _
    rw [Subsingleton.elim p p₀]
    exact hxU
  obtain ⟨n₀, hPU, hconv⟩ := hP U hU hQU
  have hPV : ∀ n, n₀ ≤ n → ⊤ ≤ (mapPt φ hφ (P n)).1 ⁻¹ᵁ V := by
    intro n hn p hp
    show ((P n).1 ≫ φ).base p ∈ V
    exact hUV' (hPU n hn hp)
  refine ⟨n₀, hPV, fun t => ?_⟩
  have key : ∀ (n : ℕ) (h : n₀ ≤ n), ((mapPt φ hφ (P n)).1.appLE V ⊤ (hPV n h)) t =
      ((P n).1.appLE (U : X.Opens) ⊤ (hPU n h)) (φ.appLE V U hUV' t) := by
    intro n h
    show _ = (φ.appLE V U hUV' ≫ (P n).1.appLE (U : X.Opens) ⊤ (hPU n h)) t
    rw [Scheme.Hom.appLE_comp_appLE]
    rfl
  have keyQ : ((mapPt φ hφ Q).1.appLE V ⊤ hQV) t = (Q.1.appLE (U : X.Opens) ⊤ hQU) (φ.appLE V U hUV' t) := by
    show _ = (φ.appLE V U hUV' ≫ Q.1.appLE (U : X.Opens) ⊤ hQU) t
    rw [Scheme.Hom.appLE_comp_appLE]
    rfl
  have hfun : (fun n : ℕ => if h : n₀ ≤ n then
      (Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom (((mapPt φ hφ (P n)).1.appLE V ⊤ (hPV n h)) t) else 0) =
      (fun n : ℕ => if h : n₀ ≤ n then
      (Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom (((P n).1.appLE (U : X.Opens) ⊤ (hPU n h)) (φ.appLE V U hUV' t)) else 0) := by
    funext n
    by_cases h : n₀ ≤ n
    · rw [dif_pos h, dif_pos h, key n h]
    · rw [dif_neg h, dif_neg h]
  rw [hfun, keyQ]
  exact hconv _

end S_AlgebraicGeometry_tendsto_appLE_mapPt_complex
end P2MW
export P2MW.S_AlgebraicGeometry_tendsto_appLE_mapPt_complex (solution)
