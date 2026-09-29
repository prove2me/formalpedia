-- Prove2me | solution 1 for AlgebraicGeometry.RelEffCartierDiv.comap_mapOnProdOver_I_ofPoint_and_mul_prod_pow
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:03.589526+00:00
-- url     : https://prove2.me/submissions/8719040e-10ff-56f6-b0d0-51a770d85adf

import Mathlib
import Definitions.Def_AlgebraicGeometry_RelEffCartierDiv
import Definitions.Def_AlgebraicGeometry_RelEffCartierDivOfPoint
import Definitions.Def_AlgebraicGeometry_RelEffCartierDivSum
import Theorems.Thm_AlgebraicGeometry_RelEffCartierDiv_pullbackAlong_ofPoint
import Theorems.Thm_AlgebraicGeometry_prodKerGraph_comap_mapOnProdOver
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_RelEffCartierDiv_comap_mapOnProdOver_I_ofPoint_and_mul_prod_pow

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace SecIdealChange

theorem prod_option_sigma {M : Type*} [CommMonoid M] {ι : Type} [Fintype ι] (e : ι → ℕ) (x : M) (y : ι → M) :
    ∏ j : Option (Σ i : ι, Fin (e i)), Option.elim j x (fun s => y s.1) = x * ∏ i, y i ^ (e i) := by
  classical
  rw [Fintype.prod_option]
  congr 1
  simp only [Option.elim]
  rw [Fintype.prod_sigma]
  refine Fintype.prod_congr _ _ fun i => ?_
  simp

theorem prod_ker_eq_prodKerGraph {𝒞 S T : Scheme.{u}} (f : 𝒞 ⟶ S) {g : T ⟶ S} {J : Type} [Fintype J]
    (c : J → (T ⟶ 𝒞)) (hc : ∀ j, c j ≫ f = g) :
    ∏ j, (graphOver f (c j) (hc j)).ker =
      prodKerGraph f (fun k => c ((Fintype.equivFin J).symm k)) (fun k => hc _) := by
  rw [prodKerGraph_eq_prod]
  exact (Equiv.prod_comp (Fintype.equivFin J).symm (fun j => (graphOver f (c j) (hc j)).ker)).symm

end SecIdealChange

open SecIdealChange in
theorem solution
    {𝒞 S T T' : Scheme.{u}} (f : 𝒞 ⟶ S) [IsSeparated f] {g : T ⟶ S} {g' : T' ⟶ S}
    (φ : T ⟶ T') (hφ : φ ≫ g' = g) [IsAffineHom φ]
    (a : T' ⟶ 𝒞) (ha : a ≫ f = g')
    {ι : Type} [Fintype ι] (b : ι → (T' ⟶ 𝒞)) (hb : ∀ i, b i ≫ f = g') (e : ι → ℕ) :
    (RelEffCartierDiv.ofPoint f a ha).I.comap (mapOnProdOver f φ hφ) =
        (RelEffCartierDiv.ofPoint f (φ ≫ a) (by rw [Category.assoc, ha, hφ])).I ∧
      ((RelEffCartierDiv.ofPoint f a ha).I * ∏ i, (RelEffCartierDiv.ofPoint f (b i) (hb i)).I ^ (e i)).comap
          (mapOnProdOver f φ hφ) =
        (RelEffCartierDiv.ofPoint f (φ ≫ a) (by rw [Category.assoc, ha, hφ])).I *
          ∏ i, (RelEffCartierDiv.ofPoint f (φ ≫ b i) (by rw [Category.assoc, hb i, hφ])).I ^ (e i) := by
  classical
  refine ⟨congrArg RelEffCartierDiv.I (RelEffCartierDiv.pullbackAlong_ofPoint f a ha φ hφ), ?_⟩

  let J := Option (Σ i : ι, Fin (e i))
  let c : J → (T' ⟶ 𝒞) := fun j => Option.elim j a (fun s => b s.1)
  have hc : ∀ j, c j ≫ f = g' := fun j => by
    cases j with
    | none => exact ha
    | some s => exact hb s.1
  have hL : (RelEffCartierDiv.ofPoint f a ha).I * ∏ i, (RelEffCartierDiv.ofPoint f (b i) (hb i)).I ^ (e i) =
      ∏ j, (graphOver f (c j) (hc j)).ker := by
    rw [← prod_option_sigma e ((RelEffCartierDiv.ofPoint f a ha).I) (fun i => (RelEffCartierDiv.ofPoint f (b i) (hb i)).I)]
    refine Fintype.prod_congr _ _ fun j => ?_
    cases j with
    | none => rfl
    | some s => rfl
  have hR : (RelEffCartierDiv.ofPoint f (φ ≫ a) (by rw [Category.assoc, ha, hφ])).I *
        ∏ i, (RelEffCartierDiv.ofPoint f (φ ≫ b i) (by rw [Category.assoc, hb i, hφ])).I ^ (e i) =
      ∏ j, (graphOver f (φ ≫ c j) (by rw [Category.assoc, hc j, hφ])).ker := by
    rw [← prod_option_sigma e ((RelEffCartierDiv.ofPoint f (φ ≫ a) (by rw [Category.assoc, ha, hφ])).I)
      (fun i => (RelEffCartierDiv.ofPoint f (φ ≫ b i) (by rw [Category.assoc, hb i, hφ])).I)]
    refine Fintype.prod_congr _ _ fun j => ?_
    cases j with
    | none => rfl
    | some s => rfl
  rw [hL, hR, prod_ker_eq_prodKerGraph f c hc, prodKerGraph_comap_mapOnProdOver,
    prod_ker_eq_prodKerGraph f (fun j => φ ≫ c j) (fun j => by rw [Category.assoc, hc j, hφ])]

end S_AlgebraicGeometry_RelEffCartierDiv_comap_mapOnProdOver_I_ofPoint_and_mul_prod_pow
end P2MW
export P2MW.S_AlgebraicGeometry_RelEffCartierDiv_comap_mapOnProdOver_I_ofPoint_and_mul_prod_pow (solution)
