-- Prove2me | Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_HermitianLatticeMaps
-- name    : ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_HermitianLatticeMaps
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T05:38:37.605083+00:00
-- url     : https://prove2.me/theorems/1f622a37-1887-482c-9e1d-92965ba12e69
-- title:
--   Hermitian Lattice Maps
-- statement:
--   Definitions and structural lemmas for Hermitian Lattice Maps, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/FundamentalDomains/HermitianLatticeMaps.lean

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_RealPlaceEmbeddings
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_RealPlaceEmbeddings_qb_apply

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace ReciprocityTheory.ChartRestriction.G.FD
namespace HermitianLatticeMaps
open Matrix NumberField Module
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (X : Data E r)
variable {ι : Type} [Fintype ι] [DecidableEq ι]
noncomputable def ty (f : Basis ι ℤ X.Λ) :
    (ι → ι → E) × (Free.ChooseBasisIndex ℤ (𝓞 E) → ι → ι → ℤ) :=
  (fun i j => herm X.Gm (f i : Fin r → E) (f j : Fin r → E),
    fun k i j => f.repr (RingOfIntegers.basis E k • f i) j)
noncomputable def mulQ (α : E) : (Fin r → E) →ₗ[ℚ] (Fin r → E) :=
  (α • LinearMap.id : (Fin r → E) →ₗ[E] (Fin r → E)).restrictScalars ℚ
theorem mulQ_apply (α : E) (v : Fin r → E) : mulQ α v = α • v := rfl
noncomputable def hL (y : Fin r → E) : (Fin r → E) →ₗ[ℚ] E where
  toFun x := herm X.Gm x y
  map_add' x x' := by simp [herm, add_mul, Finset.sum_add_distrib]
  map_smul' q x := by
    simp only [herm, Pi.smul_apply, Rat.smul_def, RingHom.id_apply, Finset.mul_sum]
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => by ring
noncomputable def hR (x : Fin r → E) : (Fin r → E) →ₗ[ℚ] E where
  toFun y := herm X.Gm x y
  map_add' y y' := by simp [herm, cc, mul_add, Finset.sum_add_distrib]
  map_smul' q y := by
    simp only [herm, cc, Pi.smul_apply, Rat.smul_def, RingHom.id_apply, Finset.mul_sum, map_mul,
      map_ratCast]
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => by ring
theorem coe_expand (f : Basis ι ℤ X.Λ) (v : X.Λ) :
    (v : Fin r → E) = ∑ i, f.repr v i • (f i : Fin r → E) := by
  first
    | (conv_lhs => rw [← f.sum_repr v]
       rw [Submodule.coe_sum]
       rfl)
    | (conv_lhs => rw [← f.sum_repr v]
       rw [Submodule.coe_sum]
       exact Finset.sum_congr rfl fun i _ => Submodule.coe_smul_of_tower _ _)
    | (conv_lhs => rw [← f.sum_repr v]
       push_cast
       rfl)
    | (have e := congrArg (fun w : X.Λ => (w : Fin r → E)) (f.sum_repr v)
       simp only [Submodule.coe_sum, Submodule.coe_smul_of_tower] at e
       exact e.symm)
variable (f f' : Basis ι ℤ X.Λ)
noncomputable def phi : (Fin r → E) →ₗ[ℚ] (Fin r → E) :=
  (RealPlaceEmbeddings.qb X f).constr ℚ fun i => (f' i : Fin r → E)
theorem phi_f (i : ι) : phi X f f' (f i : Fin r → E) = f' i := by
  first
    | (rw [← RealPlaceEmbeddings.qb_apply X f i]; unfold phi; rw [Basis.constr_basis])
    | (rw [← RealPlaceEmbeddings.qb_apply (X := X) f i]; unfold phi; rw [Basis.constr_basis])
    | (have e := (RealPlaceEmbeddings.qb X f).constr_basis ℚ (fun j => (f' j : Fin r → E)) i
       rw [RealPlaceEmbeddings.qb_apply] at e
       exact e)
theorem phi_zsum (n : ι → ℤ) :
    phi X f f' (∑ i, n i • (f i : Fin r → E)) = ∑ i, n i • (f' i : Fin r → E) := by
  rw [map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_zsmul, phi_f]
theorem smul_coe (ω : 𝓞 E) (v : X.Λ) : ((ω • v : X.Λ) : Fin r → E) = (ω : E) • (v : Fin r → E) := by
  first
    | rfl
    | (rw [Submodule.coe_smul]; rfl)
    | (rw [Submodule.coe_smul, Algebra.smul_def]; rfl)
variable {f f'}
theorem phi_omega (h : ty X f = ty X f') (k : Free.ChooseBasisIndex ℤ (𝓞 E)) (i : ι) :
    phi X f f' ((RingOfIntegers.basis E k : E) • (f i : Fin r → E)) =
      (RingOfIntegers.basis E k : E) • (f' i : Fin r → E) := by
  have h2 := congrArg Prod.snd h
  have hk : ∀ j, f.repr (RingOfIntegers.basis E k • f i) j =
      f'.repr (RingOfIntegers.basis E k • f' i) j :=
    fun j => congrFun (congrFun (congrFun h2 k) i) j
  have e1 := coe_expand X f (RingOfIntegers.basis E k • f i)
  have e2 := coe_expand X f' (RingOfIntegers.basis E k • f' i)
  rw [smul_coe] at e1 e2
  rw [e1, phi_zsum, e2]
  simp only [hk]
theorem phi_smul (h : ty X f = ty X f') (α : E) (v : Fin r → E) :
    phi X f f' (α • v) = α • phi X f f' v := by
  have key : ∀ i, phi X f f' (α • (f i : Fin r → E)) = α • (f' i : Fin r → E) := by
    intro i
    have hα := (NumberField.integralBasis E).sum_repr α
    rw [← hα]
    simp only [Finset.sum_smul, map_sum, smul_assoc, map_smul, NumberField.integralBasis_apply]
    refine Finset.sum_congr rfl fun k _ => ?_
    congr 1
    exact phi_omega X h k i
  have e : (phi X f f').comp (mulQ α) = (mulQ α).comp (phi X f f') := by
    refine (RealPlaceEmbeddings.qb X f).ext fun i => ?_
    rw [LinearMap.comp_apply, LinearMap.comp_apply, mulQ_apply, mulQ_apply, RealPlaceEmbeddings.qb_apply, key, phi_f]
  have := LinearMap.congr_fun e v
  rwa [LinearMap.comp_apply, LinearMap.comp_apply, mulQ_apply, mulQ_apply] at this
noncomputable def phiE (h : ty X f = ty X f') : (Fin r → E) →ₗ[E] (Fin r → E) where
  toFun := phi X f f'
  map_add' := map_add _
  map_smul' := phi_smul X h
end HermitianLatticeMaps
end ReciprocityTheory.ChartRestriction.G.FD


