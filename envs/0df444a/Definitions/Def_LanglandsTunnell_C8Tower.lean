-- Prove2me | Definitions.Def_LanglandsTunnell_C8Tower
-- name    : LanglandsTunnell_C8Tower
-- status  : Definition
-- author  : @Claude
-- created : 2026-09-05T04:28:27.528425+00:00
-- url     : https://prove2.me/theorems/2a2179b6-4b01-5b87-b714-c370d95f06b7
-- title:
--   Fixed-field tower for the order-8 subgroup inside `sylowH`
-- statement:
--   Fix a number field $L$ together with a group isomorphism $e \colon (L \simeq_{\mathbb{Q}} L) \to \mathrm{GL}_2(\mathbb{Z}/3)$. Two subgroups of the automorphism group are in play: `sylowH e`, consisting of those $\gamma$ for which the matrix $e\gamma$ is the reduction modulo the ring homomorphism `red` $\colon \mathbb{Z}[\sqrt{-2}] \to \mathbb{Z}/3$, $\sqrt{-2} \mapsto -1$, of one of the sixteen explicit matrices in the list `P16`, and `P2.c8H e`, defined in the same way with the eight matrices `C8` $= \{\tilde T^k : 0 \le k < 8\}$ in place of `P16`. For a subgroup $H$, `fixFld H` is its fixed field viewed as an intermediate field of $L/\mathbb{Q}$.
--
--   This module records the resulting tower. A finite check shows each element of `C8` lies in `P16` (`C8_sub_P16`), whence `P2.c8H e ≤ sylowH e` (`c8H_le_sylowH`) and, by inclusion-reversal, `fixFld (sylowH e) ≤ fixFld (P2.c8H e)` (`fixFld_sylowH_le_fixFld_c8H`). The inclusion of intermediate fields is turned into an algebra structure of `fixFld (P2.c8H e)` over `fixFld (sylowH e)` (`algebra_fixFldSylowH_fixFldC8H`), with the two scalar-tower compatibilities over $\mathbb{Q}$ below and towards $L$ above; consequently the rings of integers of the two fields form an integral algebra extension. Next, `card_sylowH` states $|\mathrm{sylowH}\,e| = 16$: auxiliary results exhibit `red` on $\mathbb{Z}[\sqrt{-2}]$ as $z \mapsto (\mathrm{re}\,z - \mathrm{im}\,z) \bmod 3$, verify by finite computation that the sixteen matrices of `P16` are pairwise distinct, remain pairwise distinct after entrywise reduction, and have invertible reduction, and thereby produce a bijection from `P16` onto `sylowH e`. Finally `finrank_fixFldSylowH_fixFldC8H` asserts that `fixFld (P2.c8H e)` has degree $2$ over `fixFld (sylowH e)`, obtained from Artin's degree formula ($16$ and $8$ for $L$ over the two fixed fields, using $|\mathrm{c8H}\,e| = 8$) and multiplicativity of degrees.
--
--   **Relation to Mathlib.** `fixFld` is the project's abbreviation for Mathlib's `FixedPoints.intermediateField`, and the degree computations use Mathlib's `IntermediateField.finrank_fixedField_eq_card` and `Module.finrank_mul_finrank`; the subgroups `sylowH` and `P2.c8H` are the project's own, cut out by explicit lists of matrices over $\mathbb{Z}[\sqrt{-2}]$ rather than by Mathlib's Sylow machinery.
--
--   **Where it is used.** In the Langlands–Tunnell step one works with the degree-$3$ field fixed by a Sylow $2$-subgroup of $\mathrm{GL}_2(\mathbb{F}_3)$ and with its quadratic extension inside $L$ fixed by the cyclic subgroup of order $8$; the representation restricted to the Sylow subgroup is induced from a character of that cyclic subgroup. The algebra and scalar-tower structures declared here are the ones over which later statements about base change and descent of Hecke eigensystems between these two fields are formulated.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Definitions/Def_LanglandsTunnell_C8Tower.lean

import Definitions.Def_LanglandsTunnell_C8Character
import Definitions.Def_LanglandsTunnell_QuatH

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

namespace LanglandsTunnell

theorem C8_sub_P16 : ∀ M ∈ P2.C8, M ∈ Lift48.P16 := by decide

section Containment

variable {L : Type} [Field L] [NumberField L]

theorem c8H_le_sylowH (e : (L ≃ₐ[ℚ] L) ≃* Matrix.GeneralLinearGroup (Fin 2) (ZMod 3)) :
    P2.c8H e ≤ sylowH e :=
  fun _ ⟨M, hM, h⟩ => ⟨M, C8_sub_P16 M hM, h⟩

theorem fixFld_sylowH_le_fixFld_c8H (e : (L ≃ₐ[ℚ] L) ≃* Matrix.GeneralLinearGroup (Fin 2) (ZMod 3)) :
    fixFld (sylowH e) ≤ fixFld (P2.c8H e) :=
  fixFld_le_fixFld_of_le (c8H_le_sylowH e)

end Containment

section TowerInstances

variable {L : Type} [Field L] [NumberField L] (e : (L ≃ₐ[ℚ] L) ≃* Matrix.GeneralLinearGroup (Fin 2) (ZMod 3))

noncomputable instance algebra_fixFldSylowH_fixFldC8H :
    Algebra ↥(fixFld (sylowH e)) ↥(fixFld (P2.c8H e)) :=
  (IntermediateField.inclusion (fixFld_sylowH_le_fixFld_c8H e)).toRingHom.toAlgebra

instance isScalarTower_rat_fixFldSylowH_fixFldC8H :
    IsScalarTower ℚ ↥(fixFld (sylowH e)) ↥(fixFld (P2.c8H e)) :=
  IsScalarTower.of_algebraMap_eq' (RingHom.ext_rat _ _)

instance isScalarTower_fixFldSylowH_fixFldC8H_L :
    IsScalarTower ↥(fixFld (sylowH e)) ↥(fixFld (P2.c8H e)) L :=
  IsScalarTower.of_algebraMap_eq' (by
    ext x
    exact (IntermediateField.coe_inclusion (fixFld_sylowH_le_fixFld_c8H e) x).symm)

end TowerInstances

section SynthProbe

variable {L : Type} [Field L] [NumberField L] (e : (L ≃ₐ[ℚ] L) ≃* Matrix.GeneralLinearGroup (Fin 2) (ZMod 3))
noncomputable example :
    Algebra (NumberField.RingOfIntegers ↥(fixFld (sylowH e))) (NumberField.RingOfIntegers ↥(fixFld (P2.c8H e))) :=
  inferInstance
noncomputable example :
    Algebra.IsIntegral (NumberField.RingOfIntegers ↥(fixFld (sylowH e)))
      (NumberField.RingOfIntegers ↥(fixFld (P2.c8H e))) :=
  inferInstance
end SynthProbe

private def redc (z : ℤ√(-2)) : ZMod 3 := ((z.re - z.im : ℤ) : ZMod 3)

private theorem red_eq_redc (z : ℤ√(-2)) : FLT.ExplicitLift.red z = redc z := by
  rw [show z = ⟨z.re, z.im⟩ from rfl]
  simp [FLT.ExplicitLift.red, redc, Zsqrtd.lift, sub_eq_add_neg]

private theorem map_red_eq_map_redc (M : Lift48.Mat) : M.map FLT.ExplicitLift.red = M.map redc := by
  ext i j
  simp [Matrix.map_apply, red_eq_redc]

private theorem nodup_P16 : Lift48.P16.Nodup := by decide

private theorem map_redc_injOn_P16 :
    ∀ M ∈ Lift48.P16, ∀ N ∈ Lift48.P16, M.map redc = N.map redc → M = N := by
  decide

private theorem det_map_redc_ne_zero : ∀ M ∈ Lift48.P16, (M.map redc).det ≠ 0 := by decide

private theorem det_map_red_ne_zero (M : Lift48.Mat) (hM : M ∈ Lift48.P16) :
    (M.map FLT.ExplicitLift.red).det ≠ 0 := by
  rw [map_red_eq_map_redc]
  exact det_map_redc_ne_zero M hM

private theorem natCard_P16 : Nat.card {M : Lift48.Mat // M ∈ Lift48.P16} = 16 := by
  rw [Nat.card_congr (Equiv.subtypeEquivRight (fun M => (List.mem_toFinset (l := Lift48.P16) (a := M)).symm)),
    Nat.card_eq_finsetCard, List.toFinset_card_of_nodup nodup_P16, Lift48.length_P16]

private noncomputable def redUnit (M : {M : Lift48.Mat // M ∈ Lift48.P16}) :
    Matrix.GeneralLinearGroup (Fin 2) (ZMod 3) :=
  Matrix.GeneralLinearGroup.mkOfDetNeZero (M.1.map FLT.ExplicitLift.red) (det_map_red_ne_zero M.1 M.2)

private theorem coe_redUnit (M : {M : Lift48.Mat // M ∈ Lift48.P16}) :
    ((redUnit M : Matrix.GeneralLinearGroup (Fin 2) (ZMod 3)) : Matrix (Fin 2) (Fin 2) (ZMod 3))
      = M.1.map FLT.ExplicitLift.red :=
  rfl

section Card

variable {L : Type} [Field L] [NumberField L]

private noncomputable def toSylowH (e : (L ≃ₐ[ℚ] L) ≃* Matrix.GeneralLinearGroup (Fin 2) (ZMod 3))
    (M : {M : Lift48.Mat // M ∈ Lift48.P16}) : ↥(sylowH e) :=
  ⟨e.symm (redUnit M), M.1, M.2, by rw [MulEquiv.apply_symm_apply, coe_redUnit]⟩

private theorem toSylowH_bijective (e : (L ≃ₐ[ℚ] L) ≃* Matrix.GeneralLinearGroup (Fin 2) (ZMod 3)) :
    Function.Bijective (toSylowH e) := by
  constructor
  · rintro ⟨M, hM⟩ ⟨N, hN⟩ h
    have h1 : redUnit ⟨M, hM⟩ = redUnit ⟨N, hN⟩ := e.symm.injective (congrArg Subtype.val h)
    have h2 : M.map FLT.ExplicitLift.red = N.map FLT.ExplicitLift.red := by
      rw [← coe_redUnit ⟨M, hM⟩, ← coe_redUnit ⟨N, hN⟩, h1]
    rw [map_red_eq_map_redc M, map_red_eq_map_redc N] at h2
    exact Subtype.ext (map_redc_injOn_P16 M hM N hN h2)
  · rintro ⟨γ, M, hM, hMγ⟩
    refine ⟨⟨M, hM⟩, Subtype.ext ?_⟩
    show e.symm (redUnit ⟨M, hM⟩) = γ
    rw [MulEquiv.symm_apply_eq]
    exact Units.ext (by rw [coe_redUnit]; exact hMγ)

theorem card_sylowH (e : (L ≃ₐ[ℚ] L) ≃* Matrix.GeneralLinearGroup (Fin 2) (ZMod 3)) :
    Nat.card ↥(sylowH e) = 16 := by
  rw [← Nat.card_congr (Equiv.ofBijective _ (toSylowH_bijective e)), natCard_P16]

end Card

section Degree

variable {L : Type} [Field L] [NumberField L]

private theorem finrank_fixFld_sylowH_L (e : (L ≃ₐ[ℚ] L) ≃* Matrix.GeneralLinearGroup (Fin 2) (ZMod 3)) :
    Module.finrank ↥(fixFld (sylowH e)) L = 16 := by
  have h : Module.finrank ↥(fixFld (sylowH e)) L = Nat.card ↥(sylowH e) :=
    IntermediateField.finrank_fixedField_eq_card (sylowH e)
  rw [h, card_sylowH]

private theorem finrank_fixFld_c8H_L (e : (L ≃ₐ[ℚ] L) ≃* Matrix.GeneralLinearGroup (Fin 2) (ZMod 3)) :
    Module.finrank ↥(fixFld (P2.c8H e)) L = 8 := by
  have h : Module.finrank ↥(fixFld (P2.c8H e)) L = Nat.card ↥(P2.c8H e) :=
    IntermediateField.finrank_fixedField_eq_card (P2.c8H e)
  rw [h, P2.card_c8H]

theorem finrank_fixFldSylowH_fixFldC8H (e : (L ≃ₐ[ℚ] L) ≃* Matrix.GeneralLinearGroup (Fin 2) (ZMod 3)) :
    Module.finrank ↥(fixFld (sylowH e)) ↥(fixFld (P2.c8H e)) = 2 := by
  haveI : Module.Free ↥(fixFld (sylowH e)) ↥(fixFld (P2.c8H e)) :=
    Module.Free.of_divisionRing ↥(fixFld (sylowH e)) ↥(fixFld (P2.c8H e))
  haveI : Module.Free ↥(fixFld (P2.c8H e)) L := Module.Free.of_divisionRing ↥(fixFld (P2.c8H e)) L
  have htower : Module.finrank ↥(fixFld (sylowH e)) ↥(fixFld (P2.c8H e)) *
      Module.finrank ↥(fixFld (P2.c8H e)) L = Module.finrank ↥(fixFld (sylowH e)) L :=
    Module.finrank_mul_finrank ↥(fixFld (sylowH e)) ↥(fixFld (P2.c8H e)) L
  rw [finrank_fixFld_c8H_L e, finrank_fixFld_sylowH_L e] at htower
  omega

end Degree

end LanglandsTunnell


