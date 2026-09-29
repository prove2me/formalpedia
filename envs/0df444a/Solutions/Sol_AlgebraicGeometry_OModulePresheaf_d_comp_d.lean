-- Prove2me | solution 1 for AlgebraicGeometry.OModulePresheaf.d_comp_d
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:02.935278+00:00
-- url     : https://prove2.me/submissions/b0016bd6-ce07-57d4-85ce-393673fbf222

import Mathlib.AlgebraicGeometry.AffineScheme
import Definitions.Def_AlgebraicGeometry_OrderedAffineCoverCech
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_OModulePresheaf_d_comp_d

set_option linter.unusedSectionVars false
set_option autoImplicit false

p2m_open "AlgebraicGeometry P2MW.S_AlgebraicGeometry_OModulePresheaf_d_comp_d.AlgebraicGeometry CategoryTheory"

namespace AlgebraicGeometry
p2m_export "AlgebraicGeometry" "Spec Scheme AffineScheme OModulePresheaf"
namespace OModulePresheaf
p2m_export "AlgebraicGeometry.OModulePresheaf" "cochain d d_apply res module res_comp"
namespace DCompD
p2m_open "AlgebraicGeometry.OModulePresheaf AlgebraicGeometry"

universe u

variable {R : Type u} [CommRing R] {V : Scheme.{u}} {π : V ⟶ Spec (.of R)}
variable (F : OModulePresheaf π) (K : V.OrderedAffineCover)

theorem succAbove_comp_succAbove {n : ℕ} {i j : Fin (n + 2)} (H : i ≤ j) :
    Fin.succAbove j.succ ∘ Fin.succAbove i = Fin.succAbove i.castSucc ∘ Fin.succAbove j := by
  ext k
  simp only [Function.comp_apply, Fin.succAbove]
  rcases i with ⟨i, hi⟩; rcases j with ⟨j, hj⟩; rcases k with ⟨k, hk⟩
  simp only [Fin.le_def] at H
  simp only [Fin.lt_def, Fin.castSucc_mk, Fin.succ_mk, Fin.val_castSucc]
  split_ifs <;> simp_all only [Fin.val_succ, Fin.val_castSucc] <;> omega

theorem res_at_eq {i : ℕ} {t t' : K.Idx i} (heq : t = t') (f : F.cochain K i) {U : V.Opens}
    (h : U ≤ K.inter t) (h' : U ≤ K.inter t') : F.res h (f t) = F.res h' (f t') := by
  subst heq; rfl

theorem d_comp_d (i : ℕ) : F.d K (i + 1) ∘ₗ F.d K i = 0 := by
  refine LinearMap.ext fun f => funext fun s => ?_
  rw [LinearMap.comp_apply, F.d_apply, LinearMap.zero_apply, Pi.zero_apply]
  simp only [F.d_apply, map_sum, map_zsmul, Finset.smul_sum, smul_smul, ← pow_add]
  have hres : ∀ (a : Fin (i + 3)) (b : Fin (i + 2)),
      F.res (K.inter_le_inter_face s a)
          (F.res (K.inter_le_inter_face (K.face s a) b) (f (K.face (K.face s a) b)))
        = F.res ((K.inter_le_inter_face s a).trans (K.inter_le_inter_face (K.face s a) b))
            (f (K.face (K.face s a) b)) :=
    fun a b => (congrFun (congrArg DFunLike.coe (F.res_comp _ _)) _).symm
  simp only [hres]
  rw [← Finset.sum_product', Finset.univ_product_univ]
  set S : Finset (Fin (i + 3) × Fin (i + 2)) := {ab | (ab.1 : ℕ) ≤ (ab.2 : ℕ)}
  rw [← Finset.sum_add_sum_compl S, ← eq_neg_iff_add_eq_zero, ← Finset.sum_neg_distrib]
  refine Finset.sum_bij
    (fun ab (hab : ab ∈ S) =>
      (ab.2.succ, Fin.castLT ab.1 (Nat.lt_of_le_of_lt (Finset.mem_filter.mp hab).2 ab.2.isLt)))
    ?hmem ?hinj ?hsurj ?hterm
  case hmem =>
    rintro ⟨a, b⟩ hab
    simp only [S, Finset.compl_filter, Finset.mem_filter, Finset.mem_univ, true_and,
      Fin.val_succ, not_le, Fin.val_castLT]
    exact Nat.lt_succ_of_le (Finset.mem_filter.mp hab).2
  case hinj =>
    rintro ⟨a, b⟩ hab ⟨a', b'⟩ hab' heq
    have h2 := congrArg Prod.snd heq
    exact Prod.ext (Fin.eq_of_val_eq (by simpa using congrArg Fin.val h2))
      (Fin.succ_injective _ (congrArg Prod.fst heq))
  case hsurj =>
    rintro ⟨a', b'⟩ hab'
    have hlt : (b' : ℕ) < (a' : ℕ) := by
      simpa [S, Finset.compl_filter, Finset.mem_filter, not_le] using hab'
    have ha'0 : a' ≠ 0 := fun h => by simp [h] at hlt
    refine ⟨(Fin.castSucc b', a'.pred ha'0), ?_, ?_⟩
    · simp only [S, Finset.mem_filter, Finset.mem_univ, true_and, Fin.val_castSucc,
        Fin.val_pred]; omega
    · exact Prod.ext (Fin.succ_pred a' ha'0)
        (Fin.eq_of_val_eq (by simp only [Fin.val_castLT, Fin.val_castSucc]))
  case hterm =>
    rintro ⟨a, b⟩ hab
    have hba : (a : ℕ) ≤ (b : ℕ) := (Finset.mem_filter.mp hab).2
    set a' : Fin (i + 2) := Fin.castLT a (Nat.lt_of_le_of_lt hba b.isLt)
    have halt : a' ≤ b := Fin.le_def.mpr (by simpa [a'] using hba)
    have hacs : a'.castSucc = a := Fin.eq_of_val_eq (by simp [a'])
    have hface : K.face (K.face s a) b = K.face (K.face s b.succ) a' := by
      apply Subtype.ext
      change s.1 ∘ (Fin.succAbove a ∘ Fin.succAbove b) = s.1 ∘ (Fin.succAbove b.succ ∘ Fin.succAbove a')
      rw [← hacs, succAbove_comp_succAbove halt]
    have hsign : ((-1 : ℤ) ^ ((a : ℕ) + (b : ℕ)))
        = -((-1 : ℤ) ^ (((b.succ : Fin (i + 3)) : ℕ) + (a' : ℕ))) := by
      simp only [Fin.val_succ, a', Fin.val_castLT]
      rw [show ((b : ℕ) + 1 + (a : ℕ)) = ((a : ℕ) + (b : ℕ)) + 1 from by ring, pow_succ]; ring
    rw [hsign, neg_smul]
    refine congrArg Neg.neg (congrArg₂ (· • ·) (by congr 1) ?_)
    exact res_at_eq F K hface f _ _

end AlgebraicGeometry.OModulePresheaf.DCompD

universe u
open _root_.AlgebraicGeometry _root_.P2MW.S_AlgebraicGeometry_OModulePresheaf_d_comp_d.AlgebraicGeometry in
theorem solution {R : Type u} [CommRing R] {V : Scheme.{u}} {π : V ⟶ Spec (.of R)}
    (F : OModulePresheaf π) (K : V.OrderedAffineCover) (i : ℕ) :
    F.d K (i + 1) ∘ₗ F.d K i = 0 :=
  OModulePresheaf.DCompD.d_comp_d F K i

end S_AlgebraicGeometry_OModulePresheaf_d_comp_d
end P2MW
export P2MW.S_AlgebraicGeometry_OModulePresheaf_d_comp_d (solution)
