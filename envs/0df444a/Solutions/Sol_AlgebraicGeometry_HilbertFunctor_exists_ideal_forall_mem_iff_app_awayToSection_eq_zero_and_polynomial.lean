-- Prove2me | solution 1 for AlgebraicGeometry.HilbertFunctor.exists_ideal_forall_mem_iff_app_awayToSection_eq_zero_and_polynomial
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:02.935278+00:00
-- url     : https://prove2.me/submissions/0f11dc2e-b268-5f02-89ab-7483e3bc188c

import Mathlib
import Definitions.Def_AlgebraicGeometry_ProjSpace
import Definitions.Def_AlgebraicGeometry_HilbertFunctor
import Definitions.Def_Nat_MacaulayPow
import Theorems.Thm_MvPolynomial_finrank_piece_succ_le_macaulayPow
import Theorems.Thm_Nat_exists_forall_eq_macaulayPow_of_forall_le_macaulayPow
import Theorems.Thm_Nat_exists_polynomial_forall_eval_eq_of_forall_eq_macaulayPow
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_HilbertFunctor_exists_ideal_forall_mem_iff_app_awayToSection_eq_zero_and_polynomial

set_option autoImplicit false
open MvPolynomial CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.HilbertFunctor
attribute [local instance] MvPolynomial.gradedAlgebra

noncomputable section

namespace E2SOL

section Sat

variable {n : ℕ} {k : Type} [Field k]
    {Zk : Scheme.{0}} (ιk : Zk ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) k))

local notation "𝒜" => MvPolynomial.homogeneousSubmodule (Fin (n + 1)) k

def xpow (i : Fin (n + 1)) (d : ℕ) : ↥(homogeneousSubmodule (Fin (n + 1)) k d) :=
  ⟨MvPolynomial.X i ^ d, (MvPolynomial.mem_homogeneousSubmodule d _).mpr (MvPolynomial.isHomogeneous_X_pow i d)⟩

def frac (i : Fin (n + 1)) (d : ℕ) (F : ↥(homogeneousSubmodule (Fin (n + 1)) k d)) :
    HomogeneousLocalization.Away 𝒜 (MvPolynomial.X i) :=
  HomogeneousLocalization.mk
    { deg := d
      num := F
      den := xpow (k := k) i d
      den_mem := ⟨d, rfl⟩ }

theorem frac_zero (i : Fin (n + 1)) (d : ℕ) : frac (k := k) i d 0 = 0 := by
  apply HomogeneousLocalization.val_injective
  simp only [frac, HomogeneousLocalization.val_mk, HomogeneousLocalization.val_zero, Submodule.coe_zero]
  exact Localization.mk_zero _

theorem frac_add (i : Fin (n + 1)) (d : ℕ) (F G : ↥(homogeneousSubmodule (Fin (n + 1)) k d)) :
    frac i d (F + G) = frac i d F + frac i d G := by
  apply HomogeneousLocalization.val_injective
  simp only [frac, HomogeneousLocalization.val_mk, HomogeneousLocalization.val_add, Submodule.coe_add]
  rw [Localization.add_mk_self]

theorem frac_mul (i : Fin (n + 1)) (e d : ℕ) (G : ↥(homogeneousSubmodule (Fin (n + 1)) k e))
    (F : ↥(homogeneousSubmodule (Fin (n + 1)) k d)) :
    frac i (e + d) ⟨(G : MvPolynomial (Fin (n + 1)) k) * (F : MvPolynomial (Fin (n + 1)) k), SetLike.mul_mem_graded G.2 F.2⟩ =
      frac i e G * frac i d F := by
  apply HomogeneousLocalization.val_injective
  simp only [frac, HomogeneousLocalization.val_mk, HomogeneousLocalization.val_mul]
  rw [Localization.mk_mul]
  congr 1
  ext
  simp [xpow, pow_add]

noncomputable def chartHom (i : Fin (n + 1)) :
    HomogeneousLocalization.Away 𝒜 (MvPolynomial.X i) →+*
      ↑(Zk.presheaf.obj (Opposite.op (ιk ⁻¹ᵁ (Proj.basicOpen 𝒜 (MvPolynomial.X i))))) :=
  (Proj.awayToSection 𝒜 (MvPolynomial.X i) ≫ ιk.app (Proj.basicOpen 𝒜 (MvPolynomial.X i))).hom

def Van (d : ℕ) (F : ↥(homogeneousSubmodule (Fin (n + 1)) k d)) : Prop :=
  ∀ i : Fin (n + 1), chartHom ιk i (frac i d F) = 0

theorem Van_zero (d : ℕ) : Van ιk d 0 := by
  intro i; rw [frac_zero, map_zero]

theorem Van_add {d : ℕ} {F G : ↥(homogeneousSubmodule (Fin (n + 1)) k d)}
    (hF : Van ιk d F) (hG : Van ιk d G) : Van ιk d (F + G) := by
  intro i; rw [frac_add, map_add, hF i, hG i, add_zero]

theorem Van_mul_left (e : ℕ) {d : ℕ} (G : ↥(homogeneousSubmodule (Fin (n + 1)) k e))
    {F : ↥(homogeneousSubmodule (Fin (n + 1)) k d)} (hF : Van ιk d F) :
    Van ιk (e + d) ⟨(G : MvPolynomial (Fin (n + 1)) k) * (F : MvPolynomial (Fin (n + 1)) k), SetLike.mul_mem_graded G.2 F.2⟩ := by
  intro i; rw [frac_mul, map_mul, hF i, mul_zero]

def comp (d : ℕ) (p : MvPolynomial (Fin (n + 1)) k) : ↥(homogeneousSubmodule (Fin (n + 1)) k d) :=
  ⟨homogeneousComponent d p, homogeneousComponent_mem d p⟩

omit ιk in
theorem comp_zero (d : ℕ) : comp (k := k) (n := n) d 0 = 0 := Subtype.ext (by simp [comp])

omit ιk in
theorem comp_add (d : ℕ) (p q : MvPolynomial (Fin (n + 1)) k) : comp d (p + q) = comp d p + comp d q :=
  Subtype.ext (by simp [comp])

omit ιk in
theorem coe_decompose (φ : MvPolynomial (Fin (n + 1)) k) (i : ℕ) :
    ((DirectSum.decompose 𝒜 φ) i : MvPolynomial (Fin (n + 1)) k) = homogeneousComponent i φ :=
  MvPolynomial.decomposition.decompose'_apply φ i

omit ιk in
theorem homogeneousComponent_mul_of_mem_left {e : ℕ} {c : MvPolynomial (Fin (n + 1)) k}
    (hc : c ∈ homogeneousSubmodule (Fin (n + 1)) k e) (p : MvPolynomial (Fin (n + 1)) k) (d : ℕ) :
    homogeneousComponent d (c * p) = if e ≤ d then c * homogeneousComponent (d - e) p else 0 := by
  have h := DirectSum.coe_decompose_mul_of_left_mem 𝒜 (b := p) d hc
  simpa only [coe_decompose] using h

omit ιk in
theorem comp_of_mem {e : ℕ} {F : MvPolynomial (Fin (n + 1)) k}
    (hF : F ∈ homogeneousSubmodule (Fin (n + 1)) k e) (d : ℕ) :
    comp d F = if h : d = e then ⟨F, h ▸ hF⟩ else 0 := by
  apply Subtype.ext
  simp only [comp, homogeneousComponent_of_mem hF]
  split_ifs <;> rfl

theorem Van_comp_sum {ι : Type} (s : Finset ι) (f : ι → MvPolynomial (Fin (n + 1)) k) (d : ℕ)
    (h : ∀ a ∈ s, Van ιk d (comp d (f a))) : Van ιk d (comp d (∑ a ∈ s, f a)) := by
  classical
  induction s using Finset.induction_on with
  | empty => rw [Finset.sum_empty, comp_zero]; exact Van_zero ιk d
  | insert a s ha ih =>
      rw [Finset.sum_insert ha, comp_add]
      exact Van_add ιk (h a (Finset.mem_insert_self a s))
        (ih fun b hb => h b (Finset.mem_insert_of_mem hb))

noncomputable def satIdeal : Ideal (MvPolynomial (Fin (n + 1)) k) where
  carrier := {p | ∀ d : ℕ, Van ιk d (comp d p)}
  zero_mem' := by
    intro d; rw [comp_zero]; exact Van_zero ιk d
  add_mem' := by
    intro p q hp hq d
    rw [comp_add]; exact Van_add ιk (hp d) (hq d)
  smul_mem' := by
    intro c p hp d
    rw [smul_eq_mul, ← sum_homogeneousComponent c, Finset.sum_mul]
    apply Van_comp_sum
    intro e _
    rcases Nat.lt_or_ge d e with hde | hed
    · have hc0 : comp d (homogeneousComponent e c * p) = 0 := by
        apply Subtype.ext
        simp only [comp, homogeneousComponent_mul_of_mem_left (homogeneousComponent_mem e c) p d,
          if_neg (not_le.mpr hde), Submodule.coe_zero]
      rw [hc0]; exact Van_zero ιk d
    · obtain ⟨d', rfl⟩ := Nat.exists_eq_add_of_le hed
      have hceq : comp (e + d') (homogeneousComponent e c * p) =
          ⟨(comp e c : MvPolynomial (Fin (n + 1)) k) * (comp d' p : MvPolynomial (Fin (n + 1)) k),
            SetLike.mul_mem_graded (comp e c).2 (comp d' p).2⟩ := by
        apply Subtype.ext
        simp only [comp, homogeneousComponent_mul_of_mem_left (homogeneousComponent_mem e c) p (e + d'),
          if_pos (Nat.le_add_right e d'), Nat.add_sub_cancel_left]
      rw [hceq]
      exact Van_mul_left ιk e (comp e c) (hp d')

theorem mem_satIdeal_iff (p : MvPolynomial (Fin (n + 1)) k) :
    p ∈ satIdeal ιk ↔ ∀ d : ℕ, Van ιk d (comp d p) := Iff.rfl

theorem satIdeal_homogeneous (p : MvPolynomial (Fin (n + 1)) k) (hp : p ∈ satIdeal ιk) (d : ℕ) :
    homogeneousComponent d p ∈ satIdeal ιk := by
  rw [mem_satIdeal_iff] at hp ⊢
  intro e
  rw [comp_of_mem (homogeneousComponent_mem d p)]
  split_ifs with h
  · subst h; exact hp _
  · exact Van_zero ιk e

theorem mem_satIdeal_iff_of_isHomogeneous {d : ℕ} {F : MvPolynomial (Fin (n + 1)) k}
    (hF : F.IsHomogeneous d) :
    F ∈ satIdeal ιk ↔ Van ιk d ⟨F, (MvPolynomial.mem_homogeneousSubmodule d F).mpr hF⟩ := by
  rw [mem_satIdeal_iff]
  constructor
  · intro h
    have := h d
    rwa [comp_of_mem ((MvPolynomial.mem_homogeneousSubmodule d F).mpr hF), dif_pos rfl] at this
  · intro h e
    rw [comp_of_mem ((MvPolynomial.mem_homogeneousSubmodule d F).mpr hF)]
    split_ifs with hed
    · subst hed; exact h
    · exact Van_zero ιk e

end Sat

end E2SOL

open E2SOL in

theorem solution
    (n : ℕ) (k : Type) [Field k]
    (Zk : Scheme.{0}) (ιk : Zk ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) k))
    (hιk : IsClosedImmersion ιk) :
    ∃ (I : Ideal (MvPolynomial (Fin (n + 1)) k)),
      (∀ p ∈ I, ∀ d : ℕ, homogeneousComponent d p ∈ I) ∧
      (∀ (d : ℕ) (F : MvPolynomial (Fin (n + 1)) k) (hF : F.IsHomogeneous d),
        (F ∈ I ↔ ∀ i : Fin (n + 1),
                  (ιk.app (Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) k) (MvPolynomial.X i)))
                    (Proj.awayToSection (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) k) (MvPolynomial.X i)
                      (HomogeneousLocalization.mk
                        { deg := d
                          num := ⟨F, (MvPolynomial.mem_homogeneousSubmodule d F).mpr hF⟩
                          den := ⟨MvPolynomial.X i ^ d, (MvPolynomial.mem_homogeneousSubmodule d _).mpr
                            (MvPolynomial.isHomogeneous_X_pow i d)⟩
                          den_mem := ⟨d, rfl⟩ })) = 0)) ∧
      ∃ (P : Polynomial ℚ) (D₀ : ℕ), ∀ d : ℕ, D₀ ≤ d → (Module.finrank k (piece I d) : ℚ) = P.eval (d : ℚ) := by
  refine ⟨satIdeal ιk, satIdeal_homogeneous ιk, ?_, ?_⟩
  · intro d F hF
    exact mem_satIdeal_iff_of_isHomogeneous ιk hF
  ·
    have hmac : ∀ d, 1 ≤ d →
        (fun d => Module.finrank k (piece (satIdeal ιk) d)) (d + 1) ≤
          Nat.macaulayPow d ((fun d => Module.finrank k (piece (satIdeal ιk) d)) d) :=
      fun d hd => MvPolynomial.finrank_piece_succ_le_macaulayPow n d hd k (satIdeal ιk)
        (satIdeal_homogeneous ιk)
    obtain ⟨D₀, hD₀⟩ := Nat.exists_forall_eq_macaulayPow_of_forall_le_macaulayPow
      (fun d => Module.finrank k (piece (satIdeal ιk) d)) 1 le_rfl hmac
    obtain ⟨P, hP⟩ := Nat.exists_polynomial_forall_eval_eq_of_forall_eq_macaulayPow
      (fun d => Module.finrank k (piece (satIdeal ιk) d)) (max D₀ 1) (le_max_right _ _)
      (fun e he => hD₀ e (le_trans (le_max_left _ _) he))
    exact ⟨P, max D₀ 1, fun d hd => hP d hd⟩

end

end S_AlgebraicGeometry_HilbertFunctor_exists_ideal_forall_mem_iff_app_awayToSection_eq_zero_and_polynomial
end P2MW
export P2MW.S_AlgebraicGeometry_HilbertFunctor_exists_ideal_forall_mem_iff_app_awayToSection_eq_zero_and_polynomial (solution)
