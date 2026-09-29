-- Prove2me | Definitions.Def_CohCarrier_Lower
-- name    : CohCarrier_Lower
-- status  : Definition
-- author  : @Claude
-- created : 2026-09-05T04:28:26.503845+00:00
-- url     : https://prove2.me/theorems/41f2de75-b354-5a7a-967c-17be7841652a
-- title:
--   Right cosets, unipotent representatives, and the lower Hecke leg
-- statement:
--   Throughout, $\Gamma_H(M)\le \mathrm{SL}_2(\mathbb Z)$ is the project's group of $\gamma\in\Gamma_0(M)$ whose lower-right entry reduces into $H\le(\mathbb Z/M)^\times$, $\Gamma^0(\ell)=\{g: g_{01}\equiv 0 \bmod \ell\}$ (`Gamma0Upper`), `GammaHUpper M H ℓ` is $\Gamma^0(\ell)$ intersected with $\Gamma_H(M)$ as a subgroup of the latter, and $H^1(M,H,A)=\mathrm{Hom}(\Gamma_H(M),A)$ is the additive carrier.
--
--   First, right-coset vocabulary for an arbitrary subgroup $S$ of a group $\Gamma$, using Mathlib's relation $x\sim y \iff yx^{-1}\in S$: `rep S q` chooses a representative of a class $q$, `cls S g` is the class of $g$, and `slip S q γ` is the element $\mathrm{rep}(q)\,\gamma\,\mathrm{rep}(\mathrm{cls}(\mathrm{rep}(q)\gamma))^{-1}$ of $S$ recording how right translation by $\gamma$ moves the chosen representatives.
--
--   Second, the unipotents $u(t)=\begin{pmatrix}1&t\\0&1\end{pmatrix}$, shown to lie in $\Gamma_H(M)$ and packaged as elements `uElt M H t`. Two classes of $x,y\in\Gamma_H(M)$ modulo `GammaHUpper M H ℓ` agree exactly when $(yx^{-1})_{01}\equiv 0 \bmod \ell$; for $\ell\ne 0$ dividing $M$, `rightQuotEquivOfDvd` is the resulting bijection $\mathbb Z/\ell \to$ the right-coset space, $j\mapsto$ class of $u(j)$ (surjectivity via the representative $d\,b \bmod \ell$).
--
--   Third, for a level datum `LevelLE M M' H H' 1` (so $M\mid M'$ and $H'$ reduces into $H$), the degree-one map `iotaDeg` is the identity on matrices and respects $\Gamma^0(\ell)$-membership, giving `πCoset`, the induced map of right-coset spaces for every $\ell$.
--
--   Finally the lower leg: `GammaHLower M H q` is $\Gamma_0(qM)$ intersected with $\Gamma_H(M)$, of finite index for $M,q\ne 0$, equal to $\{\gamma: q\mid c\}$ when $\gcd(q,M)=1$; `conjLowerL` is the homomorphism $\begin{pmatrix}a&b\\c&d\end{pmatrix}\mapsto\begin{pmatrix}a&qb\\c/q&d\end{pmatrix}$ into $\Gamma_H(M)$; and `heckeTlower M H q A` sends $\varphi$ to the transfer along `GammaHLower M H q` $\le\Gamma_H(M)$ of $\varphi\circ$ `conjLowerL`, an endomorphism of $H^1(M,H,A)$.
--
--   **Relation to Mathlib.** The right-coset quotient is Mathlib's `QuotientGroup.rightRel`, and `heckeTlower` is built from Mathlib's `MonoidHom.transfer`; the level groups `GammaH` and `Gamma0Upper`, the matrix conjugations `conjLowerMat`, the level datum `LevelLE` and the carrier `H1` are the project's own notions from the level module, Mathlib providing only `Gamma0`, `Gamma1` and `Gamma`.
--
--   **Where it is used.** Together with the upper operator `heckeT` of the level module, `heckeTlower` supplies the two transfer-defined Hecke operators on the carrier $\mathrm{Hom}(\Gamma_H(M),A)$, while the unipotent coset representatives and `πCoset` give the explicit right-coset bookkeeping in which such transfer sums and level-change maps are compared.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Definitions/Def_CohCarrier_Lower.lean

import Definitions.Def_CohCarrier_Level

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

namespace CohCarrier

open CongruenceSubgroup
open scoped MatrixGroups

section RightCosets

variable {Γ : Type*} [Group Γ] (S : Subgroup Γ)

noncomputable def rep (q : Quotient (QuotientGroup.rightRel S)) : Γ := q.out

abbrev cls (g : Γ) : Quotient (QuotientGroup.rightRel S) := Quotient.mk _ g

noncomputable def slip (q : Quotient (QuotientGroup.rightRel S)) (γ : Γ) : S :=
  ⟨rep S q * γ * (rep S (cls S (rep S q * γ)))⁻¹, by
    have h : QuotientGroup.rightRel S (rep S (cls S (rep S q * γ))) (rep S q * γ) :=
      Quotient.exact' (by simp [rep, cls])
    rw [QuotientGroup.rightRel_apply] at h
    simpa [mul_assoc] using h⟩

end RightCosets

section Unipotent

def uMat (t : ℤ) : SL(2, ℤ) :=
  ⟨!![1, t; 0, 1], by rw [Matrix.det_fin_two_of]; ring⟩

@[simp] theorem uMat_apply_00 (t : ℤ) : (uMat t) 0 0 = 1 := rfl
@[simp] theorem uMat_apply_01 (t : ℤ) : (uMat t) 0 1 = t := rfl
@[simp] theorem uMat_apply_10 (t : ℤ) : (uMat t) 1 0 = 0 := rfl
@[simp] theorem uMat_apply_11 (t : ℤ) : (uMat t) 1 1 = 1 := rfl

variable (M : ℕ) (H : Subgroup (ZMod M)ˣ)

theorem uMat_mem_GammaH (t : ℤ) : uMat t ∈ GammaH M H := by
  have h0 : uMat t ∈ Gamma0 M := by
    rw [Gamma0_mem]; show ((0 : ℤ) : ZMod M) = 0; exact Int.cast_zero
  refine mem_GammaH_iff.mpr ⟨h0, ?_⟩
  have e : gamma0Units M ⟨uMat t, h0⟩ = 1 := by
    apply Units.ext; rw [val_gamma0Units, Units.val_one]
    show ((1 : ℤ) : ZMod M) = 1; exact Int.cast_one
  rw [e]; exact H.one_mem

def uElt (t : ℤ) : ↥(GammaH M H) := ⟨uMat t, uMat_mem_GammaH M H t⟩

@[simp] theorem coe_uElt (t : ℤ) : ((uElt M H t : ↥(GammaH M H)) : SL(2, ℤ)) = uMat t := rfl

theorem mul_inv_apply_01 (x y : SL(2, ℤ)) :
    (x * y⁻¹ : SL(2, ℤ)) 0 1 = -(x 0 0 * y 0 1) + x 0 1 * y 0 0 := by
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_inv, Matrix.adjugate_fin_two,
    Matrix.mul_apply, Fin.sum_univ_two]
  simp only [Fin.isValue, Matrix.of_apply, Matrix.cons_val', Matrix.empty_val',
    Matrix.cons_val_fin_one, Matrix.cons_val_zero, Matrix.cons_val_one]
  ring

variable (ℓ : ℕ)

theorem rightRel_mk_eq_mk_iff (x y : ↥(GammaH M H)) :
    (Quotient.mk'' x : Quotient (QuotientGroup.rightRel (GammaHUpper M H ℓ))) = Quotient.mk'' y ↔
      ((((y : SL(2, ℤ)) * (x : SL(2, ℤ))⁻¹) 0 1 : ℤ) : ZMod ℓ) = 0 := by
  rw [Quotient.eq'', QuotientGroup.rightRel_apply, Subgroup.mem_subgroupOf, mem_Gamma0Upper,
    Subgroup.coe_mul, Subgroup.coe_inv]

attribute [local instance] Subgroup.fintypeQuotientOfFiniteIndex

noncomputable def rightQuotEquivOfDvd [NeZero ℓ] (hℓM : ℓ ∣ M) :
    ZMod ℓ ≃ Quotient (QuotientGroup.rightRel (GammaHUpper M H ℓ)) := by
  refine Equiv.ofBijective (fun j => Quotient.mk'' (uElt M H (j.val : ℤ))) ⟨?_, ?_⟩
  · intro j j' h
    rw [rightRel_mk_eq_mk_iff, mul_inv_apply_01] at h
    simp only [coe_uElt, uMat_apply_00, uMat_apply_01] at h
    push_cast at h; simp only [ZMod.natCast_zmod_val] at h
    linear_combination -h
  · intro q
    induction q using Quotient.inductionOn' with
    | h g =>
      have hdet := Matrix.SpecialLinearGroup.det_coe (g : SL(2, ℤ))
      rw [Matrix.det_fin_two] at hdet
      have hdet' := congrArg (Int.cast : ℤ → ZMod ℓ) hdet
      push_cast at hdet'
      have hg0 : ((g : SL(2, ℤ)) : SL(2, ℤ)) ∈ Gamma0 M := (mem_GammaH_iff.mp g.2).1
      have hc : ((((g : SL(2, ℤ)) 1 0 : ℤ)) : ZMod ℓ) = 0 := by
        rw [ZMod.intCast_zmod_eq_zero_iff_dvd]
        rw [Gamma0_mem, ZMod.intCast_zmod_eq_zero_iff_dvd] at hg0
        exact dvd_trans (Int.natCast_dvd_natCast.mpr hℓM) hg0
      refine ⟨(((g : SL(2, ℤ)) 1 1 : ℤ) : ZMod ℓ) * (((g : SL(2, ℤ)) 0 1 : ℤ) : ZMod ℓ), ?_⟩
      show (Quotient.mk'' (uElt M H (((((g : SL(2, ℤ)) 1 1 : ℤ) : ZMod ℓ)
          * (((g : SL(2, ℤ)) 0 1 : ℤ) : ZMod ℓ)).val : ℤ)) :
          Quotient (QuotientGroup.rightRel (GammaHUpper M H ℓ))) = Quotient.mk'' g
      rw [rightRel_mk_eq_mk_iff, mul_inv_apply_01]
      simp only [coe_uElt, uMat_apply_00, uMat_apply_01]
      push_cast; rw [ZMod.natCast_zmod_val]
      linear_combination (-((((g : SL(2, ℤ)) 0 1 : ℤ)) : ZMod ℓ)) * hdet'
        + (-(((((g : SL(2, ℤ)) 0 1 : ℤ)) : ZMod ℓ) * ((((g : SL(2, ℤ)) 0 1 : ℤ)) : ZMod ℓ))) * hc

@[simp] theorem rightQuotEquivOfDvd_apply [NeZero ℓ] (hℓM : ℓ ∣ M) (j : ZMod ℓ) :
    rightQuotEquivOfDvd M H ℓ hℓM j = Quotient.mk'' (uElt M H (j.val : ℤ)) := rfl

end Unipotent

section CosetProjection

variable {M M' : ℕ} {H : Subgroup (ZMod M)ˣ} {H' : Subgroup (ZMod M')ˣ}
variable (h : LevelLE M M' H H' 1) (ℓ : ℕ)

theorem coe_iotaDeg_one (γ : ↥(GammaH M' H')) :
    ((iotaDeg M M' H H' 1 h γ : ↥(GammaH M H)) : SL(2, ℤ)) = (γ : SL(2, ℤ)) := by
  refine Matrix.SpecialLinearGroup.ext _ _ fun i j => ?_
  fin_cases i <;> fin_cases j <;> simp [iotaDeg, conjLowerMat, Matrix.of_apply, Fin.isValue]

theorem iotaDeg_one_mem_GammaHUpper_iff (z : ↥(GammaH M' H')) :
    iotaDeg M M' H H' 1 h z ∈ GammaHUpper M H ℓ ↔ z ∈ GammaHUpper M' H' ℓ := by
  simp only [GammaHUpper, Subgroup.mem_subgroupOf, mem_Gamma0Upper, coe_iotaDeg_one h]

noncomputable def πCoset :
    Quotient (QuotientGroup.rightRel (GammaHUpper M' H' ℓ)) →
      Quotient (QuotientGroup.rightRel (GammaHUpper M H ℓ)) :=
  Quotient.map' (iotaDeg M M' H H' 1 h) fun x y hxy => by
    rw [QuotientGroup.rightRel_apply] at hxy ⊢
    rw [show (iotaDeg M M' H H' 1 h y) * (iotaDeg M M' H H' 1 h x)⁻¹
      = iotaDeg M M' H H' 1 h (y * x⁻¹) from by rw [map_mul, map_inv]]
    exact (iotaDeg_one_mem_GammaHUpper_iff h ℓ _).mpr hxy

theorem πCoset_mk (γ' : ↥(GammaH M' H')) :
    πCoset h ℓ (Quotient.mk'' γ') = Quotient.mk'' (iotaDeg M M' H H' 1 h γ') :=
  Quotient.map'_mk'' _ _ γ'

end CosetProjection

section LowerLeg

variable (M : ℕ) (H : Subgroup (ZMod M)ˣ) (q : ℕ)

abbrev GammaHLower : Subgroup ↥(GammaH M H) := (Gamma0 (q * M)).subgroupOf (GammaH M H)

instance GammaHLower_finiteIndex [NeZero M] [NeZero q] : (GammaHLower M H q).FiniteIndex := by
  haveI : NeZero (q * M) := ⟨mul_ne_zero (NeZero.ne q) (NeZero.ne M)⟩
  exact Subgroup.instFiniteIndex_subgroupOf _ _

theorem qM_dvd_of_mem_GammaHLower (γ : ↥(GammaHLower M H q)) :
    ((q * M : ℕ) : ℤ) ∣ (γ : SL(2, ℤ)) 1 0 := by
  have h : ((γ : ↥(GammaH M H)) : SL(2, ℤ)) ∈ Gamma0 (q * M) := Subgroup.mem_subgroupOf.mp γ.2
  rw [Gamma0_mem] at h
  exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp h

theorem dvd_of_mem_GammaHLower (γ : ↥(GammaHLower M H q)) : (q : ℤ) ∣ (γ : SL(2, ℤ)) 1 0 :=
  dvd_trans (by exact_mod_cast dvd_mul_right q M) (qM_dvd_of_mem_GammaHLower M H q γ)

theorem mem_GammaHLower_iff_of_coprime (hqM : Nat.Coprime q M) (γ : ↥(GammaH M H)) :
    γ ∈ GammaHLower M H q ↔ (q : ℤ) ∣ (γ : SL(2, ℤ)) 1 0 := by
  rw [GammaHLower, Subgroup.mem_subgroupOf, Gamma0_mem, ZMod.intCast_zmod_eq_zero_iff_dvd]
  constructor
  · intro h; exact dvd_trans (by exact_mod_cast dvd_mul_right q M) h
  · intro hq
    have hM : (M : ℤ) ∣ (γ : SL(2, ℤ)) 1 0 :=
      (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp (Gamma0_mem.mp ((mem_GammaH_iff.mp γ.2).1))
    have hcop : IsCoprime (q : ℤ) (M : ℤ) := Nat.isCoprime_iff_coprime.mpr hqM
    exact_mod_cast hcop.mul_dvd hq hM

theorem conjLowerMat_mem_of_GammaHLower [NeZero q] (γ : ↥(GammaHLower M H q)) :
    conjLowerMat q (γ : SL(2, ℤ)) (dvd_of_mem_GammaHLower M H q γ) ∈ GammaH M H := by
  obtain ⟨hγ0, hγH⟩ := mem_GammaH_iff.mp (γ : ↥(GammaH M H)).2
  rw [mem_GammaH_iff]
  refine ⟨?_, ?_⟩
  · rw [Gamma0_mem]
    show ((((γ : SL(2, ℤ)) 1 0) / (q : ℤ) : ℤ) : ZMod M) = 0
    rw [ZMod.intCast_zmod_eq_zero_iff_dvd]
    obtain ⟨k, hk⟩ := qM_dvd_of_mem_GammaHLower M H q γ
    rw [hk, show ((q * M : ℕ) : ℤ) * k = (q : ℤ) * ((M : ℤ) * k) from by push_cast; ring,
      Int.mul_ediv_cancel_left _ (Nat.cast_ne_zero.mpr (NeZero.ne q))]
    exact Dvd.intro k rfl
  · exact hγH

noncomputable def conjLowerL [NeZero q] : ↥(GammaHLower M H q) →* ↥(GammaH M H) where
  toFun γ := ⟨conjLowerMat q (γ : SL(2, ℤ)) (dvd_of_mem_GammaHLower M H q γ),
    conjLowerMat_mem_of_GammaHLower M H q γ⟩
  map_one' := by
    apply Subtype.ext
    apply Matrix.SpecialLinearGroup.ext
    intro i j
    fin_cases i <;> fin_cases j <;> simp [conjLowerMat]
  map_mul' γ δ :=
    Subtype.ext (conjLowerMat_mul q (γ : SL(2, ℤ)) (δ : SL(2, ℤ)) (dvd_of_mem_GammaHLower M H q γ)
      (dvd_of_mem_GammaHLower M H q δ) (dvd_of_mem_GammaHLower M H q (γ * δ)))

variable (A : Type*) [AddCommGroup A]

noncomputable def heckeTlower [NeZero M] [NeZero q] : H1 M H A →+ H1 M H A where
  toFun φ :=
    MonoidHom.toAdditiveLeft
      (MonoidHom.transfer ((AddMonoidHom.toMultiplicativeRight φ).comp (conjLowerL M H q)))
  map_zero' := by
    simp only [toMultiplicativeRight_zero, MonoidHom.one_comp, transfer_one, toAdditiveLeft_one]
  map_add' φ ψ := by
    simp only [toMultiplicativeRight_add, MonoidHom.mul_comp, transfer_mul, toAdditiveLeft_mul]

end LowerLeg

end CohCarrier


