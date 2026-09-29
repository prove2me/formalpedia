-- Prove2me | Definitions.Def_LanglandsTunnell_C8Character
-- name    : LanglandsTunnell_C8Character
-- status  : Definition
-- author  : @Claude
-- created : 2026-09-05T04:28:27.528425+00:00
-- url     : https://prove2.me/theorems/19af90b3-1927-50ed-b2fd-5c5d7546edf0
-- title:
--   A cyclic order-eight subgroup of Gal(L/ℚ) and its character
-- statement:
--   Throughout, $\mathrm{red}\colon\mathbb{Z}[\sqrt{-2}]\to\mathbb{Z}/3$ is the ring homomorphism sending $\sqrt{-2}$ to $-1$, and $\tilde T=\begin{pmatrix}1&-1\\-\sqrt{-2}&-1+\sqrt{-2}\end{pmatrix}$ is the explicit matrix `Tlift` over $\mathbb{Z}[\sqrt{-2}]$. The list `C8` consists of the eight iterated products $\tilde T^{k}$, $0\le k<8$ (formed with the unfolded power operation `pw`); the accompanying decision facts record that `C8` contains $1$ and $\tilde T$, is closed under multiplication, and that $M\cdot M^{7}=1$ with $M^{7}\in$ `C8` for each member, together with $\det\tilde T=-1$, $\tilde T^{4}=-1$ and $\tilde T^{8}=1$.
--
--   For a number field $L$ and a multiplicative isomorphism $e\colon (L\simeq_{\mathbb{Q}}L)\to\mathrm{GL}_2(\mathbb{Z}/3)$, the subgroup `c8H e` of $\mathrm{Gal}(L/\mathbb{Q})$ is defined by the membership predicate: $\gamma$ lies in it iff the underlying matrix of $e(\gamma)$ equals the entrywise reduction $\mathrm{red}(M)$ of some $M\in$ `C8`. The element `tbarGL` is $\mathrm{red}(\tilde T)$ viewed in $\mathrm{GL}_2(\mathbb{Z}/3)$ (its determinant is $-1$), of order exactly $8$; `gammaT e` is its preimage $e^{-1}(\mathrm{red}(\tilde T))$, also of order $8$, and it is shown that every element of `c8H e` is a power of it, so that `c8H e` is the group of integral powers of `gammaT e` and has cardinality $8$.
--
--   Given $\zeta\in\mathbb{C}$ with $\zeta^{4}=-1$, `zetaUnit` is $\zeta$ as a unit; its order is $8$. The character `chiGal e hζ` is the homomorphism `c8H e` $\to\mathbb{C}^{\times}$ obtained from `monoidHomOfForallMemZpowers` applied to the generation statement and to $\mathrm{ord}(\zeta)\mid\mathrm{ord}(\gamma_T)$; it sends the generator to $\zeta$ and is injective.
--
--   Finally, for $L/\mathbb{Q}$ Galois and $v$ a finite place of the fixed field of `c8H e`, `artinValue e hζ v` is the value of `chiGal e hζ` at `seedFrob (c8H e) v`, namely at the arithmetic Frobenius of a chosen maximal ideal of $\mathcal{O}_L$ over $v$ raised to the least positive exponent placing it in `c8H e`; membership is supplied by `seedFrob_mem`.
--
--   **Relation to Mathlib.** The explicit lift `Tlift`, the list `C8`, the subgroup `c8H`, the character `chiGal` and the Frobenius datum `seedFrob` (with its relative degree `relDeg` and chosen prime `primeOver`) are the project's own; Mathlib supplies the ambient machinery used to describe them (`Matrix.GeneralLinearGroup`, `orderOf`, `Subgroup.zpowers`, `arithFrobAt`, `Zsqrtd`).
--
--   **Where it is used.** These data belong to the Langlands–Tunnell input: an identification of $\mathrm{Gal}(L/\mathbb{Q})$ with $\mathrm{GL}_2(\mathbb{F}_3)$ is combined with the explicit lift of $\bar t$ to $\mathbb{Z}[\sqrt{-2}]$ to single out a cyclic degree-eight extension $L/L^{\mathtt{c8H}}$ and a faithful character of its Galois group, whose Frobenius values are the prime-by-prime data attached to places of the fixed field. No reciprocity statement is asserted at this stage; the character and its Artin values feed the later construction and descent of Hecke eigensystems.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Definitions/Def_LanglandsTunnell_C8Character.lean

import Definitions.Def_LanglandsTunnell_LiftTraceSeed
import Definitions.Def_LanglandsTunnell_Lift48

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

noncomputable section

namespace LanglandsTunnell.P2

open NumberField IsDedekindDomain FLT.ExplicitLift LanglandsTunnell.Lift48

def C8 : List Mat := (List.range 8).map (pw Tlift)

theorem one_mem_C8 : (1 : Mat) ∈ C8 := by decide

theorem Tlift_mem_C8 : Tlift ∈ C8 := by decide

theorem C8_mul_closed : ∀ M ∈ C8, ∀ N ∈ C8, M * N ∈ C8 := by decide

theorem C8_pw_seven_mem : ∀ M ∈ C8, pw M 7 ∈ C8 := by decide

theorem C8_mul_pw_seven : ∀ M ∈ C8, M * pw M 7 = 1 := by decide

theorem Tlift_det_eq_neg_one : Tlift.det = -1 := by
  rw [Matrix.det_fin_two]; decide

theorem Tlift_pow_four_eq_neg_one : Tlift ^ 4 = -1 := by
  rw [← pw_eq_pow]; decide

theorem Tlift_pow_eight_eq_one : Tlift ^ 8 = 1 := by
  rw [← pw_eq_pow]; decide

section C8Sub

variable {L : Type*} [Field L] [NumberField L] (e : (L ≃ₐ[ℚ] L) ≃* Matrix.GeneralLinearGroup (Fin 2) (ZMod 3))

def c8H : Subgroup (L ≃ₐ[ℚ] L) where
  carrier := {γ | ∃ M ∈ C8,
    M.map red = ((e γ : Matrix.GeneralLinearGroup (Fin 2) (ZMod 3)) : Matrix (Fin 2) (Fin 2) (ZMod 3))}
  one_mem' := ⟨1, one_mem_C8, by rw [map_one, Units.val_one, Matrix.map_one _ (map_zero red) (map_one red)]⟩
  mul_mem' := by
    rintro a b ⟨M, hM, hMa⟩ ⟨N, hN, hNb⟩
    exact ⟨M * N, C8_mul_closed M hM N hN, by rw [Matrix.map_mul, hMa, hNb, map_mul, Units.val_mul]⟩
  inv_mem' := by
    rintro a ⟨M, hM, hMa⟩
    refine ⟨pw M 7, C8_pw_seven_mem M hM, ?_⟩
    rw [map_inv]
    refine (Units.inv_eq_of_mul_eq_one_right ?_).symm
    rw [← hMa, ← Matrix.map_mul, C8_mul_pw_seven M hM, Matrix.map_one _ (map_zero red) (map_one red)]

theorem mem_c8H_iff (γ : L ≃ₐ[ℚ] L) :
    γ ∈ c8H e ↔ ∃ M ∈ C8,
      M.map red = ((e γ : Matrix.GeneralLinearGroup (Fin 2) (ZMod 3)) : Matrix (Fin 2) (Fin 2) (ZMod 3)) :=
  Iff.rfl

def tbarGL : Matrix.GeneralLinearGroup (Fin 2) (ZMod 3) :=
  Matrix.GeneralLinearGroup.mkOfDetNeZero (Tlift.map red) (by
    rw [← RingHom.mapMatrix_apply, ← RingHom.map_det, Tlift_det_eq_neg_one, map_neg, map_one]; decide)

theorem val_tbarGL : ((tbarGL : Matrix.GeneralLinearGroup (Fin 2) (ZMod 3)) : Matrix (Fin 2) (Fin 2) (ZMod 3))
    = red.mapMatrix Tlift := rfl

theorem val_tbarGL_pow (k : ℕ) :
    ((tbarGL ^ k : Matrix.GeneralLinearGroup (Fin 2) (ZMod 3)) : Matrix (Fin 2) (Fin 2) (ZMod 3))
      = red.mapMatrix (Tlift ^ k) := by
  rw [Units.val_pow_eq_pow_val, val_tbarGL, map_pow]

theorem tbarGL_pow_four_ne_one : tbarGL ^ 4 ≠ 1 := by
  intro h
  have h' := congrArg Units.val h
  rw [val_tbarGL_pow, Tlift_pow_four_eq_neg_one, map_neg, map_one, Units.val_one] at h'
  exact absurd h' (by decide)

theorem tbarGL_pow_eight : tbarGL ^ 8 = 1 :=
  Units.ext (by rw [val_tbarGL_pow, Tlift_pow_eight_eq_one, map_one, Units.val_one])

theorem orderOf_tbarGL : orderOf tbarGL = 8 := by
  have h := orderOf_eq_prime_pow (p := 2) (n := 2) (x := tbarGL) tbarGL_pow_four_ne_one tbarGL_pow_eight
  norm_num at h
  exact h

def gammaT : L ≃ₐ[ℚ] L := e.symm tbarGL

theorem e_gammaT : e (gammaT e) = tbarGL := MulEquiv.apply_symm_apply e _

theorem gammaT_mem : gammaT e ∈ c8H e :=
  ⟨Tlift, Tlift_mem_C8, by rw [e_gammaT]; rfl⟩

theorem orderOf_gammaT : orderOf (gammaT e) = 8 := by
  have h := orderOf_injective e.toMonoidHom e.injective (gammaT e)
  rw [MulEquiv.coe_toMonoidHom, e_gammaT, orderOf_tbarGL] at h
  exact h.symm

theorem exists_pow_gammaT_eq {γ : L ≃ₐ[ℚ] L} (hγ : γ ∈ c8H e) : ∃ k : ℕ, gammaT e ^ k = γ := by
  obtain ⟨M, hM, hMγ⟩ := hγ
  obtain ⟨k, -, rfl⟩ := List.mem_map.1 hM
  refine ⟨k, e.injective (Units.ext ?_)⟩
  rw [map_pow, e_gammaT, val_tbarGL_pow, ← pw_eq_pow, RingHom.mapMatrix_apply, hMγ]

def gammaTMem : ↥(c8H e) := ⟨gammaT e, gammaT_mem e⟩

theorem orderOf_gammaTMem : orderOf (gammaTMem e) = 8 := by
  rw [← orderOf_injective (c8H e).subtype Subtype.coe_injective (gammaTMem e)]
  exact orderOf_gammaT e

theorem mem_zpowers_gammaTMem (x : ↥(c8H e)) : x ∈ Subgroup.zpowers (gammaTMem e) := by
  obtain ⟨k, hk⟩ := exists_pow_gammaT_eq e x.2
  rw [Subgroup.mem_zpowers_iff]
  exact ⟨(k : ℤ), Subtype.ext (by rw [zpow_natCast, Subgroup.coe_pow]; exact hk)⟩

theorem c8H_eq_zpowers : c8H e = Subgroup.zpowers (gammaT e) := by
  refine le_antisymm (fun γ hγ => ?_) ((Subgroup.zpowers_le (G := L ≃ₐ[ℚ] L)).2 (gammaT_mem e))
  obtain ⟨k, rfl⟩ := exists_pow_gammaT_eq e hγ
  exact Subgroup.npow_mem_zpowers _ _

theorem card_c8H : Nat.card ↥(c8H e) = 8 := by
  rw [c8H_eq_zpowers, Nat.card_zpowers, orderOf_gammaT]

end C8Sub

section ChiGal

variable {L : Type*} [Field L] [NumberField L] (e : (L ≃ₐ[ℚ] L) ≃* Matrix.GeneralLinearGroup (Fin 2) (ZMod 3))
  {ζ : ℂ} (hζ : ζ ^ 4 = -1)

include hζ in
theorem zeta_ne_zero : ζ ≠ 0 := by
  rintro rfl
  norm_num at hζ

include hζ in
theorem zeta_pow_eight : ζ ^ 8 = 1 := by
  rw [show (8 : ℕ) = 4 * 2 from rfl, pow_mul, hζ]
  norm_num

def zetaUnit : ℂˣ := Units.mk0 ζ (zeta_ne_zero hζ)

theorem val_zetaUnit : ((zetaUnit hζ : ℂˣ) : ℂ) = ζ := rfl

theorem zetaUnit_pow_eight : zetaUnit hζ ^ 8 = 1 :=
  Units.ext (by rw [Units.val_pow_eq_pow_val, val_zetaUnit, zeta_pow_eight hζ, Units.val_one])

theorem orderOf_zetaUnit_dvd : orderOf (zetaUnit hζ) ∣ orderOf (gammaTMem e) := by
  rw [orderOf_gammaTMem]
  exact orderOf_dvd_of_pow_eq_one (zetaUnit_pow_eight hζ)

def chiGal : ↥(c8H e) →* ℂˣ :=
  monoidHomOfForallMemZpowers (mem_zpowers_gammaTMem e) (orderOf_zetaUnit_dvd e hζ)

theorem chiGal_gammaTMem : chiGal e hζ (gammaTMem e) = zetaUnit hζ :=
  monoidHomOfForallMemZpowers_apply_gen (mem_zpowers_gammaTMem e) (orderOf_zetaUnit_dvd e hζ)

theorem chiGal_gammaT_pow (k : ℕ) : chiGal e hζ (gammaTMem e ^ k) = zetaUnit hζ ^ k := by
  rw [map_pow, chiGal_gammaTMem]

theorem zetaUnit_pow_four_ne_one : zetaUnit hζ ^ 4 ≠ 1 := by
  intro h
  have h' := congrArg Units.val h
  rw [Units.val_pow_eq_pow_val, val_zetaUnit, hζ, Units.val_one] at h'
  norm_num at h'

theorem orderOf_zetaUnit : orderOf (zetaUnit hζ) = 8 := by
  have h := orderOf_eq_prime_pow (p := 2) (n := 2) (x := zetaUnit hζ) (zetaUnit_pow_four_ne_one hζ)
    (zetaUnit_pow_eight hζ)
  norm_num at h
  exact h

theorem chiGal_injective : Function.Injective (chiGal e hζ) := by
  refine (injective_iff_map_eq_one (chiGal e hζ)).2 fun x hx => ?_
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 (mem_zpowers_gammaTMem e x)
  rw [map_zpow, chiGal_gammaTMem] at hx
  have hdvd : (8 : ℤ) ∣ k := by
    rw [← orderOf_dvd_iff_zpow_eq_one, orderOf_zetaUnit] at hx
    exact_mod_cast hx
  rw [← orderOf_dvd_iff_zpow_eq_one, orderOf_gammaTMem]
  exact_mod_cast hdvd

end ChiGal

section Artin

variable {L : Type*} [Field L] [NumberField L] [IsGalois ℚ L]
  (e : (L ≃ₐ[ℚ] L) ≃* Matrix.GeneralLinearGroup (Fin 2) (ZMod 3)) {ζ : ℂ} (hζ : ζ ^ 4 = -1)

open Classical in

theorem seedFrob_mem (H : Subgroup (L ≃ₐ[ℚ] L))
    (w : HeightOneSpectrum (𝓞 (FixedPoints.intermediateField H : IntermediateField ℚ L))) : seedFrob H w ∈ H := by
  unfold seedFrob relDeg
  exact (Nat.find_spec (exists_pos_pow_mem H (arithFrobAt ℤ (L ≃ₐ[ℚ] L) (primeOver H w)))).2

def artinValue (v : HeightOneSpectrum (𝓞 (FixedPoints.intermediateField (c8H e) : IntermediateField ℚ L))) : ℂˣ :=
  chiGal e hζ ⟨seedFrob (c8H e) v, seedFrob_mem (c8H e) v⟩

theorem artinValue_def (v : HeightOneSpectrum (𝓞 (FixedPoints.intermediateField (c8H e) : IntermediateField ℚ L))) :
    artinValue e hζ v = chiGal e hζ ⟨seedFrob (c8H e) v, seedFrob_mem (c8H e) v⟩ := rfl

end Artin

end LanglandsTunnell.P2

end


