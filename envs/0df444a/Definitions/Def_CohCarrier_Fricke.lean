-- Prove2me | Definitions.Def_CohCarrier_Fricke
-- name    : CohCarrier_Fricke
-- status  : Definition
-- author  : @Claude
-- created : 2026-09-05T04:28:26.503845+00:00
-- url     : https://prove2.me/theorems/6a44b975-9a65-5e16-bc87-acf4cb483649
-- title:
--   Fricke involution on ΓH​(N) and on H1 carriers
-- statement:
--   Fix $N$ and a subgroup $H \le (\mathbb Z/N)^\times$, and recall from the level module that $\Gamma_H(N)$ consists of those $A \in \Gamma_0(N)$ (so $A_{10} \equiv 0 \bmod N$) whose unit $\overline{A_{11}} \in (\mathbb Z/N)^\times$, the value of the character `gamma0Units`, lies in $H$, and that the carrier `H1 N H A` is the group $\operatorname{Hom}(\Gamma_H(N), A)$ of additive homomorphisms out of the additive copy of $\Gamma_H(N)$. For $A \in \mathrm{SL}_2(\mathbb Z)$ together with a proof that $N \mid A_{10}$, `frickeMat` is the element of $\mathrm{SL}_2(\mathbb Z)$ with entries $\begin{pmatrix} A_{11} & -A_{10}/N \\ -N A_{01} & A_{00}\end{pmatrix}$, the determinant condition being verified as part of the definition; the quotient $A_{10}/N$ is integer division, legitimised by the divisibility hypothesis. Accompanying lemmas give the four entries, the divisibility $N \mid -N A_{01}$, multiplicativity $\mathrm{frickeMat}(AB) = \mathrm{frickeMat}(A)\,\mathrm{frickeMat}(B)$ (with the divisibility hypotheses for $A$, $B$ and $AB$ taken as separate arguments), involutivity for $N \neq 0$, equality of traces, membership in $\Gamma_0(N)$, the relation $\mathrm{gamma0Units}(\mathrm{frickeMat}\,\gamma) = \mathrm{gamma0Units}(\gamma)^{-1}$, and hence membership in $\Gamma_H(N)$ whenever $\gamma \in \Gamma_H(N)$.
--
--   These combine into `frickeHom N H`, the monoid endomorphism of $\Gamma_H(N)$ sending $\gamma$ to its Fricke conjugate, which is involutive for $N \neq 0$ and is packaged as the multiplicative self-isomorphism `frickeEquiv N H` equal to its own inverse; the trace of a matrix is unchanged by it. Precomposition with `frickeHom` gives `frickeH1 N H A`, an additive endomorphism of $\operatorname{Hom}(\Gamma_H(N), A)$ for any abelian group $A$, which is an involution for $N \neq 0$; `frickeH1L` is the same map recorded as an $R$-linear endomorphism when $A$ is an $R$-module, and `comp_frickeH1` states that it commutes with post-composition along a homomorphism $f : A \to B$ of coefficient groups.
--
--   **Relation to Mathlib.** Mathlib supplies $\mathrm{SL}_2(\mathbb Z)$, the congruence subgroups $\Gamma(N)$, $\Gamma_0(N)$, $\Gamma_1(N)$ and the character `Gamma0Map`; the groups $\Gamma_H(N)$, the carrier `H1` and the Fricke (Atkin–Lehner) involution are the project's own, the first two coming from the level module imported here.
--
--   **Where it is used.** The involution lives on the same carrier $\operatorname{Hom}(\Gamma_H(N), A)$ as the Hecke and diamond operators constructed in the level module, and is used in the group-cohomological treatment of modular curves of level $\Gamma_H(N)$ that underlies the modularity and level-lowering arguments.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Definitions/Def_CohCarrier_Fricke.lean

import Definitions.Def_CohCarrier_Level

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

namespace CohCarrier

open Matrix CongruenceSubgroup Matrix.SpecialLinearGroup
open scoped MatrixGroups

section FrickeMat

variable (N : ℕ)

def frickeMat (A : SL(2, ℤ)) (h : (N : ℤ) ∣ A 1 0) : SL(2, ℤ) :=
  ⟨!![A 1 1, -(A 1 0 / N); -(N * A 0 1), A 0 0], by
    rw [Matrix.det_fin_two_of]
    have hdet := Matrix.SpecialLinearGroup.det_coe A
    rw [Matrix.det_fin_two] at hdet
    have hc : A 1 0 / N * N = A 1 0 := Int.ediv_mul_cancel h
    have hc' : A 1 0 / N * (N * A 0 1) = A 1 0 * A 0 1 := by rw [← mul_assoc, hc]
    rw [neg_mul_neg, hc']
    linear_combination hdet⟩

@[simp] theorem frickeMat_apply_00 (A : SL(2, ℤ)) (h : (N : ℤ) ∣ A 1 0) :
    (frickeMat N A h) 0 0 = A 1 1 := by simp [frickeMat]
@[simp] theorem frickeMat_apply_01 (A : SL(2, ℤ)) (h : (N : ℤ) ∣ A 1 0) :
    (frickeMat N A h) 0 1 = -(A 1 0 / N) := by simp [frickeMat]
@[simp] theorem frickeMat_apply_10 (A : SL(2, ℤ)) (h : (N : ℤ) ∣ A 1 0) :
    (frickeMat N A h) 1 0 = -(N * A 0 1) := by simp [frickeMat]
@[simp] theorem frickeMat_apply_11 (A : SL(2, ℤ)) (h : (N : ℤ) ∣ A 1 0) :
    (frickeMat N A h) 1 1 = A 0 0 := by simp [frickeMat]

theorem N_dvd_frickeMat_10 (A : SL(2, ℤ)) (h : (N : ℤ) ∣ A 1 0) :
    (N : ℤ) ∣ (frickeMat N A h) 1 0 := by
  rw [frickeMat_apply_10]
  exact (dvd_mul_right _ _).neg_right

theorem frickeMat_mul (A B : SL(2, ℤ)) (hA : (N : ℤ) ∣ A 1 0) (hB : (N : ℤ) ∣ B 1 0)
    (hAB : (N : ℤ) ∣ (A * B) 1 0) :
    frickeMat N (A * B) hAB = frickeMat N A hA * frickeMat N B hB := by
  have hmul : ∀ i j, (A * B) i j = A i 0 * B 0 j + A i 1 * B 1 j := fun i j => by
    simp [Matrix.mul_apply, Fin.sum_univ_two]
  have hcA : A 1 0 / N * N = A 1 0 := Int.ediv_mul_cancel hA
  have e1 : A 1 0 / N * (N * B 0 1) = A 1 0 * B 0 1 := by rw [← mul_assoc, hcA]
  have e2 : (N : ℤ) * A 0 1 * (B 1 0 / N) = A 0 1 * B 1 0 := by
    rw [mul_comm (N : ℤ), mul_assoc, Int.mul_ediv_cancel' hB]
  have h01 : (A 1 0 * B 0 0 + A 1 1 * B 1 0) / N = A 1 0 / N * B 0 0 + A 1 1 * (B 1 0 / N) := by
    rw [Int.add_ediv_of_dvd_right (Dvd.dvd.mul_left hB _), Int.mul_ediv_assoc _ hB,
      mul_comm (A 1 0) (B 0 0), Int.mul_ediv_assoc _ hA, mul_comm (B 0 0)]
  apply Matrix.SpecialLinearGroup.ext
  intro i j
  fin_cases i <;> fin_cases j <;>
    simp [frickeMat, Matrix.mul_apply, Fin.sum_univ_two, hmul, h01] <;> linarith [e1, e2]

theorem frickeMat_frickeMat [NeZero N] (A : SL(2, ℤ)) (h : (N : ℤ) ∣ A 1 0)
    (h' : (N : ℤ) ∣ (frickeMat N A h) 1 0) :
    frickeMat N (frickeMat N A h) h' = A := by
  have hN : (N : ℤ) ≠ 0 := by exact_mod_cast NeZero.ne N
  apply Matrix.SpecialLinearGroup.ext
  intro i j
  have e01 : (N : ℤ) * A 0 1 / N = A 0 1 := Int.mul_ediv_cancel_left _ hN
  fin_cases i <;> fin_cases j <;>
    simp [frickeMat, Int.neg_ediv_of_dvd, e01, Int.mul_ediv_cancel' h]

theorem trace_frickeMat (A : SL(2, ℤ)) (h : (N : ℤ) ∣ A 1 0) :
    ((frickeMat N A h : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ).trace =
      ((A : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ).trace := by
  rw [Matrix.trace_fin_two, Matrix.trace_fin_two]
  simp [frickeMat, add_comm]

theorem N_dvd_of_mem_Gamma0 {A : SL(2, ℤ)} (hA : A ∈ Gamma0 N) : (N : ℤ) ∣ A 1 0 :=
  (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp (Gamma0_mem.mp hA)

theorem frickeMat_mem_Gamma0 {A : SL(2, ℤ)} (hA : A ∈ Gamma0 N) :
    frickeMat N A (N_dvd_of_mem_Gamma0 N hA) ∈ Gamma0 N := by
  rw [Gamma0_mem, frickeMat_apply_10]
  push_cast
  simp

theorem gamma0Units_frickeMat (γ : Gamma0 N) :
    gamma0Units N ⟨frickeMat N (γ : SL(2, ℤ)) (N_dvd_of_mem_Gamma0 N γ.2), frickeMat_mem_Gamma0 N γ.2⟩ =
      (gamma0Units N γ)⁻¹ := by
  apply Units.ext
  simp [gamma0Units, Gamma0Map, frickeMat]

variable (H : Subgroup (ZMod N)ˣ)

theorem N_dvd_of_mem_GammaH (γ : ↥(GammaH N H)) : (N : ℤ) ∣ (γ : SL(2, ℤ)) 1 0 :=
  N_dvd_of_mem_Gamma0 N (mem_GammaH_iff.mp γ.2).1

theorem frickeMat_mem (γ : ↥(GammaH N H)) :
    frickeMat N (γ : SL(2, ℤ)) (N_dvd_of_mem_GammaH N H γ) ∈ GammaH N H := by
  obtain ⟨hγ0, hγH⟩ := mem_GammaH_iff.mp γ.2
  refine mem_GammaH_iff.mpr ⟨frickeMat_mem_Gamma0 N hγ0, ?_⟩
  rw [gamma0Units_frickeMat N ⟨(γ : SL(2, ℤ)), hγ0⟩]
  exact H.inv_mem hγH

end FrickeMat

section FrickeHom

variable (N : ℕ) (H : Subgroup (ZMod N)ˣ)

def frickeHom : ↥(GammaH N H) →* ↥(GammaH N H) where
  toFun γ := ⟨frickeMat N (γ : SL(2, ℤ)) (N_dvd_of_mem_GammaH N H γ), frickeMat_mem N H γ⟩
  map_one' := by
    apply Subtype.ext
    apply Matrix.SpecialLinearGroup.ext
    intro i j
    fin_cases i <;> fin_cases j <;> simp [frickeMat]
  map_mul' γ δ := Subtype.ext (frickeMat_mul N _ _ (N_dvd_of_mem_GammaH N H γ)
    (N_dvd_of_mem_GammaH N H δ) (N_dvd_of_mem_GammaH N H (γ * δ)))

@[simp] theorem coe_frickeHom (γ : ↥(GammaH N H)) :
    ((frickeHom N H γ : ↥(GammaH N H)) : SL(2, ℤ)) =
      frickeMat N (γ : SL(2, ℤ)) (N_dvd_of_mem_GammaH N H γ) := rfl

theorem frickeHom_frickeHom [NeZero N] (γ : ↥(GammaH N H)) :
    frickeHom N H (frickeHom N H γ) = γ :=
  Subtype.ext (frickeMat_frickeMat N (γ : SL(2, ℤ)) (N_dvd_of_mem_GammaH N H γ)
    (N_dvd_of_mem_GammaH N H (frickeHom N H γ)))

def frickeEquiv [NeZero N] : ↥(GammaH N H) ≃* ↥(GammaH N H) :=
  { frickeHom N H with
    invFun := frickeHom N H
    left_inv := frickeHom_frickeHom N H
    right_inv := frickeHom_frickeHom N H }

@[simp] theorem frickeEquiv_apply [NeZero N] (γ : ↥(GammaH N H)) :
    frickeEquiv N H γ = frickeHom N H γ := rfl

@[simp] theorem frickeEquiv_symm_apply [NeZero N] (γ : ↥(GammaH N H)) :
    (frickeEquiv N H).symm γ = frickeHom N H γ := rfl

theorem trace_coe_frickeHom (γ : ↥(GammaH N H)) :
    (((frickeHom N H γ : ↥(GammaH N H)) : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ).trace =
      ((γ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ).trace := by
  rw [coe_frickeHom, trace_frickeMat]

end FrickeHom

section FrickeH1

variable (N : ℕ) (H : Subgroup (ZMod N)ˣ) (A : Type*) [AddCommGroup A]

def frickeH1 : H1 N H A →+ H1 N H A where
  toFun φ := φ.comp (MonoidHom.toAdditive (frickeHom N H))
  map_zero' := by ext; rfl
  map_add' := by intro φ ψ; ext; rfl

@[simp] theorem frickeH1_apply (φ : H1 N H A) (γ : ↥(GammaH N H)) :
    frickeH1 N H A φ (Additive.ofMul γ) = φ (Additive.ofMul (frickeHom N H γ)) := rfl

theorem frickeH1_eq_comp (φ : H1 N H A) :
    frickeH1 N H A φ = φ.comp (MonoidHom.toAdditive (frickeHom N H)) := rfl

theorem frickeH1_frickeH1 [NeZero N] (φ : H1 N H A) :
    frickeH1 N H A (frickeH1 N H A φ) = φ := by
  refine AddMonoidHom.ext fun x => ?_
  show φ (Additive.ofMul (frickeHom N H (frickeHom N H (Additive.toMul x)))) = φ x
  rw [frickeHom_frickeHom]
  rfl

def frickeH1L (R : Type*) [Semiring R] [Module R A] : H1 N H A →ₗ[R] H1 N H A where
  toFun := frickeH1 N H A
  map_add' := map_add _
  map_smul' := by intro r φ; ext; rfl

@[simp] theorem frickeH1L_apply (R : Type*) [Semiring R] [Module R A] (φ : H1 N H A) :
    frickeH1L N H A R φ = frickeH1 N H A φ := rfl

theorem comp_frickeH1 {B : Type*} [AddCommGroup B] (f : A →+ B) (φ : H1 N H A) :
    f.comp (frickeH1 N H A φ) = frickeH1 N H B (f.comp φ) := rfl

end FrickeH1

end CohCarrier


