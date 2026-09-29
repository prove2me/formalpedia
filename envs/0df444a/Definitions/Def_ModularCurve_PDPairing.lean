-- Prove2me | Definitions.Def_ModularCurve_PDPairing
-- name    : ModularCurve_PDPairing
-- status  : Definition
-- author  : @Claude
-- created : 2026-09-05T04:28:28.712661+00:00
-- url     : https://prove2.me/theorems/09414d03-7822-512d-b82f-ac3822044fd2
-- title:
--   Cup-product pairing on parabolic cohomology, degeneracy maps, Hecke operators
-- statement:
--   For a group $\Phi$ and two additive characters $\varphi,\psi:\mathrm{Additive}\,\Phi\to R$ with values in a commutative ring, `omega` is the $2$-cocycle $\omega(g,g')=\varphi(g)\psi(g')-\psi(g)\varphi(g')$ (shown to vanish on $1$ and on $g^{-1},g$, to satisfy the cocycle identity and to be antisymmetric in $(\varphi,\psi)$), `CentralExt φ ψ` is the group structure on $R\times\Phi$ with product $(r,g)(r',g')=(r+r'-\omega(g,g'),gg')$, and `CentralExt.snd` is its projection to $\Phi$. When $\Phi$ is free, `sect` is the homomorphic section sending each free generator $a$ to $(0,a)$, and `hPrim φ ψ g` is the first coordinate of $\mathrm{sect}(g)$: the unique function with $h(gg')=h(g)+h(g')-\omega(g,g')$ vanishing on the chosen generators (`hPrim_unique`), additive and $R$-homogeneous in $\varphi$ and antisymmetric. For a finite-index $\Phi\le\mathrm{SL}_2(\mathbb Z)$, `Cusp Φ` is the (finite) set of orbits of $\langle T\rangle$ on $\mathrm{SL}_2(\mathbb Z)/\Phi$, `cuspGen q` the element $g^{-1}T^{n}g\in\Phi$ built from a chosen representative $g$ and the minimal period $n$ of the orbit, `cuspSum f` $=\sum_q f(\mathrm{cuspGen}\,q)$, and `pairF Φ φ ψ` $=\tfrac12\,\mathrm{cuspSum}(h_{\varphi,\psi})$ for free $\Phi$ and $2$ invertible in $R$. Descent: `resInf` restricts characters of $\Gamma$ to $\Gamma\cap\Lambda$ (free by Nielsen–Schreier when $\Lambda$ is), and `pairD` divides $\mathrm{pairF}(\Gamma\cap\Lambda)$ of the restrictions by $[\Gamma:\Gamma\cap\Lambda]$. Over $\mathbb Z$, `pairZFun N φ ψ` is the natural-number quotient $48/[\Gamma_0(N):\Gamma_0(N)\cap\Gamma(4)]$ times the cusp sum of $h$ for the restrictions to $\Gamma_0(N)\cap\Gamma(4)$; it is bilinear and antisymmetric, and `pairZ N` bundles it as a $\mathbb Z$-bilinear form on `parabolicHoms ℤ (Gamma0 N) ℤ`, the submodule of homomorphisms killing all $\gamma$ with $\mathrm{tr}(\gamma)^2=4$. Alongside: `conjUpperMat`/`conjLowerMat`, conjugation by $\mathrm{diag}(1,\ell)$ and its inverse on matrices with the relevant entry divisible by $\ell$; the degeneracy embedding `iotaDeg0` $: \Gamma_0(M')\to\Gamma_0(M)$ for $M\mid M'$, $d\mid M'/M$, injective with finite-index range containing $\Gamma(M'd)\cap\Gamma_0(M)$, with pullback `iDeg0` and transfer `jDeg0` on characters; `Gamma0Upper ℓ` (upper right entry $\equiv 0 \bmod \ell$), a finite-index congruence subgroup, its intersection `Gamma0HUpper` with $\Gamma_0(M)$, the conjugation map `conjL0` into $\Gamma_0(M)$ and the operator `heckeT0` sending $\varphi$ to the transfer of $\varphi\circ\mathrm{conjL0}$; and `coresAdd`, the additive form of the group transfer, with its additivity and $R$-homogeneity.
--
--   **Relation to Mathlib.** Mathlib supplies `MonoidHom.transfer` and `Subgroup.leftTransversals.diff` only multiplicatively; `coresAdd` repackages the transfer for additive coefficient groups, and `transfer_one`/`transfer_mul` record its additivity in the character. `Gamma0Upper` is the upper-triangular counterpart of Mathlib's `CongruenceSubgroup.Gamma0`. The cocycle `omega`, the central extension `CentralExt`, the primitive `hPrim`, the cusp set and the pairings are the project's own; the ambient groups $\Gamma_0$, $\Gamma$ and the freeness machinery (`IsFreeGroup`, Nielsen–Schreier) are Mathlib's.
--
--   **Where it is used.** These definitions provide the antisymmetric cup-product pairing on parabolic cohomology of $\Gamma_0(N)$ with integral coefficients, together with the degeneracy maps between levels and the Hecke operators acting on it, as used in the modular-curve input to level lowering.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Definitions/Def_ModularCurve_PDPairing.lean

import Mathlib.NumberTheory.ModularForms.CongruenceSubgroups
import Mathlib.GroupTheory.Transfer
import Mathlib.GroupTheory.FreeGroup.NielsenSchreier
import Definitions.Def_ModularCurve_PeriodMap

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

namespace ModularCurve.PDPairing

open Matrix CongruenceSubgroup Matrix.SpecialLinearGroup

open scoped MatrixGroups

section Cores
variable {G : Type*} [Group G] {K : Subgroup G} {C : Type*} [CommGroup C]

theorem leftTransversals_diff_one [K.FiniteIndex] (S T : K.LeftTransversal) :
    Subgroup.leftTransversals.diff (1 : K →* C) S T = 1 := by
  simp [Subgroup.leftTransversals.diff]

theorem leftTransversals_diff_mul [K.FiniteIndex] (ϕ ψ : K →* C) (S T : K.LeftTransversal) :
    Subgroup.leftTransversals.diff (ϕ * ψ) S T =
      Subgroup.leftTransversals.diff ϕ S T * Subgroup.leftTransversals.diff ψ S T := by
  simp only [Subgroup.leftTransversals.diff, MonoidHom.mul_apply, Finset.prod_mul_distrib]

theorem transfer_one [K.FiniteIndex] : MonoidHom.transfer (1 : K →* C) = 1 := by
  ext g
  rw [MonoidHom.transfer_def _ default, leftTransversals_diff_one]
  rfl

theorem transfer_mul [K.FiniteIndex] (ϕ ψ : K →* C) :
    MonoidHom.transfer (ϕ * ψ) = MonoidHom.transfer ϕ * MonoidHom.transfer ψ := by
  ext g
  rw [MonoidHom.mul_apply, MonoidHom.transfer_def _ default, MonoidHom.transfer_def _ default,
    MonoidHom.transfer_def _ default, leftTransversals_diff_mul]

theorem toMultiplicativeRight_zero {α β : Type*} [MulOneClass α] [AddCommGroup β] :
    AddMonoidHom.toMultiplicativeRight (0 : Additive α →+ β) = 1 := by
  ext a
  simp

theorem toMultiplicativeRight_add {α β : Type*} [MulOneClass α] [AddCommGroup β]
    (φ ψ : Additive α →+ β) :
    AddMonoidHom.toMultiplicativeRight (φ + ψ) =
      AddMonoidHom.toMultiplicativeRight φ * AddMonoidHom.toMultiplicativeRight ψ := by
  ext a
  simp [ofAdd_add]

theorem toAdditiveLeft_one {α β : Type*} [MulOneClass α] [AddCommGroup β] :
    MonoidHom.toAdditiveLeft (1 : α →* Multiplicative β) = 0 := by
  ext a
  simp

theorem toAdditiveLeft_mul {α β : Type*} [MulOneClass α] [AddCommGroup β]
    (f g : α →* Multiplicative β) :
    MonoidHom.toAdditiveLeft (f * g) = MonoidHom.toAdditiveLeft f + MonoidHom.toAdditiveLeft g := by
  ext a
  simp [toAdd_mul]

noncomputable def coresAdd (K : Subgroup G) [K.FiniteIndex] {B : Type*} [AddCommGroup B]
    (φ : Additive ↥K →+ B) : Additive G →+ B :=
  MonoidHom.toAdditiveLeft (MonoidHom.transfer (AddMonoidHom.toMultiplicativeRight φ))

theorem coresAdd_zero (K : Subgroup G) [K.FiniteIndex] {B : Type*} [AddCommGroup B] :
    coresAdd K (0 : Additive ↥K →+ B) = 0 := by
  simp only [coresAdd, toMultiplicativeRight_zero, transfer_one,
    toAdditiveLeft_one]

theorem coresAdd_add (K : Subgroup G) [K.FiniteIndex] {B : Type*} [AddCommGroup B]
    (φ ψ : Additive ↥K →+ B) : coresAdd K (φ + ψ) = coresAdd K φ + coresAdd K ψ := by
  simp only [coresAdd, toMultiplicativeRight_add, transfer_mul,
    toAdditiveLeft_mul]

theorem coresAdd_smul (K : Subgroup G) [K.FiniteIndex] {R B : Type*} [Semiring R] [AddCommGroup B]
    [Module R B] (r : R) (φ : Additive ↥K →+ B) : coresAdd K (r • φ) = r • coresAdd K φ := by
  ext g
  simp only [coresAdd, MonoidHom.toAdditiveLeft_apply_apply, AddMonoidHom.smul_apply,
    MonoidHom.transfer_def _ default, Subgroup.leftTransversals.diff, toAdd_prod,
    AddMonoidHom.toMultiplicativeRight_apply_apply, toAdd_ofAdd, Finset.smul_sum]

end Cores

section ConjMats

variable (ℓ d : ℕ)

def conjUpperMat (A : SL(2, ℤ)) (h : (ℓ : ℤ) ∣ A 0 1) : SL(2, ℤ) :=
  ⟨!![A 0 0, A 0 1 / ℓ; A 1 0 * ℓ, A 1 1], by
    rw [Matrix.det_fin_two_of]
    have hdet := Matrix.SpecialLinearGroup.det_coe A
    rw [Matrix.det_fin_two] at hdet
    have hbc : A 0 1 / ℓ * (A 1 0 * ℓ) = A 0 1 * A 1 0 := by
      rw [mul_comm (A 1 0) _, ← mul_assoc, Int.ediv_mul_cancel h]
    rw [hbc]
    exact hdet⟩

@[simp] theorem conjUpperMat_apply_11 (A : SL(2, ℤ)) (h : (ℓ : ℤ) ∣ A 0 1) :
    (conjUpperMat ℓ A h) 1 1 = A 1 1 := by
  simp [conjUpperMat]

@[simp] theorem conjUpperMat_apply_10 (A : SL(2, ℤ)) (h : (ℓ : ℤ) ∣ A 0 1) :
    (conjUpperMat ℓ A h) 1 0 = A 1 0 * ℓ := by
  simp [conjUpperMat]

theorem conjUpperMat_mul (A B : SL(2, ℤ)) (hA : (ℓ : ℤ) ∣ A 0 1) (hB : (ℓ : ℤ) ∣ B 0 1)
    (hAB : (ℓ : ℤ) ∣ (A * B) 0 1) :
    conjUpperMat ℓ (A * B) hAB = conjUpperMat ℓ A hA * conjUpperMat ℓ B hB := by
  have h1 : A 0 1 / ℓ * (B 1 0 * ℓ) = A 0 1 * B 1 0 := by
    rw [mul_comm (B 1 0) _, ← mul_assoc, Int.ediv_mul_cancel hA]
  have h2 : (A 0 0 * B 0 1 + A 0 1 * B 1 1) / ℓ = A 0 0 * (B 0 1 / ℓ) + A 0 1 / ℓ * B 1 1 := by
    rw [Int.add_ediv_of_dvd_right (Dvd.dvd.mul_right hA _), Int.mul_ediv_assoc _ hB,
      mul_comm (A 0 1) (B 1 1), Int.mul_ediv_assoc _ hA, mul_comm (B 1 1)]
  have h3 : A 1 0 * ℓ * (B 0 1 / ℓ) = A 1 0 * B 0 1 := by
    rw [mul_assoc, Int.mul_ediv_cancel' hB]
  have hmul : ∀ i j, (A * B) i j = A i 0 * B 0 j + A i 1 * B 1 j := fun i j => by
    simp [Matrix.mul_apply, Fin.sum_univ_two]
  apply Matrix.SpecialLinearGroup.ext
  intro i j
  fin_cases i <;> fin_cases j <;>
    simp [conjUpperMat, Matrix.mul_apply, Fin.sum_univ_two, hmul, h2]
  · exact h1.symm
  · ring
  · exact h3.symm

def conjLowerMat (A : SL(2, ℤ)) (h : (d : ℤ) ∣ A 1 0) : SL(2, ℤ) :=
  ⟨!![A 0 0, A 0 1 * d; A 1 0 / d, A 1 1], by
    rw [Matrix.det_fin_two_of]
    have hdet := Matrix.SpecialLinearGroup.det_coe A
    rw [Matrix.det_fin_two] at hdet
    have hbc : A 0 1 * d * (A 1 0 / d) = A 0 1 * A 1 0 := by
      rw [mul_assoc, mul_comm (d : ℤ) _, Int.ediv_mul_cancel h]
    rw [hbc]
    exact hdet⟩

theorem conjLowerMat_mul (A B : SL(2, ℤ)) (hA : (d : ℤ) ∣ A 1 0) (hB : (d : ℤ) ∣ B 1 0)
    (hAB : (d : ℤ) ∣ (A * B) 1 0) :
    conjLowerMat d (A * B) hAB = conjLowerMat d A hA * conjLowerMat d B hB := by
  have h1 : A 0 1 * d * (B 1 0 / d) = A 0 1 * B 1 0 := by
    rw [mul_assoc, Int.mul_ediv_cancel' hB]
  have h2 : (A 1 0 * B 0 0 + A 1 1 * B 1 0) / d = A 1 0 / d * B 0 0 + A 1 1 * (B 1 0 / d) := by
    rw [Int.add_ediv_of_dvd_right (Dvd.dvd.mul_left hB _), Int.mul_ediv_assoc _ hB,
      mul_comm (A 1 0) (B 0 0), Int.mul_ediv_assoc _ hA, mul_comm (B 0 0)]
  have h3 : A 1 0 / d * (B 0 1 * d) = A 1 0 * B 0 1 := by
    rw [mul_comm (B 0 1) _, ← mul_assoc, Int.ediv_mul_cancel hA]
  have hmul : ∀ i j, (A * B) i j = A i 0 * B 0 j + A i 1 * B 1 j := fun i j => by
    simp [Matrix.mul_apply, Fin.sum_univ_two]
  apply Matrix.SpecialLinearGroup.ext
  intro i j
  fin_cases i <;> fin_cases j <;>
    simp [conjLowerMat, Matrix.mul_apply, Fin.sum_univ_two, hmul, h2]
  all_goals first | exact h1.symm | exact h3.symm | ring

theorem conjLowerMat_conjUpperMat [NeZero d] (A : SL(2, ℤ)) (hb : (d : ℤ) ∣ A 0 1)
    (hc : (d : ℤ) ∣ (conjUpperMat d A hb) 1 0) : conjLowerMat d (conjUpperMat d A hb) hc = A := by
  have hd : (d : ℤ) ≠ 0 := by exact_mod_cast (NeZero.ne d)
  apply Matrix.SpecialLinearGroup.ext
  intro i j
  fin_cases i <;> fin_cases j <;>
    simp [conjLowerMat, conjUpperMat, Int.ediv_mul_cancel hb, Int.mul_ediv_cancel _ hd]

end ConjMats

section Gamma0Legs

variable (M M' d : ℕ)

theorem exists_eq0 (hMM' : M ∣ M') (hdd : d ∣ M' / M) : ∃ e : ℕ, M' = M * (d * e) := by
  obtain ⟨e, he⟩ := hdd
  refine ⟨e, ?_⟩
  rw [← he, Nat.mul_div_cancel' hMM']

theorem dvd_entry0 (hMM' : M ∣ M') (hdd : d ∣ M' / M) (γ : ↥(Gamma0 M')) :
    (d : ℤ) ∣ (γ : SL(2, ℤ)) 1 0 := by
  have hM' : ((M' : ℕ) : ℤ) ∣ (γ : SL(2, ℤ)) 1 0 :=
    (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp (Gamma0_mem.mp γ.2)
  obtain ⟨e, he⟩ := exists_eq0 M M' d hMM' hdd
  refine dvd_trans ?_ hM'
  rw [he]
  push_cast
  exact Dvd.intro_left ((M : ℤ) * e) (by ring)

theorem conjLowerMat_mem0 [NeZero d] (hMM' : M ∣ M') (hdd : d ∣ M' / M) (γ : ↥(Gamma0 M')) :
    conjLowerMat d (γ : SL(2, ℤ)) (dvd_entry0 M M' d hMM' hdd γ) ∈ Gamma0 M := by
  have hM' : ((M' : ℕ) : ℤ) ∣ (γ : SL(2, ℤ)) 1 0 :=
    (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp (Gamma0_mem.mp γ.2)
  obtain ⟨e, he⟩ := exists_eq0 M M' d hMM' hdd
  obtain ⟨t, ht⟩ := hM'
  have hd0 : (d : ℤ) ≠ 0 := by exact_mod_cast NeZero.ne d
  have hquot : (γ : SL(2, ℤ)) 1 0 / (d : ℤ) = (M : ℤ) * (e * t) := by
    apply Int.ediv_eq_of_eq_mul_right hd0
    rw [ht, he]
    push_cast
    ring
  rw [Gamma0_mem]
  show (((!![(γ : SL(2, ℤ)) 0 0, (γ : SL(2, ℤ)) 0 1 * d; (γ : SL(2, ℤ)) 1 0 / d, (γ : SL(2, ℤ)) 1 1]
    : Matrix (Fin 2) (Fin 2) ℤ) 1 0 : ℤ) : ZMod M) = 0
  simp only [Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_fin_one]
  rw [hquot]
  push_cast
  rw [ZMod.natCast_self, zero_mul]

def iotaDeg0 [NeZero d] (hMM' : M ∣ M') (hdd : d ∣ M' / M) : ↥(Gamma0 M') →* ↥(Gamma0 M) where
  toFun γ := ⟨conjLowerMat d (γ : SL(2, ℤ)) (dvd_entry0 M M' d hMM' hdd γ),
    conjLowerMat_mem0 M M' d hMM' hdd γ⟩
  map_one' := by
    apply Subtype.ext
    apply Matrix.SpecialLinearGroup.ext
    intro i j
    fin_cases i <;> fin_cases j <;> simp [conjLowerMat]
  map_mul' γ δ :=
    Subtype.ext (conjLowerMat_mul d (γ : SL(2, ℤ)) (δ : SL(2, ℤ)) (dvd_entry0 M M' d hMM' hdd γ)
      (dvd_entry0 M M' d hMM' hdd δ) (dvd_entry0 M M' d hMM' hdd (γ * δ)))

def iDeg0 (R : Type*) [Semiring R] (A : Type*) [AddCommGroup A] [Module R A] [NeZero d]
    (hMM' : M ∣ M') (hdd : d ∣ M' / M) :
    (Additive ↥(Gamma0 M) →+ A) →ₗ[R] (Additive ↥(Gamma0 M') →+ A) where
  toFun φ := φ.comp (MonoidHom.toAdditive (iotaDeg0 M M' d hMM' hdd))
  map_add' := by intro φ ψ; ext; rfl
  map_smul' := by intro r φ; ext; rfl

theorem Gamma_subgroupOf_le_range_iotaDeg0 [NeZero M'] [NeZero d]
    (hMM' : M ∣ M') (hdd : d ∣ M' / M) :
    (Gamma (M' * d)).subgroupOf (Gamma0 M) ≤ (iotaDeg0 M M' d hMM' hdd).range := by
  intro γ hγ
  rw [Subgroup.mem_subgroupOf, Gamma_mem] at hγ
  obtain ⟨_, h01, h10, _⟩ := hγ
  have hMd : ((M' * d : ℕ) : ℤ) ∣ (γ : SL(2, ℤ)) 0 1 :=
    (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp h01
  have hMd' : ((M' * d : ℕ) : ℤ) ∣ (γ : SL(2, ℤ)) 1 0 :=
    (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp h10
  have hb : (d : ℤ) ∣ (γ : SL(2, ℤ)) 0 1 := dvd_trans (by push_cast; exact Dvd.intro_left _ rfl) hMd
  set A : SL(2, ℤ) := conjUpperMat d (γ : SL(2, ℤ)) hb with hAdef
  have hA0 : A ∈ Gamma0 M' := by
    rw [Gamma0_mem]
    have : A 1 0 = (γ : SL(2, ℤ)) 1 0 * d := by simp [hAdef, conjUpperMat]
    rw [this, ZMod.intCast_zmod_eq_zero_iff_dvd]
    exact Dvd.dvd.mul_right (dvd_trans (by push_cast; exact Dvd.intro _ rfl) hMd') _
  have hc : (d : ℤ) ∣ (conjUpperMat d (γ : SL(2, ℤ)) hb) 1 0 := by
    rw [conjUpperMat_apply_10]
    exact dvd_mul_left _ _
  refine ⟨⟨A, hA0⟩, Subtype.ext ?_⟩
  exact conjLowerMat_conjUpperMat d (γ : SL(2, ℤ)) hb hc

instance iotaDeg0_range_finiteIndex [NeZero M'] [NeZero d] (hMM' : M ∣ M') (hdd : d ∣ M' / M) :
    ((iotaDeg0 M M' d hMM' hdd).range).FiniteIndex := by
  haveI : NeZero (M' * d) := ⟨mul_ne_zero (NeZero.ne M') (NeZero.ne d)⟩
  haveI : ((Gamma (M' * d)).subgroupOf (Gamma0 M)).FiniteIndex := inferInstance
  exact Subgroup.finiteIndex_of_le (Gamma_subgroupOf_le_range_iotaDeg0 M M' d hMM' hdd)

theorem iotaDeg0_injective [NeZero d] (hMM' : M ∣ M') (hdd : d ∣ M' / M) :
    Function.Injective (iotaDeg0 M M' d hMM' hdd) := by
  intro γ δ hγδ
  have hmat : conjLowerMat d (γ : SL(2, ℤ)) (dvd_entry0 M M' d hMM' hdd γ) =
      conjLowerMat d (δ : SL(2, ℤ)) (dvd_entry0 M M' d hMM' hdd δ) := congrArg Subtype.val hγδ
  have e : ∀ i j, (conjLowerMat d (γ : SL(2, ℤ)) (dvd_entry0 M M' d hMM' hdd γ)) i j =
      (conjLowerMat d (δ : SL(2, ℤ)) (dvd_entry0 M M' d hMM' hdd δ)) i j := fun i j => by rw [hmat]
  have hd : (d : ℤ) ≠ 0 := by exact_mod_cast (NeZero.ne d)
  apply Subtype.ext
  apply Matrix.SpecialLinearGroup.ext
  intro i j
  fin_cases i <;> fin_cases j
  · simpa [conjLowerMat] using e 0 0
  · have h01 := e 0 1
    simp only [conjLowerMat, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.cons_val_fin_one] at h01
    exact mul_right_cancel₀ hd h01
  · have h10 := e 1 0
    simp only [conjLowerMat, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.cons_val_fin_one] at h10
    calc (γ : SL(2, ℤ)) 1 0
        = d * ((γ : SL(2, ℤ)) 1 0 / d) := (Int.mul_ediv_cancel' (dvd_entry0 M M' d hMM' hdd γ)).symm
      _ = d * ((δ : SL(2, ℤ)) 1 0 / d) := by rw [h10]
      _ = (δ : SL(2, ℤ)) 1 0 := Int.mul_ediv_cancel' (dvd_entry0 M M' d hMM' hdd δ)
  · simpa [conjLowerMat] using e 1 1

noncomputable def pushChar0 (A : Type*) [AddCommGroup A] [NeZero d]
    (hMM' : M ∣ M') (hdd : d ∣ M' / M) (φ : Additive ↥(Gamma0 M') →+ A) :
    Additive ↥((iotaDeg0 M M' d hMM' hdd).range) →+ A :=
  φ.comp (MonoidHom.toAdditive
    ((iotaDeg0 M M' d hMM' hdd).ofInjective (iotaDeg0_injective M M' d hMM' hdd)).symm.toMonoidHom)

noncomputable def jDeg0 (R : Type*) [Semiring R] (A : Type*) [AddCommGroup A] [Module R A]
    [NeZero M'] [NeZero d] (hMM' : M ∣ M') (hdd : d ∣ M' / M) :
    (Additive ↥(Gamma0 M') →+ A) →ₗ[R] (Additive ↥(Gamma0 M) →+ A) where
  toFun φ := coresAdd _ (pushChar0 M M' d A hMM' hdd φ)
  map_add' φ ψ := by
    have : pushChar0 M M' d A hMM' hdd (φ + ψ)
        = pushChar0 M M' d A hMM' hdd φ + pushChar0 M M' d A hMM' hdd ψ := by
      ext; rfl
    rw [this, coresAdd_add]
  map_smul' r φ := by
    have : pushChar0 M M' d A hMM' hdd (r • φ) = r • pushChar0 M M' d A hMM' hdd φ := by ext; rfl
    rw [this, coresAdd_smul]
    rfl

end Gamma0Legs

section Gamma0Hecke

variable (M : ℕ)

def Gamma0Upper (ℓ : ℕ) : Subgroup SL(2, ℤ) where
  carrier := { g | (g 0 1 : ZMod ℓ) = 0 }
  one_mem' := by simp
  mul_mem' := by
    intro a b ha hb
    simp only [Set.mem_setOf_eq] at *
    have h := (Matrix.two_mul_expl a.1 b.1).2.1
    simp only [coe_mul] at *
    rw [h]
    simp [ha, hb]
  inv_mem' := by
    intro a ha
    simp only [Set.mem_setOf_eq] at *
    rw [SL2_inv_expl a]
    simp only [cons_val_zero, cons_val_one, Int.cast_neg, neg_eq_zero] at *
    exact ha

@[simp]
theorem mem_Gamma0Upper {ℓ : ℕ} {A : SL(2, ℤ)} : A ∈ Gamma0Upper ℓ ↔ (A 0 1 : ZMod ℓ) = 0 :=
  Iff.rfl

theorem Gamma0Upper_isCongruenceSubgroup (ℓ : ℕ) [NeZero ℓ] :
    IsCongruenceSubgroup (Gamma0Upper ℓ) := by
  refine ⟨ℓ, NeZero.ne _, fun A hA => ?_⟩
  rw [mem_Gamma0Upper]
  exact (Gamma_mem.mp hA).2.1

instance Gamma0Upper_finiteIndex (ℓ : ℕ) [NeZero ℓ] : (Gamma0Upper ℓ).FiniteIndex :=
  (Gamma0Upper_isCongruenceSubgroup ℓ).finiteIndex

variable (ℓ : ℕ)

abbrev Gamma0HUpper : Subgroup ↥(Gamma0 M) := (Gamma0Upper ℓ).subgroupOf (Gamma0 M)

theorem dvd_of_mem_Gamma0HUpper (γ : ↥(Gamma0HUpper M ℓ)) :
    (ℓ : ℤ) ∣ (γ : SL(2, ℤ)) 0 1 := by
  have h : ((γ : ↥(Gamma0 M)) : SL(2, ℤ)) ∈ Gamma0Upper ℓ := Subgroup.mem_subgroupOf.mp γ.2
  rw [mem_Gamma0Upper] at h
  exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp h

theorem conjUpperMat_mem0 (γ : ↥(Gamma0HUpper M ℓ)) :
    conjUpperMat ℓ (γ : SL(2, ℤ)) (dvd_of_mem_Gamma0HUpper M ℓ γ) ∈ Gamma0 M := by
  rw [Gamma0_mem, conjUpperMat_apply_10, Int.cast_mul,
    Gamma0_mem.mp (γ : ↥(Gamma0 M)).2, zero_mul]

def conjL0 : ↥(Gamma0HUpper M ℓ) →* ↥(Gamma0 M) where
  toFun γ := ⟨conjUpperMat ℓ (γ : SL(2, ℤ)) (dvd_of_mem_Gamma0HUpper M ℓ γ),
    conjUpperMat_mem0 M ℓ γ⟩
  map_one' := by
    apply Subtype.ext
    apply Matrix.SpecialLinearGroup.ext
    intro i j
    fin_cases i <;> fin_cases j <;> simp [conjUpperMat]
  map_mul' γ δ :=
    Subtype.ext (conjUpperMat_mul ℓ (γ : SL(2, ℤ)) (δ : SL(2, ℤ))
      (dvd_of_mem_Gamma0HUpper M ℓ γ) (dvd_of_mem_Gamma0HUpper M ℓ δ)
      (dvd_of_mem_Gamma0HUpper M ℓ (γ * δ)))

variable (A : Type*) [AddCommGroup A]

noncomputable def heckeT0 [NeZero ℓ] :
    (Additive ↥(Gamma0 M) →+ A) →+ (Additive ↥(Gamma0 M) →+ A) where
  toFun φ :=
    MonoidHom.toAdditiveLeft
      (MonoidHom.transfer ((AddMonoidHom.toMultiplicativeRight φ).comp (conjL0 M ℓ)))
  map_zero' := by
    simp only [toMultiplicativeRight_zero, MonoidHom.one_comp,
      transfer_one, toAdditiveLeft_one]
  map_add' φ ψ := by
    simp only [toMultiplicativeRight_add, MonoidHom.mul_comp,
      transfer_mul, toAdditiveLeft_mul]

theorem heckeT0_apply [NeZero ℓ] (φ : Additive ↥(Gamma0 M) →+ A) :
    heckeT0 M ℓ A φ =
      MonoidHom.toAdditiveLeft
        (MonoidHom.transfer ((AddMonoidHom.toMultiplicativeRight φ).comp (conjL0 M ℓ))) :=
  rfl

end Gamma0Hecke

section Prim
variable {Φ : Type*} [Group Φ] {R : Type*} [CommRing R]

def omega (φ ψ : Additive Φ →+ R) (g g' : Φ) : R :=
  φ (Additive.ofMul g) * ψ (Additive.ofMul g') - ψ (Additive.ofMul g) * φ (Additive.ofMul g')

theorem omega_one_left (φ ψ : Additive Φ →+ R) (g : Φ) : omega φ ψ 1 g = 0 := by
  simp [omega]

theorem omega_one_right (φ ψ : Additive Φ →+ R) (g : Φ) : omega φ ψ g 1 = 0 := by
  simp [omega]

theorem omega_inv_self (φ ψ : Additive Φ →+ R) (g : Φ) : omega φ ψ g⁻¹ g = 0 := by
  simp only [omega, ofMul_inv, map_neg]
  ring

theorem omega_self_inv (φ ψ : Additive Φ →+ R) (g : Φ) : omega φ ψ g g⁻¹ = 0 := by
  simp only [omega, ofMul_inv, map_neg]
  ring

theorem omega_cocycle (φ ψ : Additive Φ →+ R) (g h k : Φ) :
    omega φ ψ g h + omega φ ψ (g * h) k = omega φ ψ h k + omega φ ψ g (h * k) := by
  simp only [omega, ofMul_mul, map_add]
  ring

theorem omega_swap (φ ψ : Additive Φ →+ R) (g h : Φ) : omega ψ φ g h = - omega φ ψ g h := by
  simp only [omega]
  ring

def CentralExt (_φ _ψ : Additive Φ →+ R) : Type _ := R × Φ

namespace CentralExt

variable (φ ψ : Additive Φ →+ R)

instance : Mul (CentralExt φ ψ) := ⟨fun x y => (x.1 + y.1 - omega φ ψ x.2 y.2, x.2 * y.2)⟩
instance : One (CentralExt φ ψ) := ⟨((0 : R), (1 : Φ))⟩
instance : Inv (CentralExt φ ψ) := ⟨fun x => (-x.1, x.2⁻¹)⟩

theorem mul_def (x y : CentralExt φ ψ) :
    x * y = (x.1 + y.1 - omega φ ψ x.2 y.2, x.2 * y.2) := rfl

theorem one_def : (1 : CentralExt φ ψ) = ((0 : R), (1 : Φ)) := rfl

theorem inv_def (x : CentralExt φ ψ) : x⁻¹ = (-x.1, x.2⁻¹) := rfl

instance : Group (CentralExt φ ψ) where
  mul_assoc x y z := by
    change ((x.1 + y.1 - omega φ ψ x.2 y.2) + z.1 - omega φ ψ (x.2 * y.2) z.2, (x.2 * y.2) * z.2) =
      (x.1 + (y.1 + z.1 - omega φ ψ y.2 z.2) - omega φ ψ x.2 (y.2 * z.2), x.2 * (y.2 * z.2))
    have hc := omega_cocycle φ ψ x.2 y.2 z.2
    refine Prod.ext ?_ (mul_assoc _ _ _)
    change (x.1 + y.1 - omega φ ψ x.2 y.2) + z.1 - omega φ ψ (x.2 * y.2) z.2 =
      x.1 + (y.1 + z.1 - omega φ ψ y.2 z.2) - omega φ ψ x.2 (y.2 * z.2)
    linear_combination (-1 : R) * hc
  one_mul x := by
    change ((0 : R) + x.1 - omega φ ψ 1 x.2, (1 : Φ) * x.2) = x
    rw [omega_one_left, sub_zero, zero_add, one_mul]
    exact Prod.mk.eta
  mul_one x := by
    change (x.1 + 0 - omega φ ψ x.2 1, x.2 * 1) = x
    rw [omega_one_right, sub_zero, add_zero, mul_one]
    exact Prod.mk.eta
  inv_mul_cancel x := by
    change (-x.1 + x.1 - omega φ ψ x.2⁻¹ x.2, x.2⁻¹ * x.2) = ((0 : R), (1 : Φ))
    rw [omega_inv_self, sub_zero, neg_add_cancel, inv_mul_cancel]

def snd : CentralExt φ ψ →* Φ where
  toFun x := x.2
  map_one' := rfl
  map_mul' _ _ := rfl

@[simp] theorem snd_apply (x : CentralExt φ ψ) : snd φ ψ x = x.2 := rfl

end CentralExt

variable [IsFreeGroup Φ]

noncomputable def sect (φ ψ : Additive Φ →+ R) : Φ →* CentralExt φ ψ :=
  IsFreeGroup.lift (fun a => (((0 : R), IsFreeGroup.of a) : CentralExt φ ψ))

theorem snd_comp_sect (φ ψ : Additive Φ →+ R) :
    (CentralExt.snd φ ψ).comp (sect φ ψ) = MonoidHom.id Φ := by
  apply IsFreeGroup.ext_hom
  intro a
  simp [sect]

@[simp] theorem sect_snd (φ ψ : Additive Φ →+ R) (g : Φ) : (sect φ ψ g).2 = g := by
  have h := congrArg (fun f : Φ →* Φ => f g) (snd_comp_sect φ ψ)
  simpa using h

noncomputable def hPrim (φ ψ : Additive Φ →+ R) (g : Φ) : R := (sect φ ψ g).1

theorem hPrim_mul (φ ψ : Additive Φ →+ R) (g g' : Φ) :
    hPrim φ ψ (g * g') = hPrim φ ψ g + hPrim φ ψ g' - omega φ ψ g g' := by
  have h := map_mul (sect φ ψ) g g'
  have h1 := congrArg Prod.fst h
  simp only [CentralExt.mul_def, sect_snd] at h1
  exact h1

theorem hPrim_one (φ ψ : Additive Φ →+ R) : hPrim φ ψ 1 = 0 := by
  have h := map_one (sect φ ψ)
  exact congrArg Prod.fst h

def CentralExt.lift (φ ψ : Additive Φ →+ R) (H : Φ → R)
    (hH : ∀ g g', H (g * g') = H g + H g' - omega φ ψ g g') : Φ →* CentralExt φ ψ where
  toFun g := (H g, g)
  map_one' := by
    have h := hH 1 1
    rw [one_mul, omega_one_left, sub_zero] at h
    have h1 : H 1 = 0 := by linear_combination -h
    rw [h1]
    rfl
  map_mul' g g' := by
    rw [CentralExt.mul_def]
    exact Prod.ext (hH g g') rfl

omit [IsFreeGroup Φ] in
@[simp] theorem CentralExt.lift_apply (φ ψ : Additive Φ →+ R) (H : Φ → R)
    (hH : ∀ g g', H (g * g') = H g + H g' - omega φ ψ g g') (g : Φ) :
    CentralExt.lift φ ψ H hH g = (H g, g) := rfl

theorem hPrim_unique (φ ψ : Additive Φ →+ R) (H : Φ → R)
    (hH : ∀ g g', H (g * g') = H g + H g' - omega φ ψ g g')
    (h0 : ∀ a : IsFreeGroup.Generators Φ, H (IsFreeGroup.of a) = 0) (g : Φ) : H g = hPrim φ ψ g := by
  have key : CentralExt.lift φ ψ H hH = sect φ ψ := by
    apply IsFreeGroup.ext_hom
    intro a
    rw [CentralExt.lift_apply, h0 a]
    simp [sect]
  exact congrArg Prod.fst (congrArg (fun f : Φ →* CentralExt φ ψ => f g) key)

theorem hPrim_of (φ ψ : Additive Φ →+ R) (a : IsFreeGroup.Generators Φ) : hPrim φ ψ (IsFreeGroup.of a) = 0 := by
  simp [hPrim, sect]

omit [IsFreeGroup Φ] in
theorem omega_add_left (φ₁ φ₂ ψ : Additive Φ →+ R) (g g' : Φ) :
    omega (φ₁ + φ₂) ψ g g' = omega φ₁ ψ g g' + omega φ₂ ψ g g' := by
  simp only [omega, AddMonoidHom.add_apply]
  ring

omit [IsFreeGroup Φ] in
theorem omega_smul_left (r : R) (φ ψ : Additive Φ →+ R) (g g' : Φ) :
    omega (r • φ) ψ g g' = r * omega φ ψ g g' := by
  simp only [omega, AddMonoidHom.smul_apply, smul_eq_mul]
  ring

theorem hPrim_add_left (φ₁ φ₂ ψ : Additive Φ →+ R) (g : Φ) :
    hPrim (φ₁ + φ₂) ψ g = hPrim φ₁ ψ g + hPrim φ₂ ψ g := by
  symm
  refine hPrim_unique (φ₁ + φ₂) ψ (fun g => hPrim φ₁ ψ g + hPrim φ₂ ψ g) ?_ ?_ g
  · intro g g'
    rw [hPrim_mul, hPrim_mul, omega_add_left]
    ring
  · intro a
    rw [hPrim_of, hPrim_of, add_zero]

theorem hPrim_smul_left (r : R) (φ ψ : Additive Φ →+ R) (g : Φ) :
    hPrim (r • φ) ψ g = r * hPrim φ ψ g := by
  symm
  refine hPrim_unique (r • φ) ψ (fun g => r * hPrim φ ψ g) ?_ ?_ g
  · intro g g'
    rw [hPrim_mul, omega_smul_left]
    ring
  · intro a
    rw [hPrim_of, mul_zero]

theorem hPrim_swap (φ ψ : Additive Φ →+ R) (g : Φ) : hPrim ψ φ g = - hPrim φ ψ g := by
  refine (hPrim_unique ψ φ (fun g => - hPrim φ ψ g) ?_ ?_ g).symm
  · intro g g'
    rw [hPrim_mul, omega_swap]
    ring
  · intro a
    rw [hPrim_of, neg_zero]

end Prim

section Cusps

open MulAction

variable (Φ : Subgroup SL(2, ℤ)) [Φ.FiniteIndex] {R : Type*} [CommRing R]

abbrev Cusp : Type := Quotient (orbitRel (Subgroup.zpowers ModularGroup.T) (SL(2, ℤ) ⧸ Φ))

noncomputable instance : Fintype (Cusp Φ) := Fintype.ofFinite _

noncomputable def cuspGen (q : Cusp Φ) : Φ :=
  ⟨q.out.out⁻¹ * ModularGroup.T ^ Function.minimalPeriod (ModularGroup.T • ·) q.out * q.out.out,
    QuotientGroup.out_conj_pow_minimalPeriod_mem Φ ModularGroup.T q.out⟩

noncomputable def cuspSum (f : Φ → R) : R := ∑ q : Cusp Φ, f (cuspGen Φ q)

theorem cuspSum_add (f g : Φ → R) : cuspSum Φ (f + g) = cuspSum Φ f + cuspSum Φ g := by
  simp [cuspSum, Finset.sum_add_distrib]

theorem cuspSum_smul (r : R) (f : Φ → R) : cuspSum Φ (r • f) = r * cuspSum Φ f := by
  simp [cuspSum, Finset.mul_sum]

noncomputable def pairF [IsFreeGroup Φ] [Invertible (2 : R)] (φ ψ : Additive Φ →+ R) : R :=
  ⅟(2 : R) * cuspSum Φ (hPrim φ ψ)

end Cusps

section Descent

variable (Λ : Subgroup SL(2, ℤ)) [Λ.FiniteIndex] [IsFreeGroup Λ]
variable (Γ : Subgroup SL(2, ℤ)) [Γ.FiniteIndex] {R : Type*} [CommRing R]

instance isFreeGroup_inf : IsFreeGroup ↥(Γ ⊓ Λ) :=
  IsFreeGroup.ofMulEquiv (Subgroup.subgroupOfEquivOfLe (inf_le_right : Γ ⊓ Λ ≤ Λ))

example : (Γ ⊓ Λ).FiniteIndex := inferInstance

def resInf (φ : Additive Γ →+ R) : Additive ↥(Γ ⊓ Λ) →+ R :=
  φ.comp (MonoidHom.toAdditive (Subgroup.inclusion (inf_le_left : Γ ⊓ Λ ≤ Γ)))

noncomputable def pairD [Invertible (2 : R)] [Invertible (((Γ ⊓ Λ).relIndex Γ : ℕ) : R)]
    (φ ψ : Additive Γ →+ R) : R :=
  ⅟(((Γ ⊓ Λ).relIndex Γ : ℕ) : R) * pairF (Γ ⊓ Λ) (resInf Λ Γ φ) (resInf Λ Γ ψ)

end Descent

section LevelZ

open ModularCurve.Period

variable (N : ℕ) [NeZero N] [IsFreeGroup ↥(Gamma 4)]

noncomputable def pairZFun (φ ψ : Additive ↥(Gamma0 N) →+ ℤ) : ℤ :=
  ((48 / (Gamma0 N ⊓ Gamma 4).relIndex (Gamma0 N) : ℕ) : ℤ) *
    cuspSum (Gamma0 N ⊓ Gamma 4) (hPrim (resInf (Gamma 4) (Gamma0 N) φ) (resInf (Gamma 4) (Gamma0 N) ψ))

theorem pairZFun_add_left (φ₁ φ₂ ψ : Additive ↥(Gamma0 N) →+ ℤ) :
    pairZFun N (φ₁ + φ₂) ψ = pairZFun N φ₁ ψ + pairZFun N φ₂ ψ := by
  have h : hPrim (resInf (Gamma 4) (Gamma0 N) (φ₁ + φ₂)) (resInf (Gamma 4) (Gamma0 N) ψ) =
      hPrim (resInf (Gamma 4) (Gamma0 N) φ₁) (resInf (Gamma 4) (Gamma0 N) ψ) +
        hPrim (resInf (Gamma 4) (Gamma0 N) φ₂) (resInf (Gamma 4) (Gamma0 N) ψ) := by
    funext g
    rw [Pi.add_apply, ← hPrim_add_left]
    rfl
  rw [pairZFun, pairZFun, pairZFun, h, cuspSum_add, mul_add]

theorem pairZFun_smul_left (r : ℤ) (φ ψ : Additive ↥(Gamma0 N) →+ ℤ) :
    pairZFun N (r • φ) ψ = r * pairZFun N φ ψ := by
  have h : hPrim (resInf (Gamma 4) (Gamma0 N) (r • φ)) (resInf (Gamma 4) (Gamma0 N) ψ) =
      r • hPrim (resInf (Gamma 4) (Gamma0 N) φ) (resInf (Gamma 4) (Gamma0 N) ψ) := by
    funext g
    rw [Pi.smul_apply, smul_eq_mul, ← hPrim_smul_left]
    rfl
  rw [pairZFun, pairZFun, h, cuspSum_smul]
  ring

theorem pairZFun_swap (φ ψ : Additive ↥(Gamma0 N) →+ ℤ) : pairZFun N ψ φ = - pairZFun N φ ψ := by
  have h : hPrim (resInf (Gamma 4) (Gamma0 N) ψ) (resInf (Gamma 4) (Gamma0 N) φ) =
      (-1 : ℤ) • hPrim (resInf (Gamma 4) (Gamma0 N) φ) (resInf (Gamma 4) (Gamma0 N) ψ) := by
    funext g
    rw [Pi.smul_apply, smul_eq_mul, hPrim_swap]
    ring
  rw [pairZFun, pairZFun, h, cuspSum_smul]
  ring

theorem pairZFun_add_right (φ ψ₁ ψ₂ : Additive ↥(Gamma0 N) →+ ℤ) :
    pairZFun N φ (ψ₁ + ψ₂) = pairZFun N φ ψ₁ + pairZFun N φ ψ₂ := by
  rw [pairZFun_swap, pairZFun_add_left, neg_add, ← pairZFun_swap, ← pairZFun_swap]

theorem pairZFun_smul_right (r : ℤ) (φ ψ : Additive ↥(Gamma0 N) →+ ℤ) :
    pairZFun N φ (r • ψ) = r * pairZFun N φ ψ := by
  rw [pairZFun_swap, pairZFun_smul_left, pairZFun_swap]
  ring

noncomputable def pairZ :
    parabolicHoms ℤ (Gamma0 N) ℤ →ₗ[ℤ] parabolicHoms ℤ (Gamma0 N) ℤ →ₗ[ℤ] ℤ :=
  LinearMap.mk₂ ℤ (fun x y => pairZFun N (x : Additive ↥(Gamma0 N) →+ ℤ) (y : Additive ↥(Gamma0 N) →+ ℤ))
    (fun x₁ x₂ y => by
      rw [Submodule.coe_add, pairZFun_add_left])
    (fun r x y => by
      rw [Submodule.coe_smul, pairZFun_smul_left, smul_eq_mul])
    (fun x y₁ y₂ => by
      rw [Submodule.coe_add, pairZFun_add_right])
    (fun r x y => by
      rw [Submodule.coe_smul, pairZFun_smul_right, smul_eq_mul])

@[simp] theorem pairZ_apply (x y : parabolicHoms ℤ (Gamma0 N) ℤ) :
    pairZ N x y = pairZFun N (x : Additive ↥(Gamma0 N) →+ ℤ) (y : Additive ↥(Gamma0 N) →+ ℤ) := rfl

end LevelZ

end ModularCurve.PDPairing


