-- Prove2me | Definitions.Def_OddOrder_GroupTheory_RepresentationTheory_ClassSumAlgebra
-- name    : OddOrder_GroupTheory_RepresentationTheory_ClassSumAlgebra
-- status  : Definition
-- author  : @burkh4rt
-- created : 2026-11-12T04:51:58.322202+00:00
-- url     : https://prove2.me/theorems/4b4ce430-1f67-437a-a689-e065efb7cfa7
-- title:
--   Peterfalvi (6.7.3) and class-sum orthogonality (tail of the class-sum algebra)
-- statement:
--   The tail of the class-sum algebra development: the steps of Peterfalvi (6.7.3), namely combining the two (6.7.2) instances, dividing by $|C_1|$ and the final step, assembled into $\psi(z)\equiv\psi(1)\pmod{|P|}$. It also regroups class-function sums by conjugacy class, proves first orthogonality in class-sum form, and proves $\chi_\rho(1)\mid|G|$ (Isaacs, *Character Theory of Finite Groups*, Thm 3.11).
--
--   The bundle consists of lemmas only.
--
--   The bundle also proves 2 supporting lemmas used by later statements.
-- source:
--   Yawara Ishida, Lean 4 formalization of the Feit–Thompson (odd order) theorem, github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0), https://github.com/yawara/odd-order/blob/20a6fccbb63c0b138acda9f7fafd798c42f9441b/OddOrder/GroupTheory/RepresentationTheory/ClassSumAlgebra.lean

/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
-- From github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0; LICENSE at that commit):
--   OddOrder/GroupTheory/RepresentationTheory/ClassSumAlgebra.lean
-- Generated for Prove2Me by deleting declarations; the remaining commands are verbatim except:
-- `private` dropped where another file uses the declaration, and a solution's main theorem
-- renamed `_root_.solution` (platform convention).
import Definitions.Def_OddOrder_GroupTheory_RepresentationTheory_ClassSumCongruence

namespace OddOrder.RepresentationTheory

open scoped MonoidAlgebra

open OddOrder.GroupTheory.CenterClassSum

open Module (finrank)

open Representation

variable {G : Type*} [Group G]

section ClassCongruence

open OddOrder.AlgInt

variable {V : Type*} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]

variable [Fintype G] [DecidableEq G] [DecidableEq (ConjClasses G)] [Fintype (ConjClasses G)]

/-- Shorthand for the central-character value `ω_ρ(C_s)` on a class sum (re-declared after the
prefix-split: `local notation` does not cross file boundaries). -/
local notation3 "ω" ρ:max C:max => centralCharacterOfRep ρ ⟨classSum C, classSum_mem_center C⟩

omit [Fintype G] [DecidableEq G] [DecidableEq (ConjClasses G)] [Fintype (ConjClasses G)] in
/-- **Peterfalvi (6.7.3)**, combination of the two (6.7.2) instances.  After (6.7.2) at `(1,1)`
(where `a_{110} = 0`) and `(1,2)` (where `a_{120} = |C₁|`), transitivity of the congruence yields
`ψ(1)·a_{11}·α ≡ ψ(1)·(|C₁| + a_{12}·α) (mod n)` from the two statements
`ψ(1)·α² ≡ ψ(1)·a_{11}·α` and `ψ(1)·α² ≡ ψ(1)·(|C₁| + a_{12}·α)`. -/
theorem peterfalvi_673_combine {n : ℤ} {ψ1 α q a₁₁ a₁₂ : ℂ}
    (h11 : ψ1 * α ^ 2 ≡ ψ1 * (a₁₁ * α) [ALGMOD n])
    (h12 : ψ1 * α ^ 2 ≡ ψ1 * (q + a₁₂ * α) [ALGMOD n]) :
    ψ1 * (a₁₁ * α) ≡ ψ1 * (q + a₁₂ * α) [ALGMOD n] :=
  h11.symm.trans h12

omit [Fintype G] [DecidableEq G] [DecidableEq (ConjClasses G)] [Fintype (ConjClasses G)] in
/-- **Peterfalvi (6.7.3)**, the "divide by `|C₁|`" step.  Substituting `ψ(1)·α = |C₁|·ψ(z)` into the
combined congruence `ψ(1)·a_{11}·α ≡ ψ(1)·(|C₁| + a_{12}·α)` gives a congruence with a common factor
`|C₁| = q`; since `q` is coprime to the modulus `n` (Peterfalvi: `|C₁|` prime to `p`, `n = |P|`) and
the endpoints `ψ(z)`, `ψ(1)` are algebraic integers, that factor cancels, yielding
`a_{11}·ψ(z) ≡ ψ(1) + a_{12}·ψ(z) (mod n)`. -/
theorem peterfalvi_673_cancel {n : ℤ} {ψ1 ψz α a₁₁ a₁₂ : ℂ} {q : ℤ}
    (hcop : IsCoprime q n) (hψz : IsIntegral ℤ ψz) (hψ1 : IsIntegral ℤ ψ1)
    (ha₁₁ : IsIntegral ℤ a₁₁) (ha₁₂ : IsIntegral ℤ a₁₂)
    (hsubst : ψ1 * α = (q : ℂ) * ψz)
    (hcomb : ψ1 * (a₁₁ * α) ≡ ψ1 * ((q : ℂ) + a₁₂ * α) [ALGMOD n]) :
    a₁₁ * ψz ≡ ψ1 + a₁₂ * ψz [ALGMOD n] := by
  -- Rewrite both sides of `hcomb` as `q · (…)` using `ψ1·α = q·ψz`.
  have hL : ψ1 * (a₁₁ * α) = (q : ℂ) * (a₁₁ * ψz) := by
    rw [show ψ1 * (a₁₁ * α) = a₁₁ * (ψ1 * α) by ring, hsubst]; ring
  have hR : ψ1 * ((q : ℂ) + a₁₂ * α) = (q : ℂ) * (ψ1 + a₁₂ * ψz) := by
    rw [show ψ1 * ((q : ℂ) + a₁₂ * α) = (q : ℂ) * ψ1 + a₁₂ * (ψ1 * α) by ring, hsubst]; ring
  rw [hL, hR] at hcomb
  -- Cancel the coprime factor `q`; endpoints are integral (counts and character values are).
  exact Cong.intMul_cancel_left hcop (ha₁₁.mul hψz) (hψ1.add (ha₁₂.mul hψz)) hcomb

omit [Fintype G] [DecidableEq G] [DecidableEq (ConjClasses G)] [Fintype (ConjClasses G)] in
/-- **Peterfalvi (6.7.3)**, the final step.  Given the per-`ψ` congruence
`a_{11}·ψ(z) ≡ ψ(1) + a_{12}·ψ(z) (mod n)` and the `ψ = 1_G` specialization
`a_{11} ≡ 1 + a_{12} (mod n)`, multiplying the latter by the algebraic integer `ψ(z)` and combining
yields `ψ(z) ≡ ψ(1) (mod n)`. -/
theorem peterfalvi_673_final {n : ℤ} {ψ1 ψz a₁₁ a₁₂ : ℂ} (hψz : IsIntegral ℤ ψz)
    (hψ : a₁₁ * ψz ≡ ψ1 + a₁₂ * ψz [ALGMOD n])
    (hone : a₁₁ ≡ 1 + a₁₂ [ALGMOD n]) :
    ψz ≡ ψ1 [ALGMOD n] := by
  -- Multiply `a₁₁ ≡ 1 + a₁₂` by `ψ(z)`: `a₁₁·ψz ≡ (1 + a₁₂)·ψz = ψz + a₁₂·ψz`.
  have honeψ : a₁₁ * ψz ≡ ψz + a₁₂ * ψz [ALGMOD n] := by
    have := hone.smul_left hψz
    rwa [show ψz * (1 + a₁₂) = ψz + a₁₂ * ψz by ring, mul_comm ψz a₁₁] at this
  -- Combine with `hψ`: `ψz + a₁₂·ψz ≡ ψ1 + a₁₂·ψz`, then cancel the common `a₁₂·ψz`.
  have hcomb : ψz + a₁₂ * ψz ≡ ψ1 + a₁₂ * ψz [ALGMOD n] := honeψ.symm.trans hψ
  have := hcomb.sub (Cong.refl n (a₁₂ * ψz))
  simpa using this

omit [Fintype G] [DecidableEq G] [DecidableEq (ConjClasses G)] [Fintype (ConjClasses G)] in
/-- **Peterfalvi (6.7.3)** (`ψ(z) ≡ ψ(1) (mod |P|)`), assembled from its (6.7.2) inputs.  Given:

* the two (6.7.2) congruences `ψ(1)·α² ≡ ψ(1)·a_{11}·α` (instance `(1,1)`, where `a_{110} = 0`)
  and `ψ(1)·α² ≡ ψ(1)·(|C₁| + a_{12}·α)` (instance `(1,2)`, where `a_{120} = |C₁|`);
* the identity `ψ(1)·α = |C₁|·ψ(z)` (`α = ω(C₁)`, `z ∈ C₁ ∩ Z^#`);
* the `ψ = 1_G` specialization `a_{11} ≡ 1 + a_{12}` of the cancelled congruence;
* coprimality `IsCoprime |C₁| |P|` (Peterfalvi: `|C₁|` prime to `p`, `|P| = p^k`) and integrality of
  the character values `ψ(z)`, `ψ(1)` and the integer structure constants `a_{11}`, `a_{12}`,

one concludes `ψ(z) ≡ ψ(1) (mod |P|)`.  This is Peterfalvi's chain
combine ⟶ substitute-and-cancel-`|C₁|` ⟶ multiply the `1_G` congruence by `ψ(z)` and subtract. -/
theorem peterfalvi_673 {n : ℤ} {ψ1 ψz α a₁₁ a₁₂ : ℂ} {q : ℤ}
    (hcop : IsCoprime q n) (hψz : IsIntegral ℤ ψz) (hψ1 : IsIntegral ℤ ψ1)
    (ha₁₁ : IsIntegral ℤ a₁₁) (ha₁₂ : IsIntegral ℤ a₁₂)
    (h11 : ψ1 * α ^ 2 ≡ ψ1 * (a₁₁ * α) [ALGMOD n])
    (h12 : ψ1 * α ^ 2 ≡ ψ1 * ((q : ℂ) + a₁₂ * α) [ALGMOD n])
    (hsubst : ψ1 * α = (q : ℂ) * ψz)
    (hone : a₁₁ ≡ 1 + a₁₂ [ALGMOD n]) :
    ψz ≡ ψ1 [ALGMOD n] :=
  peterfalvi_673_final hψz
    (peterfalvi_673_cancel hcop hψz hψ1 ha₁₁ ha₁₂ hsubst (peterfalvi_673_combine h11 h12)) hone

/-- **Peterfalvi (6.7)**, wired to the final congruence.  In the (6.7) Sylow/TI setup, let
`C₁=⟦z⟧`, `C₂=⟦z⁻¹⟧`, and let `a₁₁`, `a₁₂` be the collapsed nonidentity `Z`-class coefficient sums
`nonidentityZClassCoeffSum Z C₁ C₁` and `nonidentityZClassCoeffSum Z C₁ C₂`.  If

* `z⁻¹` is not conjugate to `z` (`a_{110}=0`; the downstream TI/odd-order wrapper discharges this),
* `ψ` and `|N_G(P) ∩ C_G(-)|` are constant on `Z^#` (the `(iii)` central-character constancy atom),
* the trivial-character specialization gives `a₁₁ ≡ 1 + a₁₂ (mod |P|)`,

then `ψ(z) ≡ ψ(1) (mod |P|)`.

Everything else in (6.7.3) is discharged here: the two collapsed (6.7.2) congruences, the
`a_{120}=|C₁|` identity coefficient, `ψ(1)ω(C₁)=|C₁|ψ(z)`, algebraic integrality, and
`(|C₁|,|P|)=1`. -/
theorem peterfalvi_67 [Finite G] (ρ : Representation ℂ G V) [IsIrreducible ρ]
    {p : ℕ} [Fact p.Prime] (P : Sylow p G) {Z : Subgroup G}
    (hZP : Z ≤ (P : Subgroup G))
    (hZnormal : (Z.subgroupOf (Subgroup.normalizer (P : Subgroup G))).Normal)
    (hti : OddOrder.GroupTheory.IsTISubset ((P : Set G) \ {1})
      (Subgroup.normalizer (P : Subgroup G)))
    {z : G} (hzZ : z ∈ Z) (hz1 : z ≠ 1)
    (hPz : (P : Subgroup G) ≤ Subgroup.centralizer {z})
    (hreal : ConjClasses.mk z⁻¹ ≠ ConjClasses.mk z)
    (hconst : ∀ ⦃w : G⦄, w ∈ Z → w ≠ 1 →
      ρ.character w = ρ.character z ∧
        Nat.card ↥(Subgroup.normalizer (P : Subgroup G) ⊓ Subgroup.centralizer ({w} : Set G)) =
          Nat.card ↥(Subgroup.normalizer (P : Subgroup G) ⊓ Subgroup.centralizer ({z} : Set G)))
    (hone : nonidentityZClassCoeffSum Z (ConjClasses.mk z) (ConjClasses.mk z)
      ≡ 1 + nonidentityZClassCoeffSum Z (ConjClasses.mk z) (ConjClasses.mk z⁻¹)
        [ALGMOD (Nat.card (P : Subgroup G) : ℤ)]) :
    ρ.character z ≡ ρ.character 1 [ALGMOD (Nat.card (P : Subgroup G) : ℤ)] := by
  classical
  let C₁ : ConjClasses G := ConjClasses.mk z
  let C₂ : ConjClasses G := ConjClasses.mk z⁻¹
  let α : ℂ := ω ρ C₁
  let a₁₁ : ℂ := nonidentityZClassCoeffSum Z C₁ C₁
  let a₁₂ : ℂ := nonidentityZClassCoeffSum Z C₁ C₂
  let q : ℤ := Nat.card { x : G // ConjClasses.mk x = C₁ }
  have hzP : z ∈ (P : Subgroup G) := hZP hzZ
  have hzA : z ∈ (P : Set G) \ {1} := ⟨hzP, by simpa using hz1⟩
  have hωconst : ∀ ⦃w : G⦄, w ∈ Z → w ≠ 1 → ω ρ (ConjClasses.mk w) = α := by
    intro w hwZ hw1
    have hwP : w ∈ (P : Subgroup G) := hZP hwZ
    have hwA : w ∈ (P : Set G) \ {1} := ⟨hwP, by simpa using hw1⟩
    rcases hconst hwZ hw1 with ⟨hchar, hcard⟩
    exact centralCharacterOfRep_eq_of_tiSubset_card_eq_of_character_eq ρ hti hwA hzA hcard hchar
  have hC₁ : ∃ y : G, y ∈ Z ∧ y ≠ 1 ∧ ConjClasses.mk y = C₁ :=
    ⟨z, hzZ, hz1, rfl⟩
  have hC₂ : ∃ y : G, y ∈ Z ∧ y ≠ 1 ∧ ConjClasses.mk y = C₂ :=
    ⟨z⁻¹, Z.inv_mem hzZ, inv_ne_one.mpr hz1, rfl⟩
  have hcoeff11 : (classSum C₁ * classSum C₁ : ℂ[G]).coeff (1 : G) = 0 := by
    rw [classSum_mul_apply_one_eq_classSumCoeff_one]
    rw [show classSumCoeff C₁ C₁ 1 = 0 by simpa [C₁] using classSumCoeff_self_one_eq_zero z hreal]
    norm_num
  have hcoeff12 : (classSum C₁ * classSum C₂ : ℂ[G]).coeff (1 : G) = (q : ℂ) := by
    rw [classSum_mul_apply_one_eq_classSumCoeff_one]
    rw [show classSumCoeff C₁ C₂ 1 = Nat.card { x : G // ConjClasses.mk x = C₁ } by
      simpa [C₁, C₂] using classSumCoeff_self_inv_one_eq_card z]
    simp [q]
  have h11raw :=
    centralCharacterOfRep_classSum_mul_cong_collapse_of_isTISubset ρ P hZP hZnormal hti hC₁ hC₁
      (α := α) hωconst
  have h12raw :=
    centralCharacterOfRep_classSum_mul_cong_collapse_of_isTISubset ρ P hZP hZnormal hti hC₁ hC₂
      (α := α) hωconst
  have hωC₂ : ω ρ C₂ = α := by
    simpa [C₂] using hωconst (Z.inv_mem hzZ) (inv_ne_one.mpr hz1)
  have h11 : ρ.character 1 * α ^ 2 ≡ ρ.character 1 * (a₁₁ * α)
      [ALGMOD (Nat.card (P : Subgroup G) : ℤ)] := by
    simpa [C₁, α, a₁₁, pow_two, hcoeff11] using h11raw
  have h12 : ρ.character 1 * α ^ 2 ≡ ρ.character 1 * ((q : ℂ) + a₁₂ * α)
      [ALGMOD (Nat.card (P : Subgroup G) : ℤ)] := by
    simpa [C₁, C₂, α, a₁₂, q, pow_two, hcoeff12, hωC₂] using h12raw
  have hsubst : ρ.character 1 * α = (q : ℂ) * ρ.character z := by
    simpa [C₁, α, q] using character_one_mul_centralCharacterOfRep_mk ρ z
  have hcop : IsCoprime q (Nat.card (P : Subgroup G) : ℤ) := by
    simpa [C₁, q] using coprime_card_class_card_sylow P hPz
  have hψz : IsIntegral ℤ (ρ.character z) := character_isIntegral ρ z
  have hψ1 : IsIntegral ℤ (ρ.character 1) := character_isIntegral ρ 1
  have ha₁₁ : IsIntegral ℤ a₁₁ := by
    simpa [a₁₁, C₁] using nonidentityZClassCoeffSum_isIntegral Z C₁ C₁
  have ha₁₂ : IsIntegral ℤ a₁₂ := by
    simpa [a₁₂, C₁, C₂] using nonidentityZClassCoeffSum_isIntegral Z C₁ C₂
  have hone' : a₁₁ ≡ 1 + a₁₂ [ALGMOD (Nat.card (P : Subgroup G) : ℤ)] := by
    simpa [a₁₁, a₁₂, C₁, C₂] using hone
  exact peterfalvi_673 hcop hψz hψ1 ha₁₁ ha₁₂ h11 h12 hsubst hone'

end ClassCongruence

section CharacterDegreeDvd

variable {V : Type*} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]

variable [Fintype G] [DecidableEq (ConjClasses G)] [Fintype (ConjClasses G)]

omit [DecidableEq (ConjClasses G)] in
set_option backward.isDefEq.respectTransparency false in
/-- **Regrouping a class function by conjugacy class.** For `F : G → ℂ` constant on conjugacy
classes, the sum over `G` regroups as a sum over classes, each contributing `|C| · F(C.out)`. -/
theorem sum_eq_sum_conjClasses_of_isClassFun {F : G → ℂ}
    (hF : ∀ g h : G, F (h * g * h⁻¹) = F g) :
    ∑ g : G, F g
      = ∑ C : ConjClasses G, (Nat.card { x : G // ConjClasses.mk x = C } : ℂ) * F C.out := by
  classical
  -- Fiberwise over the conjugacy-class map `mk : G → ConjClasses G`.
  rw [← Finset.sum_fiberwise Finset.univ (fun g : G => ConjClasses.mk g) F]
  refine Finset.sum_congr rfl fun C _ => ?_
  -- On the fiber `{g | mk g = C}`, `F` is constant equal to `F C.out`.
  have hbody : ∀ g ∈ Finset.univ.filter (fun g : G => ConjClasses.mk g = C),
      F g = F C.out := by
    intro g hg
    rw [Finset.mem_filter] at hg
    -- `g` and `C.out` are conjugate (both have class `C`), so `F g = F C.out`.
    have hmkout : ConjClasses.mk C.out = C := by
      rw [← ConjClasses.quotient_mk_eq_mk, Quotient.out_eq]
    have hconj : IsConj C.out g := ConjClasses.mk_eq_mk_iff_isConj.mp (hmkout.trans hg.2.symm)
    obtain ⟨u, rfl⟩ := isConj_iff.mp hconj
    exact hF C.out u
  rw [Finset.sum_congr rfl hbody, Finset.sum_const, nsmul_eq_mul]
  congr 2
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype]

set_option backward.isDefEq.respectTransparency false in
/-- **First orthogonality in class-sum form.** For an irreducible representation `ρ`, summing the
class-sum central-character values weighted by `χ_ρ((C.out)⁻¹)` and rescaling by `χ_ρ(1)` recovers
`|G|`:
`(∑_C ω_ρ(C) · χ_ρ((C.out)⁻¹)) · χ_ρ(1) = |G|`.
This is the first orthogonality relation `∑_g χ_ρ(g) χ_ρ(g⁻¹) = |G|` (`char_orthonormal` with
`ρ ≅ ρ`) regrouped over conjugacy classes. -/
theorem sum_centralCharacter_mul_character_inv_mul_character_one (ρ : Representation ℂ G V)
    [IsIrreducible ρ] :
    (∑ C : ConjClasses G,
        centralCharacterOfRep ρ ⟨classSum C, classSum_mem_center C⟩ * ρ.character (C.out)⁻¹)
        * ρ.character 1 = (Nat.card G : ℂ) := by
  classical
  have := nontrivial_of_isIrreducible ρ
  have hd : ρ.character 1 ≠ 0 := by
    rw [ρ.char_one]; exact Nat.cast_ne_zero.mpr Module.finrank_pos.ne'
  -- First orthogonality `∑_g χ(g) χ(g⁻¹) = |G|` from `char_orthonormal` with `ρ ≅ ρ`.
  have : Invertible (Nat.card G : ℂ) :=
    invertibleOfNonzero (Nat.cast_ne_zero.mpr Nat.card_pos.ne')
  have hNℂ : (Nat.card G : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr Nat.card_pos.ne'
  have horth := Representation.char_orthonormal ρ ρ
  rw [if_pos ⟨Representation.Equiv.refl ρ⟩] at horth
  -- Clear the `(Nat.card G)⁻¹` factor: `∑_g χ(g) χ(g⁻¹) = |G|`.
  have hsumG : ∑ g : G, ρ.character g * ρ.character g⁻¹ = (Nat.card G : ℂ) := by
    field_simp at horth
    simpa [mul_comm] using horth
  -- Distribute `· χ(1)` over the sum and identify each term with `|C| χ(g_C) χ(g_C⁻¹)`.
  rw [Finset.sum_mul]
  have hterm : ∀ C : ConjClasses G,
      (centralCharacterOfRep ρ ⟨classSum C, classSum_mem_center C⟩ * ρ.character (C.out)⁻¹)
          * ρ.character 1
        = (Nat.card { x : G // ConjClasses.mk x = C } : ℂ)
            * (ρ.character C.out * ρ.character (C.out)⁻¹) := by
    intro C
    -- `ω_ρ(C) = (|C| χ(g_C)) / χ(1)` via `centralCharacterOfRep_classSum` + class-constancy.
    have hmkout : ConjClasses.mk C.out = C := by
      rw [← ConjClasses.quotient_mk_eq_mk, Quotient.out_eq]
    have homega : centralCharacterOfRep ρ ⟨classSum C, classSum_mem_center C⟩
        = ((Nat.card { x : G // ConjClasses.mk x = C } : ℂ) * ρ.character C.out)
            / ρ.character 1 := by
      rw [centralCharacterOfRep_classSum, sum_character_eq_card_mul ρ C hmkout, ρ.char_one]
    rw [homega, div_mul_eq_mul_div, div_mul_eq_mul_div, mul_div_assoc, div_self hd, mul_one]
    ring
  rw [Finset.sum_congr rfl (fun C _ => hterm C),
    ← sum_eq_sum_conjClasses_of_isClassFun
      (F := fun g => ρ.character g * ρ.character g⁻¹) ?_]
  · exact hsumG
  · intro g h
    rw [ρ.char_conj, show (h * g * h⁻¹)⁻¹ = h * g⁻¹ * h⁻¹ by group, ρ.char_conj]

end CharacterDegreeDvd

section CharacterDegreeDvdMain

variable {V : Type*} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V] [Finite G]

set_option backward.isDefEq.respectTransparency false in
/-- **`χ_ρ(1) ∣ |G|`** (Isaacs, *Character Theory of Finite Groups*, Thm 3.11; the classical
divisibility of the degree).  For an irreducible complex representation `ρ` of a finite group `G`,
the degree `χ_ρ(1) = dim V` divides the order of the group.

Proof (the standard algebraic-integer argument): the rational number `|G| / χ_ρ(1)` equals
`∑_C ω_ρ(C) · χ_ρ((g_C)⁻¹)` (first orthogonality regrouped over classes,
`sum_centralCharacter_mul_character_inv_mul_character_one`), a sum of products of algebraic integers
(`isIntegral_card_mul_character_div` for `ω_ρ(C)`, `character_isIntegral` for the conjugate factor),
hence itself an algebraic integer.  Being a rational algebraic integer it is an integer
(`isIntegral_rat_imp_int`), so `χ_ρ(1) ∣ |G|`. -/
theorem finrank_dvd_card (ρ : Representation ℂ G V) [IsIrreducible ρ] :
    finrank ℂ V ∣ Nat.card G := by
  classical
  have : Fintype G := Fintype.ofFinite G
  have : Finite (ConjClasses G) := Finite.of_surjective _ ConjClasses.mk_surjective
  have : Fintype (ConjClasses G) := Fintype.ofFinite _
  have := nontrivial_of_isIrreducible ρ
  set d : ℕ := finrank ℂ V with hd_def
  have hdpos : 0 < d := Module.finrank_pos
  have hdℂ : (d : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hdpos.ne'
  -- The summed quantity `S := ∑_C ω_ρ(C) · χ((g_C)⁻¹)`.
  set S : ℂ := ∑ C : ConjClasses G,
      centralCharacterOfRep ρ ⟨classSum C, classSum_mem_center C⟩ * ρ.character (C.out)⁻¹ with hS
  -- `S · χ(1) = |G|`, and `χ(1) = d`, so `S · d = |G|`.
  have hSd : S * (d : ℂ) = (Nat.card G : ℂ) := by
    have := sum_centralCharacter_mul_character_inv_mul_character_one ρ
    rwa [ρ.char_one] at this
  -- `S` is an algebraic integer: a sum of products of algebraic integers.
  have hSint : IsIntegral ℤ S := by
    refine IsIntegral.sum _ fun C _ => ?_
    refine IsIntegral.mul ?_ ?_
    · -- `ω_ρ(C) = |C| χ(g_C)/χ(1)` is an algebraic integer.
      have hmkout : ConjClasses.mk C.out = C := by
        rw [← ConjClasses.quotient_mk_eq_mk, Quotient.out_eq]
      have hval := isIntegral_card_mul_character_div ρ C hmkout
      have heq : centralCharacterOfRep ρ ⟨classSum C, classSum_mem_center C⟩
          = (Nat.card { x : G // ConjClasses.mk x = C } : ℂ) * ρ.character C.out
              / ρ.character 1 := by
        rw [centralCharacterOfRep_classSum, sum_character_eq_card_mul ρ C hmkout, ρ.char_one]
      rw [heq]; exact hval
    · exact character_isIntegral ρ (C.out)⁻¹
  -- `S = (|G| / d : ℚ)` cast to `ℂ`, so `S` is a rational algebraic integer, hence an integer.
  have hSrat : S = (((Nat.card G : ℚ) / (d : ℚ) : ℚ) : ℂ) := by
    rw [eq_div_of_mul_eq hdℂ hSd]
    push_cast
    ring
  obtain ⟨n, hn⟩ := isIntegral_rat_imp_int (q := (Nat.card G : ℚ) / (d : ℚ)) (hSrat ▸ hSint)
  -- From `S = n` and `S · d = |G|`: `(n : ℂ) · d = |G|`, descend to `ℤ` then to `ℕ`.
  rw [hSrat, hn] at hSd
  -- `(n : ℂ) * d = |G|` over `ℂ` ⇒ `n * d = |G|` over `ℤ`.
  have hZ : n * (d : ℤ) = (Nat.card G : ℤ) := by
    have hcast : ((n * (d : ℤ) : ℤ) : ℂ) = ((Nat.card G : ℤ) : ℂ) := by
      push_cast
      linear_combination hSd
    exact_mod_cast hcast
  -- `d ∣ |G|` in `ℤ`, hence in `ℕ`.
  have hdvdZ : (d : ℤ) ∣ (Nat.card G : ℤ) := ⟨n, by rw [← hZ]; ring⟩
  exact_mod_cast hdvdZ

/-- **The degree of an irreducible representation of a `p`-group is a power of `p`** (Isaacs,
*Character Theory of Finite Groups*, Cor. 3.12 / standard).  If `G` is a finite `p`-group and `ρ`
is an irreducible complex representation of `G`, then `dim V = χ_ρ(1)` is a power of the prime `p`.

This is the immediate divisibility corollary of `finrank_dvd_card`: writing `|G| = p ^ n`
(`IsPGroup.iff_card`), the degree divides `p ^ n`, and a divisor of a prime power is itself a
power of that prime (`Nat.dvd_prime_pow`). -/
theorem exists_finrank_eq_prime_pow_of_isPGroup {p : ℕ} [Fact p.Prime] (hG : IsPGroup p G)
    (ρ : Representation ℂ G V) [IsIrreducible ρ] :
    ∃ k : ℕ, finrank ℂ V = p ^ k := by
  obtain ⟨n, hn⟩ := (IsPGroup.iff_card (p := p)).mp hG
  have hdvd : finrank ℂ V ∣ p ^ n := hn ▸ finrank_dvd_card ρ
  obtain ⟨k, _, hk⟩ := (Nat.dvd_prime_pow (p := p) (Fact.out (p := p.Prime))).mp hdvd
  exact ⟨k, hk⟩

end CharacterDegreeDvdMain

end OddOrder.RepresentationTheory


