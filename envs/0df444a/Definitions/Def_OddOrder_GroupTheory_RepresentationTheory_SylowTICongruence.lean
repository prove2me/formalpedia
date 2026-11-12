-- Prove2me | Definitions.Def_OddOrder_GroupTheory_RepresentationTheory_SylowTICongruence
-- name    : OddOrder_GroupTheory_RepresentationTheory_SylowTICongruence
-- status  : Definition
-- author  : @burkh4rt
-- created : 2026-11-12T05:10:24.631754+00:00
-- url     : https://prove2.me/theorems/1b85d59c-9203-4a9d-8179-76de213a87dc
-- title:
--   Peterfalvi (6.7): odd-order assembly
-- statement:
--   Formalizes Peterfalvi (6.7) (pp. 31–32), odd-order form. Let $P$ be a Sylow $p$-subgroup of $G$, $L=N_G(P)$ of odd order, $P^\#$ a TI-subset, and $Z\trianglelefteq L$ with $1\ne Z\le Z(P)$ and $|C_L(z)|$ independent of $z\in Z^\#$. If $\psi\in\mathrm{Irr}\,G$ is constant on $Z^\#$ then $\psi(z)\equiv\psi(1)\pmod{|P|}$. The earlier proof `peterfalvi_67` left two inputs as hypotheses; this file discharges them (the real-class condition from $|L|$ odd) and assembles the odd-order form.
--
--   The main result is `peterfalvi_67_of_odd` (Peterfalvi (6.7), odd-order form). The bundle consists of lemmas only.
--
--   The bundle also proves 1 supporting lemma used by later statements.
-- source:
--   Yawara Ishida, Lean 4 formalization of the Feit–Thompson (odd order) theorem, github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0), https://github.com/yawara/odd-order/blob/20a6fccbb63c0b138acda9f7fafd798c42f9441b/OddOrder/GroupTheory/RepresentationTheory/SylowTICongruence.lean

/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
-- From github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0; LICENSE at that commit):
--   OddOrder/GroupTheory/RepresentationTheory/SylowTICongruence.lean
-- Generated for Prove2Me by deleting declarations; the remaining commands are verbatim except:
-- `private` dropped where another file uses the declaration, and a solution's main theorem
-- renamed `_root_.solution` (platform convention).
import Definitions.Def_OddOrder_GroupTheory_RepresentationTheory_ClassSumAlgebra
import Definitions.Def_OddOrder_GroupTheory_RepresentationTheory_RealClassTISubset
import Definitions.Def_OddOrder_GroupTheory_RepresentationTheory_SchurCenterBound
import Mathlib.RepresentationTheory.Character
import Mathlib.RepresentationTheory.Invariants

namespace OddOrder.RepresentationTheory

open OddOrder.GroupTheory.CenterClassSum

open OddOrder.AlgInt

local notation3 "ω" ρ:max C:max => centralCharacterOfRep ρ ⟨classSum C, classSum_mem_center C⟩

variable {G : Type*} [Group G]

variable {V : Type*} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]

variable [Fintype G] [DecidableEq G] [DecidableEq (ConjClasses G)] [Fintype (ConjClasses G)]

/-- **The trivial-character instance of (6.7.2)–(6.7.3)**: under the (6.7) Sylow/TI setup
the collapsed nonidentity-`Z` structure-constant sums satisfy
`a₁₁ ≡ 1 + a₁₂ (mod |P|)`.

For the trivial representation the central character is `ω(C) = |C|` and all character
values are `1`, so the two collapsed (6.7.2) congruences at `(1,1)` and `(1,2)` combine and
the coprime factor `q = |C₁|` cancels, leaving the structure-constant congruence that
`peterfalvi_67` consumes as its `hone` input. -/
theorem nonidentityZClassCoeffSum_cong_of_isTISubset [Finite G]
    {p : ℕ} [Fact p.Prime] (P : Sylow p G) {Z : Subgroup G}
    (hZP : Z ≤ (P : Subgroup G))
    (hZnormal : (Z.subgroupOf (Subgroup.normalizer ((P : Subgroup G) : Set G))).Normal)
    (hti : OddOrder.GroupTheory.IsTISubset ((P : Set G) \ {1})
      (Subgroup.normalizer ((P : Subgroup G) : Set G)))
    {z : G} (hzZ : z ∈ Z) (hz1 : z ≠ 1)
    (hPz : (P : Subgroup G) ≤ Subgroup.centralizer {z})
    (hreal : ConjClasses.mk z⁻¹ ≠ ConjClasses.mk z)
    (hcardconst : ∀ ⦃w : G⦄, w ∈ Z → w ≠ 1 →
      Nat.card ↥(Subgroup.normalizer ((P : Subgroup G) : Set G) ⊓
          Subgroup.centralizer ({w} : Set G)) =
        Nat.card ↥(Subgroup.normalizer ((P : Subgroup G) : Set G) ⊓
          Subgroup.centralizer ({z} : Set G))) :
    nonidentityZClassCoeffSum Z (ConjClasses.mk z) (ConjClasses.mk z)
      ≡ 1 + nonidentityZClassCoeffSum Z (ConjClasses.mk z) (ConjClasses.mk z⁻¹)
        [ALGMOD (Nat.card (P : Subgroup G) : ℤ)] := by
  classical
  set ρ₀ : Representation ℂ G ℂ := Representation.trivial ℂ G ℂ with hρ₀
  have : ρ₀.IsIrreducible := isIrreducible_complex_rep ρ₀
  have hchar0 : ∀ g : G, ρ₀.character g = 1 := by
    intro g
    simp [hρ₀, Representation.character]
  let C₁ : ConjClasses G := ConjClasses.mk z
  let C₂ : ConjClasses G := ConjClasses.mk z⁻¹
  let α : ℂ := ω ρ₀ C₁
  let a₁₁ : ℂ := nonidentityZClassCoeffSum Z C₁ C₁
  let a₁₂ : ℂ := nonidentityZClassCoeffSum Z C₁ C₂
  let q : ℤ := Nat.card { x : G // ConjClasses.mk x = C₁ }
  have hzA : z ∈ (P : Set G) \ {1} := ⟨hZP hzZ, by simpa using hz1⟩
  have hωconst : ∀ ⦃w : G⦄, w ∈ Z → w ≠ 1 → ω ρ₀ (ConjClasses.mk w) = α := by
    intro w hwZ hw1
    have hwA : w ∈ (P : Set G) \ {1} := ⟨hZP hwZ, by simpa using hw1⟩
    exact centralCharacterOfRep_eq_of_tiSubset_card_eq_of_character_eq ρ₀ hti hwA hzA
      (hcardconst hwZ hw1) (by rw [hchar0, hchar0])
  have hC₁ : ∃ y : G, y ∈ Z ∧ y ≠ 1 ∧ ConjClasses.mk y = C₁ := ⟨z, hzZ, hz1, rfl⟩
  have hC₂ : ∃ y : G, y ∈ Z ∧ y ≠ 1 ∧ ConjClasses.mk y = C₂ :=
    ⟨z⁻¹, Z.inv_mem hzZ, inv_ne_one.mpr hz1, rfl⟩
  have hcoeff11 : (classSum C₁ * classSum C₁ : MonoidAlgebra ℂ G).coeff (1 : G) = 0 := by
    rw [classSum_mul_apply_one_eq_classSumCoeff_one]
    rw [show classSumCoeff C₁ C₁ 1 = 0 by
      simpa [C₁] using classSumCoeff_self_one_eq_zero z hreal]
    norm_num
  have hcoeff12 : (classSum C₁ * classSum C₂ : MonoidAlgebra ℂ G).coeff (1 : G) = (q : ℂ) := by
    rw [classSum_mul_apply_one_eq_classSumCoeff_one]
    rw [show classSumCoeff C₁ C₂ 1 = Nat.card { x : G // ConjClasses.mk x = C₁ } by
      simpa [C₁, C₂] using classSumCoeff_self_inv_one_eq_card z]
    simp [q]
  have h11raw := centralCharacterOfRep_classSum_mul_cong_collapse_of_isTISubset ρ₀ P hZP
    hZnormal hti hC₁ hC₁ (α := α) hωconst
  have h12raw := centralCharacterOfRep_classSum_mul_cong_collapse_of_isTISubset ρ₀ P hZP
    hZnormal hti hC₁ hC₂ (α := α) hωconst
  have hωC₂ : ω ρ₀ C₂ = α := by
    simpa [C₂] using hωconst (Z.inv_mem hzZ) (inv_ne_one.mpr hz1)
  have h11 : (1 : ℂ) * α ^ 2 ≡ 1 * (a₁₁ * α)
      [ALGMOD (Nat.card (P : Subgroup G) : ℤ)] := by
    simpa [C₁, α, a₁₁, pow_two, hcoeff11, hchar0] using h11raw
  have h12 : (1 : ℂ) * α ^ 2 ≡ 1 * ((q : ℂ) + a₁₂ * α)
      [ALGMOD (Nat.card (P : Subgroup G) : ℤ)] := by
    simpa [C₁, C₂, α, a₁₂, q, pow_two, hcoeff12, hωC₂, hchar0] using h12raw
  have hsubst : (1 : ℂ) * α = (q : ℂ) * 1 := by
    have h := character_one_mul_centralCharacterOfRep_mk ρ₀ z
    simpa [C₁, α, q, hchar0] using h
  have hcop : IsCoprime q (Nat.card (P : Subgroup G) : ℤ) := by
    simpa [C₁, q] using coprime_card_class_card_sylow P hPz
  have ha₁₁ : IsIntegral ℤ a₁₁ := by
    simpa [a₁₁, C₁] using nonidentityZClassCoeffSum_isIntegral Z C₁ C₁
  have ha₁₂ : IsIntegral ℤ a₁₂ := by
    simpa [a₁₂, C₁, C₂] using nonidentityZClassCoeffSum_isIntegral Z C₁ C₂
  have hcomb := peterfalvi_673_combine h11 h12
  have hfinal := peterfalvi_673_cancel hcop isIntegral_one isIntegral_one ha₁₁ ha₁₂
    hsubst hcomb
  simpa [a₁₁, a₁₂, C₁, C₂] using hfinal

set_option linter.unusedFintypeInType false in
set_option linter.unusedDecidableInType false in
/-- **Peterfalvi (6.7)** (odd-order form, mmd 04.8 L86).  Let `P` be a Sylow `p`-subgroup of
`G` with `L = N_G(P)` of **odd** order and `P^#` a TI-subset of `G`; let `Z ⊴ L` with
`Z ≤ P`, `z ∈ Z^#` centralized by `P` (the `Z ≤ Z(P)` instance at `z`), and `|C_L(·)|`
constant on `Z^#`.  If the irreducible character `ψ = χ_ρ` is constant on `Z^#`, then

`ψ(z) ≡ ψ(1) (mod |P|)`

as algebraic integers.  The two non-hypothesis inputs of `peterfalvi_67` are discharged:
`⟦z⁻¹⟧ ≠ ⟦z⟧` from oddness of `|L|`, and the structure-constant congruence from the
trivial-character specialization. -/
theorem peterfalvi_67_of_odd [Finite G] (ρ : Representation ℂ G V) [ρ.IsIrreducible]
    {p : ℕ} [Fact p.Prime] (P : Sylow p G) {Z : Subgroup G}
    (hZP : Z ≤ (P : Subgroup G))
    (hZnormal : (Z.subgroupOf (Subgroup.normalizer ((P : Subgroup G) : Set G))).Normal)
    (hti : OddOrder.GroupTheory.IsTISubset ((P : Set G) \ {1})
      (Subgroup.normalizer ((P : Subgroup G) : Set G)))
    (hodd : Odd (Nat.card (Subgroup.normalizer ((P : Subgroup G) : Set G))))
    {z : G} (hzZ : z ∈ Z) (hz1 : z ≠ 1)
    (hPz : (P : Subgroup G) ≤ Subgroup.centralizer {z})
    (hconst : ∀ ⦃w : G⦄, w ∈ Z → w ≠ 1 →
      ρ.character w = ρ.character z ∧
        Nat.card ↥(Subgroup.normalizer ((P : Subgroup G) : Set G) ⊓
            Subgroup.centralizer ({w} : Set G)) =
          Nat.card ↥(Subgroup.normalizer ((P : Subgroup G) : Set G) ⊓
            Subgroup.centralizer ({z} : Set G))) :
    ρ.character z ≡ ρ.character 1 [ALGMOD (Nat.card (P : Subgroup G) : ℤ)] := by
  have hreal : ConjClasses.mk z⁻¹ ≠ ConjClasses.mk z := by
    rw [Ne, ConjClasses.mk_eq_mk_iff_isConj]
    exact not_isConj_inv_of_isTISubset P hodd hti (hZP hzZ) hz1
  exact peterfalvi_67 ρ P hZP hZnormal hti hzZ hz1 hPz hreal hconst
    (nonidentityZClassCoeffSum_cong_of_isTISubset P hZP hZnormal hti hzZ hz1 hPz hreal
      (fun w hw h1 => (hconst hw h1).2))

end OddOrder.RepresentationTheory


