-- Prove2me | Definitions.Def_RPLib_S4_PicDescentB4
-- name    : RPLib_S4_PicDescentB4
-- status  : Definition
-- author  : @Nickrobbins95
-- created : 2026-11-15T05:13:47.839202+00:00
-- url     : https://prove2.me/theorems/487c8bc6-9608-46e7-bc78-98eb47be6bfe
-- title:
--   The finite subfields $\mathbb{F}_{q^n}$ of a field over $\mathbb{F}_q$
-- statement:
--   Let $\Omega$ be a field over the finite field $\mathbb{F}_q$. The file defines the $n$-th power of the $q$-power Frobenius $x \mapsto x^{q^n}$ and its fixed field $$L_n = \{x \in \Omega : x^{q^n} = x\},$$ proves that $L_n$ is finite for $n \ne 0$, and that when $\Omega$ is algebraically closed $\#L_n = q^n$ and $[L_n : \mathbb{F}_q] = n$.
--
--   **Formalization note.** Library module of a formalization of the Ramanujan-Petersson conjecture (etale fundamental groups, Kummer theory and tame ramification on affine curves over finite fields). It contains definitions together with proved lemmas (no `sorry`), so that later solution files can import them.
-- source:
--   R. Lidl, H. Niederreiter, Finite Fields, 2nd ed., Encyclopedia of Mathematics and its Applications 20, Cambridge University Press (1997), Chapter 2

import Definitions.Def_RPLib_S4_PicDescentB3

/-!
# S4-PicDescent, part B4a: the finite fields `L_n` inside an ambient field

`Ω` any field over the finite field `Fq` (`q = #Fq`).
* `frobPow Fq Ω n`: the `n`-th power of the arithmetic (`q`-power) Frobenius, `x ↦ x ^ q ^ n`.
* `Lc Fq Ω n`: its fixed field `{x | x ^ q ^ n = x}`; finite for `n ≠ 0`; when `Ω` is algebraically closed it has
  `q ^ n` elements and `[L_n : Fq] = n`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open scoped Polynomial

namespace RamanujanPetersson.PicDescent

open Polynomial

section Frob

variable (Fq : Type*) [Field Fq] [Fintype Fq] (Ω : Type*) [Field Ω] [Algebra Fq Ω]

/-- The `n`-th power of the arithmetic (`q`-power) Frobenius of `Ω` over `Fq`. -/
noncomputable def frobPow (n : ℕ) : Ω →ₐ[Fq] Ω := FiniteField.frobeniusAlgHom Fq Ω ^ n

theorem frobPow_apply (n : ℕ) (x : Ω) : frobPow Fq Ω n x = x ^ Fintype.card Fq ^ n := by
  induction n generalizing x with
  | zero => simp [frobPow]
  | succ n ih =>
    rw [frobPow, pow_succ, AlgHom.mul_apply, ← frobPow, ih, FiniteField.frobeniusAlgHom_apply,
      ← pow_mul, pow_succ']

/-- `L_n`: the fixed field of the `q ^ n`-Frobenius. -/
noncomputable def Lc (n : ℕ) : IntermediateField Fq Ω :=
  Subalgebra.toIntermediateField (AlgHom.equalizer (frobPow Fq Ω n) (AlgHom.id Fq Ω)) fun x hx => by
    rw [AlgHom.mem_equalizer, frobPow_apply, AlgHom.id_apply] at hx ⊢
    rw [inv_pow, hx]

variable {Fq Ω} in
theorem mem_Lc {n : ℕ} {x : Ω} : x ∈ Lc Fq Ω n ↔ x ^ Fintype.card Fq ^ n = x := by
  show x ∈ AlgHom.equalizer (frobPow Fq Ω n) (AlgHom.id Fq Ω) ↔ _
  rw [AlgHom.mem_equalizer, frobPow_apply, AlgHom.id_apply]

/-- `X ^ q ^ n - X`. -/
noncomputable def galPoly (n : ℕ) : Fq[X] := X ^ Fintype.card Fq ^ n - X

theorem natDegree_galPoly {n : ℕ} (hn : n ≠ 0) :
    (galPoly Fq n).natDegree = Fintype.card Fq ^ n :=
  FiniteField.X_pow_card_pow_sub_X_natDegree_eq Fq hn Fintype.one_lt_card

theorem galPoly_ne_zero {n : ℕ} (hn : n ≠ 0) : galPoly Fq n ≠ 0 := by
  intro h
  have := natDegree_galPoly Fq hn
  rw [h, natDegree_zero] at this
  exact (pow_pos Fintype.card_pos n).ne this

theorem galPoly_separable {n : ℕ} (hn : n ≠ 0) : (galPoly Fq n).Separable := by
  have h : ((Fintype.card Fq ^ n : ℕ) : Fq) = 0 := by
    rw [Nat.cast_pow, FiniteField.cast_card_eq_zero, zero_pow hn]
  exact galois_poly_separable (ringChar Fq) _ (ringChar.dvd h)

theorem mem_Lc_iff_rootSet {n : ℕ} (hn : n ≠ 0) {x : Ω} :
    x ∈ Lc Fq Ω n ↔ x ∈ (galPoly Fq n).rootSet Ω := by
  rw [mem_Lc, mem_rootSet]
  have e : aeval x (galPoly Fq n) = x ^ Fintype.card Fq ^ n - x := by
    rw [galPoly, map_sub, map_pow, aeval_X]
  rw [e, sub_eq_zero]
  exact ⟨fun h => ⟨galPoly_ne_zero Fq hn, h⟩, fun h => h.2⟩

instance finite_Lc (n : ℕ) [NeZero n] : Finite (Lc Fq Ω n) := by
  have : (Lc Fq Ω n : Set Ω) ⊆ (galPoly Fq n).rootSet Ω := fun x hx =>
    (mem_Lc_iff_rootSet Fq Ω (NeZero.ne n)).1 hx
  exact (((galPoly Fq n).rootSet_finite Ω).subset this).to_subtype

noncomputable instance fintype_Lc (n : ℕ) [NeZero n] : Fintype (Lc Fq Ω n) := Fintype.ofFinite _

theorem card_Lc [IsAlgClosed Ω] {n : ℕ} (hn : n ≠ 0) :
    Nat.card (Lc Fq Ω n) = Fintype.card Fq ^ n := by
  classical
  have e : (Lc Fq Ω n : Set Ω) = (galPoly Fq n).rootSet Ω :=
    Set.ext fun x => mem_Lc_iff_rootSet Fq Ω hn
  have hc := card_rootSet_eq_natDegree (K := Ω) (galPoly_separable Fq hn) (IsAlgClosed.splits _)
  rw [natDegree_galPoly Fq hn] at hc
  rw [← hc, ← Nat.card_eq_fintype_card]
  exact Nat.card_congr (Equiv.setCongr e)

theorem finrank_Lc [IsAlgClosed Ω] {n : ℕ} (hn : n ≠ 0) : Module.finrank Fq (Lc Fq Ω n) = n := by
  have : NeZero n := ⟨hn⟩
  have h1 := Module.card_eq_pow_finrank (K := Fq) (V := Lc Fq Ω n)
  rw [Fintype.card_eq_nat_card, card_Lc Fq Ω hn] at h1
  exact (Nat.pow_right_injective Fintype.one_lt_card h1).symm

variable {Fq Ω} in
theorem isSeparable_of_mem_Lc {n : ℕ} [NeZero n] {x : Ω} (hx : x ∈ Lc Fq Ω n) : IsSeparable Fq x := by
  have hr := (mem_Lc_iff_rootSet Fq Ω (NeZero.ne n)).1 hx
  rw [mem_rootSet] at hr
  exact (galPoly_separable Fq (NeZero.ne n)).of_dvd (minpoly.dvd Fq x hr.2)

/-- A power basis of `L_n` over `Fq`. -/
noncomputable def pbL (n : ℕ) [NeZero n] : PowerBasis Fq (Lc Fq Ω n) :=
  Field.powerBasisOfFiniteOfSeparable Fq (Lc Fq Ω n)

end Frob

section Ext

variable (Fq : Type*) [Field Fq] [Fintype Fq]
variable (F : Type*) [Field F] [Algebra Fq F]
variable (Ω : Type*) [Field Ω] [Algebra Fq Ω] [Algebra F Ω] [IsScalarTower Fq F Ω]

/-- `F_n = F · L_n` inside `Ω`: the constant field extension of degree `n`. -/
noncomputable def Fc (n : ℕ) : IntermediateField F Ω := IntermediateField.adjoin F (Lc Fq Ω n : Set Ω)

variable {Fq F Ω} in
theorem mem_Fc_of_mem_Lc {n : ℕ} {x : Ω} (hx : x ∈ Lc Fq Ω n) : x ∈ Fc Fq F Ω n :=
  IntermediateField.subset_adjoin F _ hx

/-- The inclusion `L_n → F_n`. -/
noncomputable def LtoF (n : ℕ) : Lc Fq Ω n →+* Fc Fq F Ω n where
  toFun x := ⟨x, mem_Fc_of_mem_Lc x.2⟩
  map_one' := rfl
  map_mul' _ _ := rfl
  map_zero' := rfl
  map_add' _ _ := rfl

noncomputable instance algebra_LF (n : ℕ) : Algebra (Lc Fq Ω n) (Fc Fq F Ω n) :=
  (LtoF Fq F Ω n).toAlgebra

theorem coe_algebraMap_LF {n : ℕ} (x : Lc Fq Ω n) :
    ((algebraMap (Lc Fq Ω n) (Fc Fq F Ω n) x : Fc Fq F Ω n) : Ω) = x := rfl

instance isScalarTower_LF (n : ℕ) : IsScalarTower Fq (Lc Fq Ω n) (Fc Fq F Ω n) :=
  IsScalarTower.of_algebraMap_eq fun _ => Subtype.ext rfl

instance finiteDimensional_Fc (n : ℕ) [NeZero n] : FiniteDimensional F (Fc Fq F Ω n) := by
  have : Finite (Lc Fq Ω n : Set Ω) := finite_Lc Fq Ω n
  exact IntermediateField.finiteDimensional_adjoin fun x hx =>
    ((isSeparable_of_mem_Lc hx).tower_top F).isIntegral

instance isSeparable_Fc (n : ℕ) [NeZero n] : Algebra.IsSeparable F (Fc Fq F Ω n) :=
  (IntermediateField.isSeparable_adjoin_iff_isSeparable F Ω).2 fun _ hx =>
    (isSeparable_of_mem_Lc hx).tower_top F

theorem Fc_eq_adjoin (n : ℕ) [NeZero n] :
    Fc Fq F Ω n = IntermediateField.adjoin F {((pbL Fq Ω n).gen : Ω)} := by
  apply le_antisymm
  · rw [Fc, IntermediateField.adjoin_le_iff]
    intro y hy
    obtain ⟨f, -, hf⟩ := (pbL Fq Ω n).exists_eq_aeval ⟨y, hy⟩
    have hy' : y = aeval ((pbL Fq Ω n).gen : Ω) f := by
      have := congrArg (Lc Fq Ω n).val hf
      rw [← Polynomial.aeval_algHom_apply] at this
      exact this
    have h2 : aeval ((pbL Fq Ω n).gen : Ω) (f.map (algebraMap Fq F)) ∈
        IntermediateField.adjoin F {((pbL Fq Ω n).gen : Ω)} :=
      IntermediateField.algebra_adjoin_le_adjoin F _ (Polynomial.aeval_mem_adjoin_singleton F _)
    rw [Polynomial.aeval_map_algebraMap] at h2
    rw [hy']
    exact h2
  · exact IntermediateField.adjoin_simple_le_iff.2 (mem_Fc_of_mem_Lc (pbL Fq Ω n).gen.2)

section FF

variable [DecidableEq (RatFunc Fq)] [Algebra Fq[X] F] [Algebra (RatFunc Fq) F]
  [IsScalarTower Fq[X] (RatFunc Fq) F] [IsScalarTower Fq Fq[X] F] [FunctionField Fq F]
  [Algebra.IsSeparable (RatFunc Fq) F]

/-- The separating element `x` of `F`, inside `F_n`. -/
noncomputable def xc (n : ℕ) : Fc Fq F Ω n := algebraMap F (Fc Fq F Ω n) (RR.xF Fq F)

noncomputable instance algebra_polyF (n : ℕ) : Algebra (Lc Fq Ω n)[X] (Fc Fq F Ω n) :=
  (aeval (xc Fq F Ω n)).toRingHom.toAlgebra

theorem algebraMap_polyF {n : ℕ} (p : (Lc Fq Ω n)[X]) :
    algebraMap (Lc Fq Ω n)[X] (Fc Fq F Ω n) p = aeval (xc Fq F Ω n) p := rfl

instance isScalarTower_polyF (n : ℕ) :
    IsScalarTower (Lc Fq Ω n) (Lc Fq Ω n)[X] (Fc Fq F Ω n) :=
  IsScalarTower.of_algebraMap_eq fun a => (aeval_C (xc Fq F Ω n) a).symm

theorem transcendental_xF : Transcendental Fq (RR.xF Fq F) := by
  rw [transcendental_iff_injective]
  intro p p' h
  rw [RR.aeval_xF, RR.aeval_xF] at h
  exact FaithfulSMul.algebraMap_injective Fq[X] F h

theorem transcendental_xc (n : ℕ) [NeZero n] : Transcendental (Lc Fq Ω n) (xc Fq F Ω n) := by
  have h1 : Transcendental Fq (xc Fq F Ω n) := by
    rw [xc, transcendental_algebraMap_iff (algebraMap F (Fc Fq F Ω n)).injective]
    exact transcendental_xF Fq F
  exact h1.extendScalars (Lc Fq Ω n)

theorem aeval_xc_injective (n : ℕ) [NeZero n] :
    Function.Injective (aeval (R := Lc Fq Ω n) (xc Fq F Ω n)) :=
  transcendental_iff_injective.1 (transcendental_xc Fq F Ω n)

noncomputable instance algebra_ratF (n : ℕ) [NeZero n] :
    Algebra (RatFunc (Lc Fq Ω n)) (Fc Fq F Ω n) :=
  (RatFunc.liftAlgHom (aeval (xc Fq F Ω n))
    (nonZeroDivisors_le_comap_nonZeroDivisors_of_injective _
      (aeval_xc_injective Fq F Ω n))).toRingHom.toAlgebra

theorem algebraMap_ratF (n : ℕ) [NeZero n] (g : RatFunc (Lc Fq Ω n)) :
    algebraMap (RatFunc (Lc Fq Ω n)) (Fc Fq F Ω n) g = RatFunc.liftAlgHom (aeval (xc Fq F Ω n))
      (nonZeroDivisors_le_comap_nonZeroDivisors_of_injective _ (aeval_xc_injective Fq F Ω n)) g :=
  rfl

instance isScalarTower_ratF (n : ℕ) [NeZero n] :
    IsScalarTower (Lc Fq Ω n)[X] (RatFunc (Lc Fq Ω n)) (Fc Fq F Ω n) :=
  IsScalarTower.of_algebraMap_eq fun p => by
    rw [algebraMap_ratF, ← div_one (algebraMap (Lc Fq Ω n)[X] (RatFunc (Lc Fq Ω n)) p),
      ← map_one (algebraMap (Lc Fq Ω n)[X] (RatFunc (Lc Fq Ω n))), RatFunc.liftAlgHom_apply_div,
      map_one, div_one, algebraMap_polyF]

noncomputable instance decEq_ratL (n : ℕ) : DecidableEq (RatFunc (Lc Fq Ω n)) := Classical.decEq _

theorem hx_Fc (n : ℕ) [NeZero n] :
    algebraMap F (Fc Fq F Ω n) (RR.xF Fq F) = RR.xF (Lc Fq Ω n) (Fc Fq F Ω n) := by
  show xc Fq F Ω n = algebraMap (Lc Fq Ω n)[X] (Fc Fq F Ω n) X
  rw [algebraMap_polyF, aeval_X]

instance functionField_Fc (n : ℕ) [NeZero n] : FunctionField (Lc Fq Ω n) (Fc Fq F Ω n) := by
  letI : Algebra (RatFunc Fq) (Fc Fq F Ω n) :=
    ((algebraMap F (Fc Fq F Ω n)).comp (algebraMap (RatFunc Fq) F)).toAlgebra
  haveI : IsScalarTower (RatFunc Fq) F (Fc Fq F Ω n) := IsScalarTower.of_algebraMap_eq fun _ => rfl
  haveI : Module.Finite (RatFunc Fq) (Fc Fq F Ω n) := Module.Finite.trans F (Fc Fq F Ω n)
  letI : Algebra (RatFunc Fq) (RatFunc (Lc Fq Ω n)) := (ratMap Fq (Lc Fq Ω n)).toAlgebra
  haveI : IsScalarTower (RatFunc Fq) (RatFunc (Lc Fq Ω n)) (Fc Fq F Ω n) :=
    IsScalarTower.of_algebraMap_eq fun g =>
      (RingHom.congr_fun (compat_rat_hom (hx_Fc Fq F Ω n)) g).symm
  exact Module.Finite.of_restrictScalars_finite (RatFunc Fq) (RatFunc (Lc Fq Ω n)) (Fc Fq F Ω n)

instance isSeparable_ratF (n : ℕ) [NeZero n] :
    Algebra.IsSeparable (RatFunc (Lc Fq Ω n)) (Fc Fq F Ω n) := by
  letI : Algebra (RatFunc Fq) (Fc Fq F Ω n) :=
    ((algebraMap F (Fc Fq F Ω n)).comp (algebraMap (RatFunc Fq) F)).toAlgebra
  haveI : IsScalarTower (RatFunc Fq) F (Fc Fq F Ω n) := IsScalarTower.of_algebraMap_eq fun _ => rfl
  letI : Algebra (RatFunc Fq) (RatFunc (Lc Fq Ω n)) := (ratMap Fq (Lc Fq Ω n)).toAlgebra
  haveI : IsScalarTower (RatFunc Fq) (RatFunc (Lc Fq Ω n)) (Fc Fq F Ω n) :=
    IsScalarTower.of_algebraMap_eq fun g =>
      (RingHom.congr_fun (compat_rat_hom (hx_Fc Fq F Ω n)) g).symm
  haveI : Algebra.IsSeparable (RatFunc Fq) (Fc Fq F Ω n) :=
    Algebra.IsSeparable.trans (F := RatFunc Fq) (E := F) (K := Fc Fq F Ω n)
  exact Algebra.isSeparable_tower_top_of_isSeparable (RatFunc Fq) (RatFunc (Lc Fq Ω n))
    (Fc Fq F Ω n)

theorem finrank_Fc (hk : Places.constField Fq F = ⊥) (n : ℕ) [NeZero n] :
    Module.finrank F (Fc Fq F Ω n) = Module.finrank Fq (Lc Fq Ω n) := by
  have h1 := natDegree_minpoly (F' := Fc Fq F Ω n) (pbL Fq Ω n) hk
  have h2 : minpoly F ((pbL Fq Ω n).gen : Ω) =
      minpoly F (algebraMap (Lc Fq Ω n) (Fc Fq F Ω n) (pbL Fq Ω n).gen) := by
    rw [← minpoly.algHom_eq (Fc Fq F Ω n).val (fun a b h => Subtype.ext h)]
    rfl
  rw [(IntermediateField.equivOfEq (Fc_eq_adjoin Fq F Ω n)).toLinearEquiv.finrank_eq,
    IntermediateField.adjoin.finrank
      ((isSeparable_of_mem_Lc (pbL Fq Ω n).gen.2).tower_top F).isIntegral, h2, h1,
    (pbL Fq Ω n).finrank]

/-- **`F_n / F` is a constant field extension** (in the coordinates of `RR.IsConstExt`). -/
theorem isConstExt_Fc (hk : Places.constField Fq F = ⊥) (n : ℕ) [NeZero n] :
    RR.IsConstExt Fq F (Lc Fq Ω n) (Fc Fq F Ω n) (pbL Fq Ω n).basis :=
  isConstExt (pbL Fq Ω n) hk (finrank_Fc Fq F Ω hk n) (hx_Fc Fq F Ω n)

theorem genusF_Fc (hk : Places.constField Fq F = ⊥) (n : ℕ) [NeZero n] :
    RR.genusF (Lc Fq Ω n) (Fc Fq F Ω n) = RR.genusF Fq F :=
  genusF_eq (pbL Fq Ω n) hk (finrank_Fc Fq F Ω hk n) (hx_Fc Fq F Ω n)

theorem constField_Fc (hk : Places.constField Fq F = ⊥) (n : ℕ) [NeZero n] :
    Places.constField (Lc Fq Ω n) (Fc Fq F Ω n) = ⊥ :=
  constField_eq_bot (pbL Fq Ω n) hk (finrank_Fc Fq F Ω hk n) (hx_Fc Fq F Ω n)

end FF

end Ext

end RamanujanPetersson.PicDescent


