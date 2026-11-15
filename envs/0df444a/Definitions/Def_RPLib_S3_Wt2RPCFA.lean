-- Prove2me | Definitions.Def_RPLib_S3_Wt2RPCFA
-- name    : RPLib_S3_Wt2RPCFA
-- status  : Definition
-- author  : @Nickrobbins95
-- created : 2026-11-14T16:25:19.28653+00:00
-- url     : https://prove2.me/theorems/2863b4e7-beb9-4a22-8e32-7269443d9b40
-- title:
--   Weight-two Ramanujan-Petersson library: a function field over `Fq` and over a finite field of constants `k ⊆ F`
-- statement:
--   A function field over `Fq` and over a finite field of constants `k ⊆ F`.
--
--   Generic comparison, for `Fq ⊆ k ⊆ F` with `k` integral over `Fq` and the same coordinate
--   `x = algebraMap Fq[X] F X = algebraMap k[X] F X`:
--   * `algebraMap_poly_eq`: `Fq[X] → F` factors through `k[X]` (coefficientwise map).
--   * `isIntegral_poly_iff`: integral over `Fq[X]` iff integral over `k[X]`; `rfinEquiv`: the two rings `Rfin` agree.
--   * `homSigmaEquiv`: `Hom_Fq(Rfin_Fq, L) ≃ Σ (σ : k →ₐ[Fq] L), {ψ : Rfin_k →+* L // ψ|_k = σ}`;
--     `card_fiber_eq`: a fiber is `Hom_k(Rfin_k, L)` for the algebra structure `σ` on `L`.
--   * `card_algHom_Rinf_le'`: homs out of `Rinf` kill `1/x`, so `#Hom_Fq(Rinf, L)` is bounded independently of `L`.
--
--   **Formalization note.** Library module of a formalization of the Ramanujan-Petersson conjecture in weight two (Eichler-Shimura-Ihara route: the Eichler-Selberg trace formula on $S_2(\Gamma_1(M))$, the Deuring-Waterhouse-Schoof count of elliptic curves over $\mathbb F_q$ with level structure by Hurwitz class numbers, conditional on Tate's isogeny theorem in prime-to-$p$ form, the Kronecker-Hurwitz class number relation, and the Hasse-Weil bound for the components of $Y_1(M)$ by the Stepanov-Bombieri method). It contains definitions together with proved lemmas (no `sorry`; where Tate's theorem is used it is an explicit hypothesis), so that later solution files can import them.
-- source:
--   H. Stichtenoth, Algebraic Function Fields and Codes, 2nd ed., GTM 254, Springer 2009, Chapters 1 and 5; E. Bombieri, Counting points on curves over finite fields (d'après S. A. Stepanov), Séminaire Bourbaki 430 (1973); A. Weil, Sur les courbes algébriques et les variétés qui s'en déduisent, Hermann 1948

import Mathlib
import Definitions.Def_RPLib_S3_X1CountB

/-!
# S3-Wt2RP, O2 part A: a function field over `Fq` and over a finite field of constants `k ⊆ F`

Generic comparison, for `Fq ⊆ k ⊆ F` with `k` integral over `Fq` and the same coordinate
`x = algebraMap Fq[X] F X = algebraMap k[X] F X`:
* `algebraMap_poly_eq`: `Fq[X] → F` factors through `k[X]` (coefficientwise map).
* `isIntegral_poly_iff`: integral over `Fq[X]` iff integral over `k[X]`; `rfinEquiv`: the two rings `Rfin` agree.
* `homSigmaEquiv`: `Hom_Fq(Rfin_Fq, L) ≃ Σ (σ : k →ₐ[Fq] L), {ψ : Rfin_k →+* L // ψ|_k = σ}`;
  `card_fiber_eq`: a fiber is `Hom_k(Rfin_k, L)` for the algebra structure `σ` on `L`.
* `card_algHom_Rinf_le'`: homs out of `Rinf` kill `1/x`, so `#Hom_Fq(Rinf, L)` is bounded independently of `L`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open Polynomial

namespace RamanujanPetersson.S3.Wt2

open RamanujanPetersson.Places

section RinfGeneric

variable (Fq : Type) [Field Fq] [Fintype Fq] [DecidableEq (RatFunc Fq)]
variable (F : Type) [Field F] [Algebra Fq F] [Algebra Fq[X] F] [Algebra (RatFunc Fq) F]
  [IsScalarTower Fq[X] (RatFunc Fq) F] [IsScalarTower Fq Fq[X] F] [FunctionField Fq F]
  [Algebra.IsSeparable (RatFunc Fq) F]

/-- Homs out of `Rinf` kill `1/x` (generic form of `X1Count.card_algHom_Rinf_le`). -/
theorem card_algHom_Rinf_le' (L : Type) [Field L] [Finite L] [Algebra Fq L] :
    Nat.card (Rinf Fq F →ₐ[Fq] L) ≤
      Module.finrank Fq (Rinf Fq F ⧸ Ideal.span {algebraMap (Oinf Fq) (Rinf Fq F) (piInf Fq)}) := by
  set π' := algebraMap (Oinf Fq) (Rinf Fq F) (piInf Fq)
  have hπ : π' ≠ 0 := by
    rw [Ne, ← map_zero (algebraMap (Oinf Fq) (Rinf Fq F)), (algebraMap_Oinf_Rinf_injective Fq F).eq_iff]
    exact piInf_ne_zero Fq
  have : Finite (Rinf Fq F ⧸ Ideal.span {π'}) := FiniteQuot.finite _ hπ
  have hkill : ∀ ψ : Rinf Fq F →ₐ[Fq] L, ψ π' = 0 := by
    intro ψ
    have : Fintype L := Fintype.ofFinite L
    set Q := Fintype.card L with hQ
    have hQ1 : 1 ≤ Q := Fintype.card_pos
    have hu : IsUnit (ψ (π' ^ (Q - 1) - 1)) := by
      have := (X1Count.isUnit_piInf_pow_sub_one (k := Fq) (n := Q - 1) (by
        have : 2 ≤ Q := by
          have := Fintype.one_lt_card (α := L)
          omega
        omega)).map (algebraMap (Oinf Fq) (Rinf Fq F))
      rw [map_sub, map_pow, map_one] at this
      exact this.map ψ
    have hF : ψ π' ^ Q = ψ π' := FiniteField.pow_card _
    have h0 : ψ π' * ψ (π' ^ (Q - 1) - 1) = 0 := by
      rw [map_sub, map_pow, map_one, mul_sub, mul_one, ← pow_succ', Nat.sub_add_cancel hQ1, hF, sub_self]
    exact (mul_eq_zero.mp h0).resolve_right hu.ne_zero
  calc Nat.card (Rinf Fq F →ₐ[Fq] L) = Nat.card {ψ : Rinf Fq F →ₐ[Fq] L // ψ π' = 0} :=
        (Nat.card_congr (Equiv.subtypeUnivEquiv hkill)).symm
    _ ≤ _ := X1Count.card_kill_le π'

end RinfGeneric

section Compare

variable (Fq : Type) [Field Fq] (F : Type) [Field F] [Algebra Fq F] [Algebra Fq[X] F]
  [IsScalarTower Fq Fq[X] F]
variable (k : Type) [Field k] [Algebra k F] [Algebra k[X] F] [IsScalarTower k k[X] F]
  [Algebra Fq k] [IsScalarTower Fq k F]

/-- `Fq[X] → F` factors through `k[X]` when the coordinates agree. -/
theorem algebraMap_poly_eq (hx : algebraMap k[X] F X = algebraMap Fq[X] F X) :
    algebraMap Fq[X] F = (algebraMap k[X] F).comp (mapRingHom (algebraMap Fq k)) := by
  refine Polynomial.ringHom_ext (fun a => ?_) ?_
  · have h1 : algebraMap Fq[X] F (C a) = algebraMap Fq F a := by
      rw [IsScalarTower.algebraMap_apply Fq Fq[X] F, Polynomial.algebraMap_eq]
    have h2 : algebraMap k[X] F (C (algebraMap Fq k a)) = algebraMap Fq F a := by
      rw [IsScalarTower.algebraMap_apply Fq k F, IsScalarTower.algebraMap_apply k k[X] F, Polynomial.algebraMap_eq]
    rw [RingHom.comp_apply, coe_mapRingHom, map_C, h1, h2]
  · rw [RingHom.comp_apply, coe_mapRingHom, map_X, hx]

variable [Algebra.IsIntegral Fq k]

/-- Constants of `k` are integral over `Fq[X]`. -/
theorem isIntegral_const (c : k) : IsIntegral Fq[X] (algebraMap k F c) :=
  ((Algebra.IsIntegral.isIntegral (R := Fq) c).algebraMap (B := F)).tower_top

/-- Integral over `Fq[X]` iff integral over `k[X]`. -/
theorem isIntegral_poly_iff (hx : algebraMap k[X] F X = algebraMap Fq[X] F X) (f : F) :
    IsIntegral Fq[X] f ↔ IsIntegral k[X] f := by
  have hcomp := algebraMap_poly_eq Fq F k hx
  constructor
  · rintro ⟨P, hP, hev⟩
    refine ⟨P.map (mapRingHom (algebraMap Fq k)), hP.map _, ?_⟩
    rw [eval₂_map, ← hcomp]
    exact hev
  · intro h
    set S := integralClosure Fq[X] F with hS
    have hmem : ∀ p : k[X], algebraMap k[X] F p ∈ S := by
      intro p
      induction p using Polynomial.induction_on' with
      | add p q hp hq => rw [map_add]; exact S.add_mem hp hq
      | monomial n a =>
        rw [← C_mul_X_pow_eq_monomial, map_mul, map_pow]
        refine S.mul_mem ?_ (S.pow_mem ?_ n)
        · have e : algebraMap k[X] F (C a) = algebraMap k F a := by
            rw [IsScalarTower.algebraMap_apply k k[X] F, Polynomial.algebraMap_eq]
          rw [e]
          exact (isIntegral_const Fq F k a : _)
        · rw [hx]
          exact (isIntegral_algebraMap : IsIntegral Fq[X] (algebraMap Fq[X] F X))
    let ψ : k[X] →+* S := (algebraMap k[X] F).codRestrict S hmem
    have hψ : (algebraMap S F).comp ψ = algebraMap k[X] F := RingHom.ext fun _ => rfl
    have hSf : IsIntegral S f := by
      obtain ⟨P, hP, hev⟩ := h
      refine ⟨P.map ψ, hP.map _, ?_⟩
      rw [eval₂_map, hψ]
      exact hev
    exact isIntegral_trans f hSf

/-- The two rings of finite integers are the same subring of `F`. -/
def rfinEquiv (hx : algebraMap k[X] F X = algebraMap Fq[X] F X) :
    FunctionField.ringOfIntegers Fq F ≃+* FunctionField.ringOfIntegers k F where
  toFun a := ⟨a.1, (isIntegral_poly_iff Fq F k hx a.1).1 a.2⟩
  invFun b := ⟨b.1, (isIntegral_poly_iff Fq F k hx b.1).2 b.2⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_mul' _ _ := rfl
  map_add' _ _ := rfl

/-- Constants are regular at the finite places. -/
noncomputable def constRfin : k →ₐ[Fq] FunctionField.ringOfIntegers Fq F where
  toFun c := ⟨algebraMap k F c, isIntegral_const Fq F k c⟩
  map_one' := Subtype.ext (map_one _)
  map_mul' a b := Subtype.ext (map_mul _ a b)
  map_zero' := Subtype.ext (map_zero _)
  map_add' a b := Subtype.ext (map_add _ a b)
  commutes' a := Subtype.ext (IsScalarTower.algebraMap_apply Fq k F a).symm

variable (L : Type) [Field L] [Algebra Fq L]

/-- `Hom_Fq(Rfin_Fq, L)` splits over the embeddings of the constants. -/
noncomputable def homSigmaEquiv (hx : algebraMap k[X] F X = algebraMap Fq[X] F X) :
    (FunctionField.ringOfIntegers Fq F →ₐ[Fq] L) ≃
      Σ σ : k →ₐ[Fq] L, {ψ : FunctionField.ringOfIntegers k F →+* L //
        ∀ c, ψ (algebraMap k (FunctionField.ringOfIntegers k F) c) = σ c} where
  toFun φ := ⟨φ.comp (constRfin Fq F k),
    ⟨φ.toRingHom.comp (rfinEquiv Fq F k hx).symm.toRingHom, fun c => congrArg φ (Subtype.ext rfl)⟩⟩
  invFun s :=
    { toRingHom := s.2.1.comp (rfinEquiv Fq F k hx).toRingHom
      commutes' := fun a => by
        have h : (rfinEquiv Fq F k hx) (algebraMap Fq _ a) =
            algebraMap k (FunctionField.ringOfIntegers k F) (algebraMap Fq k a) :=
          Subtype.ext (IsScalarTower.algebraMap_apply Fq k F a)
        show s.2.1 ((rfinEquiv Fq F k hx) (algebraMap Fq _ a)) = _
        rw [h, s.2.2, AlgHom.commutes] }
  left_inv φ := AlgHom.ext fun x => congrArg φ ((rfinEquiv Fq F k hx).symm_apply_apply x)
  right_inv s := by
    obtain ⟨σ, ψ, hψ⟩ := s
    refine Sigma.subtype_ext (AlgHom.ext fun c => ?_) (RingHom.ext fun x => ?_)
    · show ψ ((rfinEquiv Fq F k hx) (constRfin Fq F k c)) = σ c
      rw [← hψ c]
      exact congrArg ψ (Subtype.ext rfl)
    · show ψ ((rfinEquiv Fq F k hx) ((rfinEquiv Fq F k hx).symm x)) = ψ x
      rw [RingEquiv.apply_symm_apply]

/-- A fiber of `homSigmaEquiv` is `Hom_k(Rfin_k, L)` for the algebra structure `σ` on `L`. -/
theorem card_fiber_eq (σ : k →ₐ[Fq] L) [Algebra k L] (hσ : ∀ c, algebraMap k L c = σ c) :
    Nat.card {ψ : FunctionField.ringOfIntegers k F →+* L //
      ∀ c, ψ (algebraMap k (FunctionField.ringOfIntegers k F) c) = σ c} =
      Nat.card (FunctionField.ringOfIntegers k F →ₐ[k] L) :=
  Nat.card_congr
    { toFun := fun ψ => { toRingHom := ψ.1, commutes' := fun c => (ψ.2 c).trans (hσ c).symm }
      invFun := fun φ => ⟨φ.toRingHom, fun c => (φ.commutes c).trans (hσ c)⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }

end Compare

end RamanujanPetersson.S3.Wt2


