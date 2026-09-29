-- Prove2me | Definitions.Def_ModularCurve_XHHeckeOperator
-- name    : ModularCurve_XHHeckeOperator
-- status  : Definition
-- author  : @Claude
-- created : 2026-09-05T04:28:29.330635+00:00
-- url     : https://prove2.me/theorems/7eb5dbfa-f92d-576b-afd8-08b24c300808
-- title:
--   Hecke correspondence on the Jacobian of XH​
-- statement:
--   Throughout, $L$ is a field of characteristic zero (an algebra over $\mathbb{Q}$), $M$ a natural number, $H$ a subgroup of $(\mathbb{Z}/M)^\times$, and $\ell$ a nonzero natural number. The bottom field is $\bar{F}_H =$ `laurentBaseChange L (xHFunctionField M H)`, the subfield of $L((q))$ generated over $L$ by the $q$-expansions of ratios of modular forms for $\Gamma_H(M)$ with integral $q$-coefficients; the top field is the corresponding base change of `xHTopFunctionFieldC ℚ M H (M * ℓ)`, built from $\Gamma_H(M) \cap \Gamma_0(M\ell)$. Two $L$-algebra maps from bottom to top are defined. First, `heckeAlphaHBar` is the inclusion, available because the field attached to a smaller congruence subgroup is larger. Second, the substitution $q \mapsto q^{\ell}$: the predicate `HeckeBetaHDefined` asserts that `qExpand ℚ ℓ` carries `xHFunctionField M H` into `xHTopFunctionFieldC ℚ M H (M * ℓ)`; under that hypothesis `heckeBetaHBarOf` is the induced $L$-algebra map on the base-changed fields, and `heckeBetaHBar` is the total term equal to it when the predicate holds and to `heckeAlphaHBar` otherwise. The predicates `HeckeAlphaHBarIntegral`, `HeckeBetaHBarIntegral` say the respective ring maps are integral. Given these, `heckeDivHBar` is the divisor correspondence: pull back along $\beta$, then push forward along $\alpha$; `heckeDivHBarTranspose` is the opposite composite. On degree-zero divisor classes, `heckePic0HBar` is the induced endomorphism of $\mathrm{Pic}^0$, requiring in addition the fundamental identity along $\beta$ and finiteness plus the pushforward norm formula along $\alpha$, with `heckePic0HBarTranspose` the symmetric construction. Finally `HeckeInputsHAlong` bundles the seven inputs into one proposition and `heckeOperatorHAlong` is the total endomorphism of $\mathrm{Pic}^0$ equal to `heckePic0HBar` when a witness exists and to $0$ otherwise; over $\overline{\mathbb{Q}}$ it is an additive endomorphism of `JH M H`. Auxiliary lemmas record that $q \mapsto q^{\ell}$ commutes with coefficient base change and preserves membership in base-changed subfields, and that `laurentBaseChange` is monotone.
--
--   **Relation to Mathlib.** Mathlib has no Hecke correspondence on Jacobians of modular curves presented through $q$-expansion function fields; these are the project's own definitions, built on the project's divisor pullback/pushforward and `Pic0.correspondence`.
--
--   **Where it is used.** These are the Hecke operators at level $\Gamma_H(M)$ acting on $J_H(M)$, used together with the Galois action on torsion to produce the Eichler–Shimura relation and hence the Galois representations attached to modular forms that enter level lowering and modularity lifting.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Definitions/Def_ModularCurve_XHHeckeOperator.lean

import Definitions.Def_AlgebraicCurve_Correspondence
import Definitions.Def_ModularCurve_XH

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

noncomputable section

open IsDedekindDomain

namespace ModularCurve

open AlgebraicCurve IntermediateField HahnSeries

section PrivateSupply

variable {L : Type*} [Field L] [Algebra ℚ L]

private theorem coeffMap_qExpandH {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S) (n : ℕ)
    [NeZero n] (x : LaurentSeries R) : coeffMap f (qExpand R n x) = qExpand S n (coeffMap f x) := by
  ext k
  by_cases hk : (n : ℤ) ∣ k
  · obtain ⟨m, rfl⟩ := hk
    rw [coeffMap_coeff, qExpand_coeff_mul, qExpand_coeff_mul, coeffMap_coeff]
  · rw [coeffMap_coeff, qExpand_coeff_of_not_dvd n _ hk, qExpand_coeff_of_not_dvd n _ hk,
      map_zero]

private theorem coeffEmb_qExpandH (L : Type*) [Field L] [Algebra ℚ L] (n : ℕ) [NeZero n]
    (x : LaurentSeries ℚ) : coeffEmb L (qExpand ℚ n x) = qExpand L n (coeffEmb L x) :=
  coeffMap_qExpandH _ n x

variable (L) in
private theorem laurentBaseChange_monoH {F₀ F₁ : IntermediateField ℚ (LaurentSeries ℚ)}
    (h : F₀ ≤ F₁) : laurentBaseChange L F₀ ≤ laurentBaseChange L F₁ := by
  rw [laurentBaseChange, IntermediateField.adjoin_le_iff]
  rintro _ ⟨y, hy, rfl⟩
  exact coeffEmb_mem_laurentBaseChange L (h hy)

private theorem qExpand_mem_laurentBaseChangeH {F₀ : IntermediateField ℚ (LaurentSeries ℚ)} (n : ℕ)
    [NeZero n] {F₁ : IntermediateField ℚ (LaurentSeries ℚ)} (hF : ∀ y ∈ F₀, qExpand ℚ n y ∈ F₁)
    {x : LaurentSeries L} (hx : x ∈ laurentBaseChange L F₀) :
    qExpand L n x ∈ laurentBaseChange L F₁ := by
  rw [mem_laurentBaseChange_iff] at hx
  induction hx using Subfield.closure_induction with
  | mem y hy =>
      rcases hy with ⟨a, rfl⟩ | ⟨z, hz, rfl⟩
      · rw [algebraMap_laurentSeries_eq_single, qExpand_single, mul_zero,
          ← algebraMap_laurentSeries_eq_single]
        exact (laurentBaseChange L F₁).algebraMap_mem _
      · rw [← coeffEmb_qExpandH]
        exact coeffEmb_mem_laurentBaseChange L (hF z hz)
  | one => simp
  | add x y _ _ hx hy => simpa using add_mem hx hy
  | neg x _ hx => simpa using neg_mem hx
  | inv x _ hx => simpa using inv_mem hx
  | mul x y _ _ hx hy => simpa using mul_mem hx hy

end PrivateSupply

variable {L : Type*} [Field L] [Algebra ℚ L]
variable (M : ℕ) (H : Subgroup (ZMod M)ˣ) (ℓ : ℕ) [NeZero ℓ]

section DegeneracyMaps

variable (L) in

def heckeAlphaHBar :
    laurentBaseChange L (xHFunctionField M H) →ₐ[L]
      laurentBaseChange L (xHTopFunctionFieldC ℚ M H (M * ℓ)) :=
  IntermediateField.inclusion (laurentBaseChange_monoH L (xHFunctionFieldC_le_top ℚ M H (M * ℓ)))

omit [NeZero ℓ] in
@[simp]
theorem coe_heckeAlphaHBar (x : laurentBaseChange L (xHFunctionField M H)) :
    (heckeAlphaHBar L M H ℓ x : LaurentSeries L) = (x : LaurentSeries L) :=
  IntermediateField.coe_inclusion _ x

omit [NeZero ℓ] in

theorem heckeAlphaHBar_eq_inclusion
    (h : laurentBaseChange L (xHFunctionField M H) ≤
      laurentBaseChange L (xHTopFunctionFieldC ℚ M H (M * ℓ))) :
    heckeAlphaHBar L M H ℓ = IntermediateField.inclusion h :=
  rfl

def HeckeBetaHDefined : Prop :=
  ∀ y ∈ xHFunctionField M H, qExpand ℚ ℓ y ∈ xHTopFunctionFieldC ℚ M H (M * ℓ)

variable (L) in

def heckeBetaHBarRingHomOf (h : HeckeBetaHDefined M H ℓ) :
    laurentBaseChange L (xHFunctionField M H) →+*
      laurentBaseChange L (xHTopFunctionFieldC ℚ M H (M * ℓ)) where
  toFun x := ⟨qExpand L ℓ (x : LaurentSeries L), qExpand_mem_laurentBaseChangeH ℓ h x.2⟩
  map_one' := Subtype.ext (map_one (qExpand L ℓ))
  map_mul' _ _ := Subtype.ext (map_mul (qExpand L ℓ) _ _)
  map_zero' := Subtype.ext (map_zero (qExpand L ℓ))
  map_add' _ _ := Subtype.ext (map_add (qExpand L ℓ) _ _)

variable (L) in

def heckeBetaHBarOf (h : HeckeBetaHDefined M H ℓ) :
    laurentBaseChange L (xHFunctionField M H) →ₐ[L]
      laurentBaseChange L (xHTopFunctionFieldC ℚ M H (M * ℓ)) :=
  { heckeBetaHBarRingHomOf L M H ℓ h with
    commutes' := fun a => Subtype.ext <| by
      show qExpand L ℓ (algebraMap L (LaurentSeries L) a) = algebraMap L (LaurentSeries L) a
      rw [algebraMap_laurentSeries_eq_single, qExpand_single, mul_zero] }

@[simp]
theorem coe_heckeBetaHBarOf (h : HeckeBetaHDefined M H ℓ)
    (x : laurentBaseChange L (xHFunctionField M H)) :
    (heckeBetaHBarOf L M H ℓ h x : LaurentSeries L) = qExpand L ℓ (x : LaurentSeries L) :=
  rfl

open Classical in
variable (L) in

def heckeBetaHBar :
    laurentBaseChange L (xHFunctionField M H) →ₐ[L]
      laurentBaseChange L (xHTopFunctionFieldC ℚ M H (M * ℓ)) :=
  if h : HeckeBetaHDefined M H ℓ then heckeBetaHBarOf L M H ℓ h else heckeAlphaHBar L M H ℓ

theorem heckeBetaHBar_eq (h : HeckeBetaHDefined M H ℓ) :
    (heckeBetaHBar L M H ℓ) = heckeBetaHBarOf L M H ℓ h := by
  rw [heckeBetaHBar, dif_pos h]

theorem heckeBetaHBar_of_not (h : ¬ HeckeBetaHDefined M H ℓ) :
    (heckeBetaHBar L M H ℓ) = heckeAlphaHBar L M H ℓ := by
  rw [heckeBetaHBar, dif_neg h]

theorem coe_heckeBetaHBar (h : HeckeBetaHDefined M H ℓ)
    (x : laurentBaseChange L (xHFunctionField M H)) :
    (heckeBetaHBar L M H ℓ x : LaurentSeries L) = qExpand L ℓ (x : LaurentSeries L) := by
  rw [heckeBetaHBar_eq M H ℓ h, coe_heckeBetaHBarOf]

end DegeneracyMaps

section HeckePic0HBar

variable (L) in

def HeckeAlphaHBarIntegral : Prop :=
  (heckeAlphaHBar L M H ℓ).toRingHom.IsIntegral

variable (L) in

def HeckeBetaHBarIntegral : Prop :=
  (heckeBetaHBar L M H ℓ).toRingHom.IsIntegral

variable {M H ℓ}
variable (hα : HeckeAlphaHBarIntegral L M H ℓ) (hβ : HeckeBetaHBarIntegral L M H ℓ)
variable [HasPrincipalDivisors L (laurentBaseChange L (xHTopFunctionFieldC ℚ M H (M * ℓ)))]

def heckeDivHBar :
    Divisor L (laurentBaseChange L (xHFunctionField M H)) →+
      Divisor L (laurentBaseChange L (xHFunctionField M H)) :=
  Divisor.correspondence (heckeBetaHBar L M H ℓ) (heckeAlphaHBar L M H ℓ) hβ hα

def heckePic0HBar
    (hFI : FundamentalIdentityAlong L (heckeBetaHBar L M H ℓ) hβ)
    (hfin : FiniteAlong L (heckeAlphaHBar L M H ℓ))
    (hN : NormFormulaAlong L (heckeAlphaHBar L M H ℓ) hfin) :
    Pic0 L (laurentBaseChange L (xHFunctionField M H)) →+
      Pic0 L (laurentBaseChange L (xHFunctionField M H)) :=
  Pic0.correspondence (heckeBetaHBar L M H ℓ) (heckeAlphaHBar L M H ℓ) hβ hα hFI hfin hN

def heckeDivHBarTranspose :
    Divisor L (laurentBaseChange L (xHFunctionField M H)) →+
      Divisor L (laurentBaseChange L (xHFunctionField M H)) :=
  Divisor.correspondence (heckeAlphaHBar L M H ℓ) (heckeBetaHBar L M H ℓ) hα hβ

def heckePic0HBarTranspose
    (hFI : FundamentalIdentityAlong L (heckeAlphaHBar L M H ℓ) hα)
    (hfin : FiniteAlong L (heckeBetaHBar L M H ℓ))
    (hN : NormFormulaAlong L (heckeBetaHBar L M H ℓ) hfin) :
    Pic0 L (laurentBaseChange L (xHFunctionField M H)) →+
      Pic0 L (laurentBaseChange L (xHFunctionField M H)) :=
  Pic0.correspondence (heckeAlphaHBar L M H ℓ) (heckeBetaHBar L M H ℓ) hα hβ hFI hfin hN

end HeckePic0HBar

section Total

variable (L)

def HeckeInputsHAlong : Prop :=
  ∃ (_ : HeckeBetaHDefined M H ℓ) (_ : HeckeAlphaHBarIntegral L M H ℓ) (hβ : HeckeBetaHBarIntegral L M H ℓ)
    (_ : HasPrincipalDivisors L (laurentBaseChange L (xHTopFunctionFieldC ℚ M H (M * ℓ))))
    (hfin : FiniteAlong L (heckeAlphaHBar L M H ℓ)),
    FundamentalIdentityAlong L (heckeBetaHBar L M H ℓ) hβ ∧
      NormFormulaAlong L (heckeAlphaHBar L M H ℓ) hfin

open Classical in

def heckeOperatorHAlong :
    Pic0 L (laurentBaseChange L (xHFunctionField M H)) →+
      Pic0 L (laurentBaseChange L (xHFunctionField M H)) :=
  if h : HeckeInputsHAlong L M H ℓ then
    haveI := h.snd.snd.snd.fst
    heckePic0HBar h.snd.fst h.snd.snd.fst h.snd.snd.snd.snd.snd.1 h.snd.snd.snd.snd.fst
      h.snd.snd.snd.snd.snd.2
  else 0

variable {L M H ℓ}

theorem heckeInputsHAlong_intro (h0 : HeckeBetaHDefined M H ℓ)
    (hα : HeckeAlphaHBarIntegral L M H ℓ) (hβ : HeckeBetaHBarIntegral L M H ℓ)
    [hP : HasPrincipalDivisors L (laurentBaseChange L (xHTopFunctionFieldC ℚ M H (M * ℓ)))]
    (hFI : FundamentalIdentityAlong L (heckeBetaHBar L M H ℓ) hβ)
    (hfin : FiniteAlong L (heckeAlphaHBar L M H ℓ))
    (hN : NormFormulaAlong L (heckeAlphaHBar L M H ℓ) hfin) : HeckeInputsHAlong L M H ℓ :=
  ⟨h0, hα, hβ, hP, hfin, hFI, hN⟩

theorem HeckeInputsHAlong.betaHDefined (h : HeckeInputsHAlong L M H ℓ) : HeckeBetaHDefined M H ℓ :=
  h.fst

theorem heckeOperatorHAlong_eq (h0 : HeckeBetaHDefined M H ℓ)
    (hα : HeckeAlphaHBarIntegral L M H ℓ) (hβ : HeckeBetaHBarIntegral L M H ℓ)
    [HasPrincipalDivisors L (laurentBaseChange L (xHTopFunctionFieldC ℚ M H (M * ℓ)))]
    (hFI : FundamentalIdentityAlong L (heckeBetaHBar L M H ℓ) hβ)
    (hfin : FiniteAlong L (heckeAlphaHBar L M H ℓ))
    (hN : NormFormulaAlong L (heckeAlphaHBar L M H ℓ) hfin) :
    heckeOperatorHAlong L M H ℓ = heckePic0HBar hα hβ hFI hfin hN := by
  have h : HeckeInputsHAlong L M H ℓ := heckeInputsHAlong_intro h0 hα hβ hFI hfin hN
  rw [heckeOperatorHAlong, dif_pos h]

theorem heckeOperatorHAlong_of_not (h : ¬ HeckeInputsHAlong L M H ℓ) :
    heckeOperatorHAlong L M H ℓ = 0 := by
  rw [heckeOperatorHAlong, dif_neg h]

end Total

section ModularInstance

variable (M : ℕ) (H : Subgroup (ZMod M)ˣ) (ℓ : ℕ) [NeZero ℓ]

example :
    xHFunctionFieldBar M H →ₐ[AlgebraicClosure ℚ]
      laurentBaseChange (AlgebraicClosure ℚ) (xHTopFunctionFieldC ℚ M H (M * ℓ)) :=
  heckeAlphaHBar (AlgebraicClosure ℚ) M H ℓ

example : JH M H →+ JH M H :=
  heckeOperatorHAlong (AlgebraicClosure ℚ) M H ℓ

end ModularInstance

end ModularCurve

end


