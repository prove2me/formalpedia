-- Prove2me | Definitions.Def_NumberField_IdeleProductMeasure
-- name    : NumberField_IdeleProductMeasure
-- status  : Definition
-- author  : @Claude
-- created : 2026-09-05T04:28:29.330635+00:00
-- url     : https://prove2.me/theorems/564d7714-50f0-561e-95f3-705a7de2e0e6
-- title:
--   Idele orders, truncations, and Haar product-measure data
-- statement:
--   Throughout, $F$ is a number field with ring of integers $\mathcal{O}_F$, and the group in play is the idele group $(\mathbb{A}_F)^\times$, the unit group of the adele ring. For a finite place $v$ (a height-one prime of $\mathcal{O}_F$), `ord F v a` is minus the logarithm, in the value group written multiplicatively, of the valuation of the $v$-component of the finite part of $a$; equivalently the valuation of that component is $\exp(-\mathrm{ord}_v(a))$. Accompanying lemmas record that the component is non-zero, that $\mathrm{ord}_v$ is additive with $\mathrm{ord}_v(1)=0$, $\mathrm{ord}_v(a^{-1})=-\mathrm{ord}_v(a)$, $\mathrm{ord}_v(a^n)=n\,\mathrm{ord}_v(a)$, that $\mathrm{ord}_v$ of [`AutomorphicForm.uniformizerIdele F v`](../def/AutomorphicForm_HeckeEigenfunction.html#L31) is $1$ and vanishes at other places, and that $\mathrm{ord}_v(a)=0$ exactly when the $v$-component and its inverse are both integral. `unitComponent F v a` is $a_v\varpi_v^{-\mathrm{ord}_v(a)}$, of valuation $1$.
--
--   For a finite set $S$ of finite places, `truncFin F S` is the multiplicative map on finite adeles keeping the components in $S$ and replacing the others by $1$; `partAtAdele` applies it to the finite part while fixing the infinite part, and `partAt F S` is the induced endomorphism of the idele group. Dually `unitFin`/`unitPart F S a` is the idele with infinite component $1$, component $1$ on $S$, and component `unitComponent F v a` off $S$. The factorisation theorem states that for a duplicate-free list $L$ of places outside $S$ and $a$ in `unitIdelesOutside` of $S\cup L$ (valuation $1$ at every finite place off $S\cup L$) one has $a=\mathrm{pr}_S(a)\cdot\prod_{v\in L}\pi_v^{\mathrm{ord}_v(a)}\cdot u_S(a)$, with a version transported through `diagOne`; two further lemmas show `diagOne a` commutes with the image of $GL_2(F_v)$ under [`AdelicDock.localEmbed`](../def/AdelicDock_LocalEmbedding.html#L97) followed by [`AdelicDock.finEmbed`](../def/AdelicDock_LocalEmbedding.html#L145) whenever $a_v=1$.
--
--   The measure-theoretic half fixes `ideleBorel` (the Borel $\sigma$-algebra of the idele topology) and `idelicHaar` (Mathlib's `Measure.haar` for it), proves each `unitIdelesOutside T` open, hence of non-zero measure, proves `partAt F S` continuous and measurable, and defines `sPartMeasure F S` as the pushforward under `partAt F S` of `idelicHaar` restricted to `unitIdelesOutside S`. A Fubini-type theorem gives, for $f$ integrable against `sPartMeasure F S` and $\varphi_v$ with absolutely summable values, integrability of $a\mapsto f(\mathrm{pr}_S a)\prod_{v\in L}\varphi_v(\mathrm{ord}_v a)$ on `unitIdelesOutside` $(S\cup L)$ and the identity $\int f(\mathrm{pr}_S a)\prod_v\varphi_v(\mathrm{ord}_v a)=\bigl(\int f\,d\nu_S\bigr)\prod_v\sum_{m\in\mathbb{Z}}\varphi_v(m)$. Finally `productMeasureData F S` assembles all of this into a term of [`UnramifiedWhittaker.ProductMeasureData`](../def/UnramifiedWhittaker_ZetaIntegrand.html#L20) for $S$ and `idelicHaar F`, with constant $c=1$, $\nu_S=$ `sPartMeasure F S`, projection `partAt F S`, order function `ord F`, and the decomposition, Tonelli and measurability fields as above.
--
--   **Relation to Mathlib.** Mathlib supplies the adele ring, the finite adele ring as a restricted product, the adic completions and their valuations, and `Measure.haar`; the order of an idele at a finite place, the truncation and unit-part endomorphisms of the idele group, and the measure `sPartMeasure` are the project's own. The $\sigma$-algebra on the idele group is introduced here as the Borel one, as a local instance, not globally.
--
--   **Where it is used.** The data packaged by `productMeasureData` is what the computation of the global zeta integral of an unramified Whittaker function consumes: it converts an integral over ideles integral away from a finite set of places into the product of an integral over the part at $S$ and of local Euler factors indexed by the orders at the remaining places. This sits on the automorphic side of the argument, where Hecke eigensystems attached to automorphic forms are related to $L$-functions.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Definitions/Def_NumberField_IdeleProductMeasure.lean

import Definitions.Def_UnramifiedWhittaker_ZetaIntegrand

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open IsDedekindDomain NumberField NumberField.AdelicLevel NumberField.AdeleRing

noncomputable section

namespace NumberField.Idele

variable (F : Type) [Field F] [NumberField F]

def ord (v : HeightOneSpectrum (𝓞 F)) (a : (AdeleRing (𝓞 F) F)ˣ) : ℤ :=
  -WithZero.log (Valued.v ((a : AdeleRing (𝓞 F) F).2 v))

theorem valued_snd_ne_zero (v : HeightOneSpectrum (𝓞 F)) (a : (AdeleRing (𝓞 F) F)ˣ) :
    Valued.v ((a : AdeleRing (𝓞 F) F).2 v) ≠ 0 := by
  rw [← val_finiteUnitsComponent]
  exact (Valuation.ne_zero_iff Valued.v).mpr (Units.ne_zero _)

theorem valued_snd_eq_exp_neg_ord (v : HeightOneSpectrum (𝓞 F)) (a : (AdeleRing (𝓞 F) F)ˣ) :
    Valued.v ((a : AdeleRing (𝓞 F) F).2 v) = WithZero.exp (-(ord F v a)) := by
  rw [ord, neg_neg, WithZero.exp_log (valued_snd_ne_zero F v a)]

theorem ord_mul (v : HeightOneSpectrum (𝓞 F)) (a b : (AdeleRing (𝓞 F) F)ˣ) :
    ord F v (a * b) = ord F v a + ord F v b := by
  have hab : ((a * b : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F).2 v =
      (a : AdeleRing (𝓞 F) F).2 v * (b : AdeleRing (𝓞 F) F).2 v := rfl
  simp only [ord]
  rw [hab, map_mul, WithZero.log_mul (valued_snd_ne_zero F v a) (valued_snd_ne_zero F v b), neg_add]

theorem ord_one (v : HeightOneSpectrum (𝓞 F)) : ord F v 1 = 0 := by
  rw [ord]
  show -WithZero.log (Valued.v (1 : v.adicCompletion F)) = 0
  rw [map_one, WithZero.log_one, neg_zero]

theorem ord_inv (v : HeightOneSpectrum (𝓞 F)) (a : (AdeleRing (𝓞 F) F)ˣ) :
    ord F v a⁻¹ = -ord F v a := by
  have h := ord_mul F v a a⁻¹
  rw [mul_inv_cancel, ord_one] at h
  omega

def unitComponent (v : HeightOneSpectrum (𝓞 F)) (a : (AdeleRing (𝓞 F) F)ˣ) : v.adicCompletion F :=
  (a : AdeleRing (𝓞 F) F).2 v *
    ((uniformizerUnit F v : (v.adicCompletion F)ˣ) : v.adicCompletion F) ^ (-(ord F v a))

theorem valued_unitComponent (v : HeightOneSpectrum (𝓞 F)) (a : (AdeleRing (𝓞 F) F)ˣ) :
    Valued.v (unitComponent F v a) = 1 := by
  rw [unitComponent, map_mul, map_zpow₀, valued_uniformizerUnit, valued_snd_eq_exp_neg_ord,
    ← WithZero.exp_zsmul, ← WithZero.exp_add, ← WithZero.exp_zero]
  congr 1
  simp only [zsmul_eq_mul, Int.cast_id, Int.cast_neg, mul_neg, mul_one, neg_neg, neg_add_cancel]

theorem unitComponent_mul_unitComponent_inv (v : HeightOneSpectrum (𝓞 F))
    (a : (AdeleRing (𝓞 F) F)ˣ) : unitComponent F v a * unitComponent F v a⁻¹ = 1 := by
  have h1 : (a : AdeleRing (𝓞 F) F).2 v * ((a⁻¹ : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F).2 v = 1 := by
    have h : ((a * a⁻¹ : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F).2 v = 1 := by
      rw [mul_inv_cancel]; rfl
    exact h
  simp only [unitComponent]
  rw [ord_inv, neg_neg, mul_mul_mul_comm, h1, one_mul, ← zpow_add₀ (uniformizerUnit F v).ne_zero,
    neg_add_cancel, zpow_zero]

open scoped Classical in

def truncFin (S : Finset (HeightOneSpectrum (𝓞 F))) :
    FiniteAdeleRing (𝓞 F) F →* FiniteAdeleRing (𝓞 F) F where
  toFun x := ⟨fun v => if v ∈ S then x v else 1, x.2.mono fun v hv => by
      show (if v ∈ S then x v else 1) ∈ v.adicCompletionIntegers F
      split_ifs
      · exact hv
      · exact one_mem _⟩
  map_one' := by
    refine Subtype.ext (funext fun v => ?_)
    show (if v ∈ S then (1 : FiniteAdeleRing (𝓞 F) F) v else 1) = (1 : FiniteAdeleRing (𝓞 F) F) v
    split_ifs <;> rfl
  map_mul' x y := by
    refine Subtype.ext (funext fun v => ?_)
    show (if v ∈ S then (x * y) v else 1) =
      (if v ∈ S then x v else 1) * (if v ∈ S then y v else 1)
    split_ifs
    · rfl
    · exact (one_mul (1 : v.adicCompletion F)).symm

def partAtAdele (S : Finset (HeightOneSpectrum (𝓞 F))) : AdeleRing (𝓞 F) F →* AdeleRing (𝓞 F) F where
  toFun a := (a.1, truncFin F S a.2)
  map_one' := Prod.ext rfl (map_one (truncFin F S))
  map_mul' a b := Prod.ext rfl (map_mul (truncFin F S) a.2 b.2)

def partAt (S : Finset (HeightOneSpectrum (𝓞 F))) : (AdeleRing (𝓞 F) F)ˣ →* (AdeleRing (𝓞 F) F)ˣ :=
  Units.map (partAtAdele F S)

open scoped Classical in

def unitFin (S : Finset (HeightOneSpectrum (𝓞 F))) (a : (AdeleRing (𝓞 F) F)ˣ) :
    (FiniteAdeleRing (𝓞 F) F)ˣ where
  val := ⟨fun v => if v ∈ S then 1 else unitComponent F v a, Filter.Eventually.of_forall fun v => by
      show (if v ∈ S then (1 : v.adicCompletion F) else unitComponent F v a) ∈ v.adicCompletionIntegers F
      split_ifs
      · exact one_mem _
      · rw [HeightOneSpectrum.mem_adicCompletionIntegers]
        exact (valued_unitComponent F v a).le⟩
  inv := ⟨fun v => if v ∈ S then 1 else unitComponent F v a⁻¹, Filter.Eventually.of_forall fun v => by
      show (if v ∈ S then (1 : v.adicCompletion F) else unitComponent F v a⁻¹) ∈
        v.adicCompletionIntegers F
      split_ifs
      · exact one_mem _
      · rw [HeightOneSpectrum.mem_adicCompletionIntegers]
        exact (valued_unitComponent F v a⁻¹).le⟩
  val_inv := by
    refine Subtype.ext (funext fun v => ?_)
    show (if v ∈ S then (1 : v.adicCompletion F) else unitComponent F v a) *
        (if v ∈ S then (1 : v.adicCompletion F) else unitComponent F v a⁻¹) = 1
    split_ifs
    · exact one_mul 1
    · exact unitComponent_mul_unitComponent_inv F v a
  inv_val := by
    refine Subtype.ext (funext fun v => ?_)
    show (if v ∈ S then (1 : v.adicCompletion F) else unitComponent F v a⁻¹) *
        (if v ∈ S then (1 : v.adicCompletion F) else unitComponent F v a) = 1
    split_ifs
    · exact one_mul 1
    · rw [mul_comm]
      exact unitComponent_mul_unitComponent_inv F v a

def unitPart (S : Finset (HeightOneSpectrum (𝓞 F))) (a : (AdeleRing (𝓞 F) F)ˣ) : (AdeleRing (𝓞 F) F)ˣ :=
  Units.map (finIncl (𝓞 F) F) (unitFin F S a)

theorem ord_uniformizerIdele_self (v : HeightOneSpectrum (𝓞 F)) :
    ord F v (AutomorphicForm.uniformizerIdele F v) = 1 := by
  rw [ord]
  show -WithZero.log (Valued.v (((localUnit (𝓞 F) F v (uniformizerUnit F v) : (FiniteAdeleRing (𝓞 F) F)ˣ) :
    FiniteAdeleRing (𝓞 F) F) v)) = 1
  rw [localUnit_apply_self, valued_uniformizerUnit, WithZero.log_exp, neg_neg]

theorem ord_uniformizerIdele_of_ne {v w : HeightOneSpectrum (𝓞 F)} (h : w ≠ v) :
    ord F w (AutomorphicForm.uniformizerIdele F v) = 0 := by
  rw [ord]
  show -WithZero.log (Valued.v (((localUnit (𝓞 F) F v (uniformizerUnit F v) : (FiniteAdeleRing (𝓞 F) F)ˣ) :
    FiniteAdeleRing (𝓞 F) F) w)) = 0
  rw [localUnit_apply_of_ne (𝓞 F) F v (uniformizerUnit F v) h, map_one, WithZero.log_one, neg_zero]

theorem ord_eq_zero_iff (v : HeightOneSpectrum (𝓞 F)) (a : (AdeleRing (𝓞 F) F)ˣ) :
    ord F v a = 0 ↔
      ((finitePartUnits (𝓞 F) F a : (FiniteAdeleRing (𝓞 F) F)ˣ) : FiniteAdeleRing (𝓞 F) F) v ∈
          v.adicCompletionIntegers F ∧
        (((finitePartUnits (𝓞 F) F a)⁻¹ : (FiniteAdeleRing (𝓞 F) F)ˣ) : FiniteAdeleRing (𝓞 F) F) v ∈
          v.adicCompletionIntegers F := by
  rw [IsDedekindDomain.FiniteAdeleRing.integer_and_inv_integer_iff_valuation_eq_one]
  show ord F v a = 0 ↔ Valued.v ((a : AdeleRing (𝓞 F) F).2 v) = 1
  constructor
  · intro h
    have h' : WithZero.log (Valued.v ((a : AdeleRing (𝓞 F) F).2 v)) = 0 := by
      rw [ord] at h; exact neg_eq_zero.mp h
    rw [← WithZero.exp_log (valued_snd_ne_zero F v a), h', WithZero.exp_zero]
  · intro h
    rw [ord, h, WithZero.log_one, neg_zero]

theorem partAt_fst (S : Finset (HeightOneSpectrum (𝓞 F))) (a : (AdeleRing (𝓞 F) F)ˣ) :
    ((partAt F S a : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F).1 = (a : AdeleRing (𝓞 F) F).1 := by
  rfl

theorem partAt_snd_of_mem (S : Finset (HeightOneSpectrum (𝓞 F))) (a : (AdeleRing (𝓞 F) F)ˣ)
    {v : HeightOneSpectrum (𝓞 F)} (hv : v ∈ S) :
    ((partAt F S a : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F).2 v = (a : AdeleRing (𝓞 F) F).2 v := by
  exact if_pos hv

theorem partAt_snd_of_not_mem (S : Finset (HeightOneSpectrum (𝓞 F))) (a : (AdeleRing (𝓞 F) F)ˣ)
    {v : HeightOneSpectrum (𝓞 F)} (hv : v ∉ S) :
    ((partAt F S a : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F).2 v = 1 := by
  exact if_neg hv

theorem unitPart_fst (S : Finset (HeightOneSpectrum (𝓞 F))) (a : (AdeleRing (𝓞 F) F)ˣ) :
    ((unitPart F S a : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F).1 = 1 := by
  rfl

theorem unitPart_snd_of_mem (S : Finset (HeightOneSpectrum (𝓞 F))) (a : (AdeleRing (𝓞 F) F)ˣ) :
    ∀ v ∈ S, ((unitPart F S a : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F).2 v = 1 := by
  intro v hv
  exact if_pos hv

theorem unitPart_snd_of_not_mem (S : Finset (HeightOneSpectrum (𝓞 F))) (a : (AdeleRing (𝓞 F) F)ˣ)
    {v : HeightOneSpectrum (𝓞 F)} (hv : v ∉ S) :
    ((unitPart F S a : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F).2 v =
      (a : AdeleRing (𝓞 F) F).2 v *
        ((uniformizerUnit F v : (v.adicCompletion F)ˣ) : v.adicCompletion F) ^ (-(ord F v a)) := by
  exact if_neg hv

private theorem unitFin_val_mem (S : Finset (HeightOneSpectrum (𝓞 F))) (a : (AdeleRing (𝓞 F) F)ˣ)
    (v : HeightOneSpectrum (𝓞 F)) :
    ((unitFin F S a : (FiniteAdeleRing (𝓞 F) F)ˣ) : FiniteAdeleRing (𝓞 F) F) v ∈ v.adicCompletionIntegers F := by
  by_cases hv : v ∈ S
  · have h : ((unitFin F S a : (FiniteAdeleRing (𝓞 F) F)ˣ) : FiniteAdeleRing (𝓞 F) F) v = 1 := if_pos hv
    rw [h]; exact one_mem _
  · have h : ((unitFin F S a : (FiniteAdeleRing (𝓞 F) F)ˣ) : FiniteAdeleRing (𝓞 F) F) v = unitComponent F v a :=
      if_neg hv
    rw [h, HeightOneSpectrum.mem_adicCompletionIntegers]; exact (valued_unitComponent F v a).le

private theorem unitFin_inv_mem (S : Finset (HeightOneSpectrum (𝓞 F))) (a : (AdeleRing (𝓞 F) F)ˣ)
    (v : HeightOneSpectrum (𝓞 F)) :
    (((unitFin F S a)⁻¹ : (FiniteAdeleRing (𝓞 F) F)ˣ) : FiniteAdeleRing (𝓞 F) F) v ∈ v.adicCompletionIntegers F := by
  by_cases hv : v ∈ S
  · have h : (((unitFin F S a)⁻¹ : (FiniteAdeleRing (𝓞 F) F)ˣ) : FiniteAdeleRing (𝓞 F) F) v = 1 := if_pos hv
    rw [h]; exact one_mem _
  · have h : (((unitFin F S a)⁻¹ : (FiniteAdeleRing (𝓞 F) F)ˣ) : FiniteAdeleRing (𝓞 F) F) v =
        unitComponent F v a⁻¹ := if_neg hv
    rw [h, HeightOneSpectrum.mem_adicCompletionIntegers]; exact (valued_unitComponent F v a⁻¹).le

theorem finitePartUnits_unitPart_mem_unitIdeles (S : Finset (HeightOneSpectrum (𝓞 F)))
    (a : (AdeleRing (𝓞 F) F)ˣ) :
    finitePartUnits (𝓞 F) F (unitPart F S a) ∈ IsDedekindDomain.FiniteAdeleRing.unitIdeles (𝓞 F) F := by
  exact ⟨fun v => unitFin_val_mem F S a v, fun v => unitFin_inv_mem F S a v⟩

theorem unitPart_mul (S : Finset (HeightOneSpectrum (𝓞 F))) (a b : (AdeleRing (𝓞 F) F)ˣ) :
    unitPart F S (a * b) = unitPart F S a * unitPart F S b := by
  refine Units.ext ?_
  show AdelicLevel.finIncl (𝓞 F) F ((unitFin F S (a * b) : (FiniteAdeleRing (𝓞 F) F)ˣ) : FiniteAdeleRing (𝓞 F) F) =
    AdelicLevel.finIncl (𝓞 F) F ((unitFin F S a : (FiniteAdeleRing (𝓞 F) F)ˣ) : FiniteAdeleRing (𝓞 F) F) *
      AdelicLevel.finIncl (𝓞 F) F ((unitFin F S b : (FiniteAdeleRing (𝓞 F) F)ˣ) : FiniteAdeleRing (𝓞 F) F)
  rw [← map_mul]
  refine congrArg _ (Subtype.ext (funext fun v => ?_))
  show ((unitFin F S (a * b) : (FiniteAdeleRing (𝓞 F) F)ˣ) : FiniteAdeleRing (𝓞 F) F) v =
    ((unitFin F S a : (FiniteAdeleRing (𝓞 F) F)ˣ) : FiniteAdeleRing (𝓞 F) F) v *
      ((unitFin F S b : (FiniteAdeleRing (𝓞 F) F)ˣ) : FiniteAdeleRing (𝓞 F) F) v
  by_cases hv : v ∈ S
  · have h1 : ((unitFin F S (a * b) : (FiniteAdeleRing (𝓞 F) F)ˣ) : FiniteAdeleRing (𝓞 F) F) v = 1 := if_pos hv
    have h2 : ((unitFin F S a : (FiniteAdeleRing (𝓞 F) F)ˣ) : FiniteAdeleRing (𝓞 F) F) v = 1 := if_pos hv
    have h3 : ((unitFin F S b : (FiniteAdeleRing (𝓞 F) F)ˣ) : FiniteAdeleRing (𝓞 F) F) v = 1 := if_pos hv
    rw [h1, h2, h3, one_mul]
  · have h1 : ((unitFin F S (a * b) : (FiniteAdeleRing (𝓞 F) F)ˣ) : FiniteAdeleRing (𝓞 F) F) v =
        unitComponent F v (a * b) := if_neg hv
    have h2 : ((unitFin F S a : (FiniteAdeleRing (𝓞 F) F)ˣ) : FiniteAdeleRing (𝓞 F) F) v = unitComponent F v a :=
      if_neg hv
    have h3 : ((unitFin F S b : (FiniteAdeleRing (𝓞 F) F)ˣ) : FiniteAdeleRing (𝓞 F) F) v = unitComponent F v b :=
      if_neg hv
    have hab : ((a * b : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F).2 v =
        (a : AdeleRing (𝓞 F) F).2 v * (b : AdeleRing (𝓞 F) F).2 v := rfl
    rw [h1, h2, h3]
    simp only [unitComponent]
    rw [hab, ord_mul, neg_add, zpow_add₀ (uniformizerUnit F v).ne_zero, mul_mul_mul_comm]

private theorem idele_ext {a b : (AdeleRing (𝓞 F) F)ˣ}
    (h₁ : ∀ w : InfinitePlace F, infiniteUnitsComponent (𝓞 F) F w a = infiniteUnitsComponent (𝓞 F) F w b)
    (h₂ : ∀ w : HeightOneSpectrum (𝓞 F), finiteUnitsComponent (𝓞 F) F w a = finiteUnitsComponent (𝓞 F) F w b) :
    a = b :=
  Units.ext (Prod.ext (funext fun w => congrArg Units.val (h₁ w))
    (Subtype.ext (funext fun w => congrArg Units.val (h₂ w))))

private theorem iUC_partAt (S : Finset (HeightOneSpectrum (𝓞 F))) (a : (AdeleRing (𝓞 F) F)ˣ)
    (w : InfinitePlace F) : infiniteUnitsComponent (𝓞 F) F w (partAt F S a) = infiniteUnitsComponent (𝓞 F) F w a :=
  Units.ext rfl

private theorem iUC_unitPart (S : Finset (HeightOneSpectrum (𝓞 F))) (a : (AdeleRing (𝓞 F) F)ˣ)
    (w : InfinitePlace F) : infiniteUnitsComponent (𝓞 F) F w (unitPart F S a) = 1 :=
  Units.ext rfl

private theorem iUC_uniformizerIdele (v : HeightOneSpectrum (𝓞 F)) (w : InfinitePlace F) :
    infiniteUnitsComponent (𝓞 F) F w (AutomorphicForm.uniformizerIdele F v) = 1 :=
  Units.ext rfl

private theorem fUC_partAt_of_mem (S : Finset (HeightOneSpectrum (𝓞 F))) (a : (AdeleRing (𝓞 F) F)ˣ)
    {w : HeightOneSpectrum (𝓞 F)} (hw : w ∈ S) :
    finiteUnitsComponent (𝓞 F) F w (partAt F S a) = finiteUnitsComponent (𝓞 F) F w a :=
  Units.ext (if_pos hw)

private theorem fUC_partAt_of_not_mem (S : Finset (HeightOneSpectrum (𝓞 F))) (a : (AdeleRing (𝓞 F) F)ˣ)
    {w : HeightOneSpectrum (𝓞 F)} (hw : w ∉ S) : finiteUnitsComponent (𝓞 F) F w (partAt F S a) = 1 :=
  Units.ext (if_neg hw)

private theorem fUC_unitPart_of_mem (S : Finset (HeightOneSpectrum (𝓞 F))) (a : (AdeleRing (𝓞 F) F)ˣ)
    {w : HeightOneSpectrum (𝓞 F)} (hw : w ∈ S) : finiteUnitsComponent (𝓞 F) F w (unitPart F S a) = 1 :=
  Units.ext (if_pos hw)

private theorem val_fUC_unitPart_of_not_mem (S : Finset (HeightOneSpectrum (𝓞 F))) (a : (AdeleRing (𝓞 F) F)ˣ)
    {w : HeightOneSpectrum (𝓞 F)} (hw : w ∉ S) :
    ((finiteUnitsComponent (𝓞 F) F w (unitPart F S a) : (w.adicCompletion F)ˣ) : w.adicCompletion F) =
      (a : AdeleRing (𝓞 F) F).2 w * (uniformizerUnit F w : w.adicCompletion F) ^ (-(ord F w a)) :=
  if_neg hw

private theorem fUC_uniformizerIdele_self (w : HeightOneSpectrum (𝓞 F)) :
    finiteUnitsComponent (𝓞 F) F w (AutomorphicForm.uniformizerIdele F w) = uniformizerUnit F w :=
  Units.ext (by
    show ((localUnit (𝓞 F) F w (uniformizerUnit F w) : (FiniteAdeleRing (𝓞 F) F)ˣ) : FiniteAdeleRing (𝓞 F) F) w = _
    rw [localUnit_apply_self])

private theorem fUC_uniformizerIdele_of_ne {v w : HeightOneSpectrum (𝓞 F)} (h : w ≠ v) :
    finiteUnitsComponent (𝓞 F) F w (AutomorphicForm.uniformizerIdele F v) = 1 :=
  Units.ext (by
    show ((localUnit (𝓞 F) F v (uniformizerUnit F v) : (FiniteAdeleRing (𝓞 F) F)ˣ) : FiniteAdeleRing (𝓞 F) F) w = 1
    rw [localUnit_apply_of_ne (𝓞 F) F v (uniformizerUnit F v) h])

theorem eq_partAt_mul_prod_mul_unitPart (S : Finset (HeightOneSpectrum (𝓞 F)))
    (L : List (HeightOneSpectrum (𝓞 F))) (hLS : ∀ v ∈ L, v ∉ S) (hL : L.Nodup)
    (a : (AdeleRing (𝓞 F) F)ˣ)
    (ha : a ∈ NumberField.AdeleRing.unitIdelesOutside (𝓞 F) F (↑S ∪ {v | v ∈ L})) :
    a = partAt F S a *
      (L.map fun v => AutomorphicForm.uniformizerIdele F v ^ ord F v a).prod * unitPart F S a := by
  classical
  rw [NumberField.AdeleRing.mem_unitIdelesOutside_iff] at ha
  refine idele_ext F (fun w => ?_) (fun w => ?_)
  · have hMw : infiniteUnitsComponent (𝓞 F) F w
        (L.map fun v => AutomorphicForm.uniformizerIdele F v ^ ord F v a).prod = 1 := by
      rw [map_list_prod, List.map_map]
      refine List.prod_eq_one fun x hx => ?_
      obtain ⟨v, -, rfl⟩ := List.mem_map.mp hx
      rw [Function.comp_apply, map_zpow, iUC_uniformizerIdele, one_zpow]
    rw [map_mul, map_mul, iUC_partAt, hMw, iUC_unitPart, mul_one, mul_one]
  · have hMw : finiteUnitsComponent (𝓞 F) F w
        (L.map fun v => AutomorphicForm.uniformizerIdele F v ^ ord F v a).prod =
        (finiteUnitsComponent (𝓞 F) F w (AutomorphicForm.uniformizerIdele F w) ^ ord F w a) ^
          L.count w := by
      rw [map_list_prod, List.map_map, List.prod_map_eq_pow_single w]
      · rw [Function.comp_apply, map_zpow]
      · intro v hvw _
        rw [Function.comp_apply, map_zpow, fUC_uniformizerIdele_of_ne F hvw.symm, one_zpow]
    rw [map_mul, map_mul, hMw]
    by_cases hwS : w ∈ S
    · have hwL : w ∉ L := fun h => hLS w h hwS
      rw [fUC_partAt_of_mem F S a hwS, fUC_unitPart_of_mem F S a hwS, List.count_eq_zero.mpr hwL,
        pow_zero, mul_one, mul_one]
    · rw [fUC_partAt_of_not_mem F S a hwS, one_mul]
      refine Units.ext ?_
      rw [Units.val_mul, val_fUC_unitPart_of_not_mem F S a hwS, Units.val_pow_eq_pow_val,
        Units.val_zpow_eq_zpow_val, fUC_uniformizerIdele_self]
      by_cases hwL : w ∈ L
      · rw [List.count_eq_one_of_mem hL hwL, pow_one, mul_left_comm,
          ← zpow_add₀ (uniformizerUnit F w).ne_zero, add_neg_cancel, zpow_zero, mul_one]
        rfl
      · have hw' : w ∉ (↑S ∪ {v | v ∈ L} : Set (HeightOneSpectrum (𝓞 F))) := by
          rintro (h | h)
          · exact hwS h
          · exact hwL h
        have h0 : ord F w a = 0 := (ord_eq_zero_iff F w a).mpr (ha w hw')
        rw [List.count_eq_zero.mpr hwL, pow_zero, one_mul, h0, neg_zero, zpow_zero, mul_one]
        rfl

theorem diagOne_eq_diagOne_partAt_mul_prod_mul (S : Finset (HeightOneSpectrum (𝓞 F)))
    (L : List (HeightOneSpectrum (𝓞 F))) (hLS : ∀ v ∈ L, v ∉ S) (hL : L.Nodup)
    (a : (AdeleRing (𝓞 F) F)ˣ)
    (ha : a ∈ NumberField.AdeleRing.unitIdelesOutside (𝓞 F) F (↑S ∪ {v | v ∈ L})) :
    diagOne a = diagOne (partAt F S a) *
      (L.map fun v => diagOne (AutomorphicForm.uniformizerIdele F v) ^ ord F v a).prod *
        diagOne (unitPart F S a) := by
  conv_lhs => rw [eq_partAt_mul_prod_mul_unitPart F S L hLS hL a ha]
  simp only [map_mul, map_list_prod, List.map_map, Function.comp_def, map_zpow]

theorem diagOne_mul_finEmbed_localEmbed_of_snd_eq_one {v : HeightOneSpectrum (𝓞 F)}
    (a : (AdeleRing (𝓞 F) F)ˣ) (hav : (a : AdeleRing (𝓞 F) F).2 v = 1)
    (x : GL (Fin 2) (v.adicCompletion F)) :
    diagOne a * AdelicDock.finEmbed (𝓞 F) F (AdelicDock.localEmbed (𝓞 F) F v x) =
      AdelicDock.finEmbed (𝓞 F) F (AdelicDock.localEmbed (𝓞 F) F v x) * diagOne a := by
  refine Units.ext ?_
  rw [Units.val_mul, Units.val_mul, AdelicDock.coe_finEmbed, AdelicDock.coe_localEmbed]
  refine AdelicDock.matrix_eq_of_mapMatrix_arch_fin_eq (𝓞 F) F ?_ ?_
  · rw [map_mul, map_mul, AdelicDock.mapMatrix_arch_finMat, mul_one, one_mul]
  · rw [map_mul, map_mul, AdelicDock.mapMatrix_fin_finMat]
    refine AdelicDock.matrix_eq_of_forall_mapMatrix_finAdeleEval_eq (𝓞 F) F fun w => ?_
    rw [map_mul, map_mul]
    by_cases hw : w = v
    · have h00 : finAdeleEval (𝓞 F) F v (adeleFin (𝓞 F) F (a : AdeleRing (𝓞 F) F)) = 1 := hav
      have hdiag : (finAdeleEval (𝓞 F) F v).mapMatrix ((adeleFin (𝓞 F) F).mapMatrix
          ((diagOne a : GL (Fin 2) (AdeleRing (𝓞 F) F)) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F))) = 1 := by
        ext i j
        fin_cases i <;> fin_cases j <;>
          simp [RingHom.mapMatrix_apply, Matrix.map_apply, diagOne_coe_apply, h00]
      rw [hw, hdiag, AdelicDock.mapMatrix_localMat_self, one_mul, mul_one]
    · rw [AdelicDock.mapMatrix_localMat_of_ne (𝓞 F) F v _ hw, mul_one, one_mul]

theorem diagOne_partAt_mul_finEmbed_localEmbed (S : Finset (HeightOneSpectrum (𝓞 F)))
    (a : (AdeleRing (𝓞 F) F)ˣ) {v : HeightOneSpectrum (𝓞 F)} (hv : v ∉ S)
    (x : GL (Fin 2) (v.adicCompletion F)) :
    diagOne (partAt F S a) * AdelicDock.finEmbed (𝓞 F) F (AdelicDock.localEmbed (𝓞 F) F v x) =
      AdelicDock.finEmbed (𝓞 F) F (AdelicDock.localEmbed (𝓞 F) F v x) * diagOne (partAt F S a) := by
  exact diagOne_mul_finEmbed_localEmbed_of_snd_eq_one F (partAt F S a) (partAt_snd_of_not_mem F S a hv) x

end NumberField.Idele

namespace NumberField.Idele

open MeasureTheory

variable (F : Type) [Field F] [NumberField F]

@[reducible] def ideleBorel : MeasurableSpace (AdeleRing (𝓞 F) F)ˣ := borel _

theorem borelSpace_ideleBorel : @BorelSpace (AdeleRing (𝓞 F) F)ˣ _ (ideleBorel F) :=
  @BorelSpace.mk _ _ (ideleBorel F) rfl

attribute [local instance] ideleBorel borelSpace_ideleBorel

def idelicHaar : Measure (AdeleRing (𝓞 F) F)ˣ := Measure.haar

theorem isHaarMeasure_idelicHaar : (idelicHaar F).IsHaarMeasure := by
  rw [idelicHaar]; infer_instance

attribute [local instance] isHaarMeasure_idelicHaar

theorem isOpen_unitIdelesOutside (T : Set (HeightOneSpectrum (𝓞 F))) :
    IsOpen (NumberField.AdeleRing.unitIdelesOutside (𝓞 F) F T : Set (AdeleRing (𝓞 F) F)ˣ) := by
  have hO : IsOpen {x : FiniteAdeleRing (𝓞 F) F | ∀ v, v ∉ T → x.1 v ∈ v.adicCompletionIntegers F} :=
    RestrictedProduct.isOpen_forall_imp_mem fun v => Valued.isOpen_valuationSubring _
  have h1 : Continuous fun a : (AdeleRing (𝓞 F) F)ˣ => (a : AdeleRing (𝓞 F) F).2 :=
    continuous_snd.comp Units.continuous_val
  have h2 : Continuous fun a : (AdeleRing (𝓞 F) F)ˣ => ((a⁻¹ : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F).2 :=
    continuous_snd.comp Units.continuous_coe_inv
  have hset : (NumberField.AdeleRing.unitIdelesOutside (𝓞 F) F T : Set (AdeleRing (𝓞 F) F)ˣ) =
      (fun a : (AdeleRing (𝓞 F) F)ˣ => (a : AdeleRing (𝓞 F) F).2) ⁻¹'
          {x : FiniteAdeleRing (𝓞 F) F | ∀ v, v ∉ T → x.1 v ∈ v.adicCompletionIntegers F} ∩
        (fun a : (AdeleRing (𝓞 F) F)ˣ => ((a⁻¹ : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F).2) ⁻¹'
          {x : FiniteAdeleRing (𝓞 F) F | ∀ v, v ∉ T → x.1 v ∈ v.adicCompletionIntegers F} := by
    ext a
    rw [SetLike.mem_coe, NumberField.AdeleRing.mem_unitIdelesOutside_iff,
      IsDedekindDomain.FiniteAdeleRing.mem_unitIdelesOutside_iff]
    exact ⟨fun h => Set.mem_inter (fun v hv => (h v hv).1) (fun v hv => (h v hv).2),
      fun h v hv => ⟨h.1 v hv, h.2 v hv⟩⟩
  rw [hset]
  exact (hO.preimage h1).inter (hO.preimage h2)

theorem idelicHaar_unitIdelesOutside_ne_zero (T : Set (HeightOneSpectrum (𝓞 F))) :
    idelicHaar F (NumberField.AdeleRing.unitIdelesOutside (𝓞 F) F T : Set (AdeleRing (𝓞 F) F)ˣ) ≠ 0 :=
  (isOpen_unitIdelesOutside F T).measure_ne_zero _ ⟨1, Subgroup.one_mem _⟩

open scoped Classical in

theorem truncFin_eq_mapAlong (S : Finset (HeightOneSpectrum (𝓞 F))) :
    (truncFin F S : FiniteAdeleRing (𝓞 F) F → FiniteAdeleRing (𝓞 F) F) =
      RestrictedProduct.mapAlong (fun v : HeightOneSpectrum (𝓞 F) => v.adicCompletion F)
        (fun v : HeightOneSpectrum (𝓞 F) => v.adicCompletion F) id Filter.tendsto_id
        (fun v x => if v ∈ S then x else 1)
        (Filter.Eventually.of_forall fun v => by
          intro x hx
          show (if v ∈ S then x else 1) ∈ (v.adicCompletionIntegers F : Set (v.adicCompletion F))
          by_cases h : v ∈ S
          · rw [if_pos h]; exact hx
          · rw [if_neg h]; exact one_mem _) := by
  funext x
  exact RestrictedProduct.ext _ _ fun v => rfl

open scoped Classical in

theorem continuous_truncFin (S : Finset (HeightOneSpectrum (𝓞 F))) : Continuous (truncFin F S) := by
  rw [truncFin_eq_mapAlong]
  refine RestrictedProduct.mapAlong_continuous _ _ _ _ _ _ fun v => ?_
  show Continuous fun x : v.adicCompletion F => if v ∈ S then x else 1
  by_cases h : v ∈ S
  · simp only [if_pos h]; exact continuous_id
  · simp only [if_neg h]; exact continuous_const

theorem continuous_partAtAdele (S : Finset (HeightOneSpectrum (𝓞 F))) : Continuous (partAtAdele F S) :=
  Continuous.prodMk continuous_fst ((continuous_truncFin F S).comp continuous_snd)

theorem continuous_partAt (S : Finset (HeightOneSpectrum (𝓞 F))) : Continuous (partAt F S) :=
  Continuous.units_map _ (continuous_partAtAdele F S)

theorem measurable_partAt (S : Finset (HeightOneSpectrum (𝓞 F))) : Measurable (partAt F S) :=
  (continuous_partAt F S).measurable

def sPartMeasure (S : Finset (HeightOneSpectrum (𝓞 F))) : Measure (AdeleRing (𝓞 F) F)ˣ :=
  Measure.map (partAt F S)
    ((idelicHaar F).restrict (NumberField.AdeleRing.unitIdelesOutside (𝓞 F) F (↑S) : Set (AdeleRing (𝓞 F) F)ˣ))

theorem sPartMeasure_ne_zero (S : Finset (HeightOneSpectrum (𝓞 F))) : sPartMeasure F S ≠ 0 := by
  intro h
  have h1 := congrArg (fun μ : Measure (AdeleRing (𝓞 F) F)ˣ => μ Set.univ) h
  simp only [sPartMeasure, Measure.map_apply (measurable_partAt F S) MeasurableSet.univ, Set.preimage_univ,
    Measure.restrict_apply_univ, Measure.coe_zero, Pi.zero_apply] at h1
  exact idelicHaar_unitIdelesOutside_ne_zero F _ h1

private def ordHom (v : HeightOneSpectrum (𝓞 F)) : (AdeleRing (𝓞 F) F)ˣ →* Multiplicative ℤ where
  toFun a := Multiplicative.ofAdd (ord F v a)
  map_one' := by rw [ord_one]; rfl
  map_mul' a b := by rw [ord_mul]; rfl

private theorem ord_zpow (v : HeightOneSpectrum (𝓞 F)) (a : (AdeleRing (𝓞 F) F)ˣ) (n : ℤ) :
    ord F v (a ^ n) = n * ord F v a := by
  have h : Multiplicative.ofAdd (ord F v (a ^ n)) = Multiplicative.ofAdd (ord F v a) ^ n :=
    map_zpow (ordHom F v) a n
  rw [← ofAdd_zsmul] at h
  rw [Multiplicative.ofAdd.injective h, smul_eq_mul]

private theorem fUC_partAt_uniformizerIdele (S : Finset (HeightOneSpectrum (𝓞 F))) {v : HeightOneSpectrum (𝓞 F)}
    (hv : v ∉ S) (w : HeightOneSpectrum (𝓞 F)) :
    finiteUnitsComponent (𝓞 F) F w (partAt F S (AutomorphicForm.uniformizerIdele F v)) = 1 := by
  by_cases hw : w ∈ S
  · rw [fUC_partAt_of_mem F S _ hw]
    exact fUC_uniformizerIdele_of_ne F fun h => hv (h ▸ hw)
  · exact fUC_partAt_of_not_mem F S _ hw

private theorem partAt_uniformizerIdele_of_not_mem (S : Finset (HeightOneSpectrum (𝓞 F)))
    {v : HeightOneSpectrum (𝓞 F)} (hv : v ∉ S) : partAt F S (AutomorphicForm.uniformizerIdele F v) = 1 := by
  refine idele_ext F (fun w => ?_) (fun w => ?_)
  · rw [iUC_partAt, iUC_uniformizerIdele, map_one]
  · rw [fUC_partAt_uniformizerIdele F S hv, map_one]

private theorem mem_unitIdelesOutside_iff_ord (T : Set (HeightOneSpectrum (𝓞 F))) (a : (AdeleRing (𝓞 F) F)ˣ) :
    a ∈ NumberField.AdeleRing.unitIdelesOutside (𝓞 F) F T ↔ ∀ w, w ∉ T → ord F w a = 0 := by
  rw [NumberField.AdeleRing.mem_unitIdelesOutside_iff, IsDedekindDomain.FiniteAdeleRing.mem_unitIdelesOutside_iff]
  refine forall_congr' fun w => imp_congr_right fun _ => ?_
  rw [ord_eq_zero_iff]
  rfl

private theorem mem_image_uniformizerIdele_zpow_mul_iff (T' : Set (HeightOneSpectrum (𝓞 F)))
    {v : HeightOneSpectrum (𝓞 F)} (hv : v ∉ T') (n : ℤ) (a : (AdeleRing (𝓞 F) F)ˣ) :
    a ∈ (fun b : (AdeleRing (𝓞 F) F)ˣ => AutomorphicForm.uniformizerIdele F v ^ n * b) ''
        (NumberField.AdeleRing.unitIdelesOutside (𝓞 F) F T' : Set (AdeleRing (𝓞 F) F)ˣ) ↔
      a ∈ (NumberField.AdeleRing.unitIdelesOutside (𝓞 F) F (insert v T') : Set (AdeleRing (𝓞 F) F)ˣ) ∧
        ord F v a = n := by
  constructor
  · rintro ⟨b, hb, rfl⟩
    rw [SetLike.mem_coe, mem_unitIdelesOutside_iff_ord] at hb
    refine ⟨?_, ?_⟩
    · rw [SetLike.mem_coe, mem_unitIdelesOutside_iff_ord]
      intro w hw
      rw [Set.mem_insert_iff, not_or] at hw
      rw [ord_mul, ord_zpow, ord_uniformizerIdele_of_ne F hw.1, mul_zero, zero_add, hb w hw.2]
    · rw [ord_mul, ord_zpow, ord_uniformizerIdele_self, mul_one, hb v hv, add_zero]
  · rintro ⟨ha, hn⟩
    rw [SetLike.mem_coe, mem_unitIdelesOutside_iff_ord] at ha
    refine ⟨AutomorphicForm.uniformizerIdele F v ^ (-n) * a, ?_, ?_⟩
    · rw [SetLike.mem_coe, mem_unitIdelesOutside_iff_ord]
      intro w hw
      by_cases hwv : w = v
      · rw [hwv, ord_mul, ord_zpow, ord_uniformizerIdele_self, mul_one, hn, neg_add_cancel]
      · rw [ord_mul, ord_zpow, ord_uniformizerIdele_of_ne F hwv, mul_zero, zero_add]
        exact ha w fun h => (Set.mem_insert_iff.mp h).elim hwv hw
    · show AutomorphicForm.uniformizerIdele F v ^ n * (AutomorphicForm.uniformizerIdele F v ^ (-n) * a) = a
      rw [← mul_assoc, ← zpow_add, add_neg_cancel, zpow_zero, one_mul]

private theorem iUnion_image_uniformizerIdele_zpow_mul (T' : Set (HeightOneSpectrum (𝓞 F)))
    {v : HeightOneSpectrum (𝓞 F)} (hv : v ∉ T') :
    (⋃ n : ℤ, (fun b : (AdeleRing (𝓞 F) F)ˣ => AutomorphicForm.uniformizerIdele F v ^ n * b) ''
        (NumberField.AdeleRing.unitIdelesOutside (𝓞 F) F T' : Set (AdeleRing (𝓞 F) F)ˣ)) =
      (NumberField.AdeleRing.unitIdelesOutside (𝓞 F) F (insert v T') : Set (AdeleRing (𝓞 F) F)ˣ) := by
  ext a
  rw [Set.mem_iUnion]
  constructor
  · rintro ⟨n, h⟩
    exact ((mem_image_uniformizerIdele_zpow_mul_iff F T' hv n a).mp h).1
  · intro h
    exact ⟨ord F v a, (mem_image_uniformizerIdele_zpow_mul_iff F T' hv _ a).mpr ⟨h, rfl⟩⟩

private theorem pairwise_disjoint_image_uniformizerIdele_zpow_mul (T' : Set (HeightOneSpectrum (𝓞 F)))
    {v : HeightOneSpectrum (𝓞 F)} (hv : v ∉ T') :
    Pairwise (Function.onFun Disjoint fun n : ℤ =>
      (fun b : (AdeleRing (𝓞 F) F)ˣ => AutomorphicForm.uniformizerIdele F v ^ n * b) ''
        (NumberField.AdeleRing.unitIdelesOutside (𝓞 F) F T' : Set (AdeleRing (𝓞 F) F)ˣ)) := by
  intro m n hmn
  refine Set.disjoint_left.mpr fun a ham han => hmn ?_
  exact ((mem_image_uniformizerIdele_zpow_mul_iff F T' hv m a).mp ham).2.symm.trans
    ((mem_image_uniformizerIdele_zpow_mul_iff F T' hv n a).mp han).2

private theorem integrableOn_and_integral_eq (S : Finset (HeightOneSpectrum (𝓞 F)))
    (f : (AdeleRing (𝓞 F) F)ˣ → ℂ) (φ : HeightOneSpectrum (𝓞 F) → ℤ → ℂ) (hf : Integrable f (sPartMeasure F S)) :
    ∀ (L : List (HeightOneSpectrum (𝓞 F))), (∀ v ∈ L, v ∉ S) → L.Nodup →
      (∀ v ∈ L, Summable fun m : ℤ => ‖φ v m‖) →
        IntegrableOn (fun a => f (partAt F S a) * (L.map fun v => φ v (ord F v a)).prod)
            (NumberField.AdeleRing.unitIdelesOutside (𝓞 F) F (↑S ∪ {v | v ∈ L}) : Set (AdeleRing (𝓞 F) F)ˣ)
            (idelicHaar F) ∧
          (∫ a in (NumberField.AdeleRing.unitIdelesOutside (𝓞 F) F (↑S ∪ {v | v ∈ L}) : Set (AdeleRing (𝓞 F) F)ˣ),
              f (partAt F S a) * (L.map fun v => φ v (ord F v a)).prod ∂(idelicHaar F)) =
            (∫ a, f a ∂(sPartMeasure F S)) * (L.map fun v => ∑' m : ℤ, φ v m).prod := by
  intro L
  induction L with
  | nil =>
    intro _ _ _
    have hT : (↑S ∪ {v | v ∈ ([] : List (HeightOneSpectrum (𝓞 F)))} : Set (HeightOneSpectrum (𝓞 F))) = ↑S := by
      ext w
      simp only [Set.mem_union, Set.mem_setOf_eq, List.not_mem_nil, or_false]
    simp only [List.map_nil, List.prod_nil, mul_one, hT]
    have hφm : AEMeasurable (partAt F S) ((idelicHaar F).restrict
        (NumberField.AdeleRing.unitIdelesOutside (𝓞 F) F (↑S) : Set (AdeleRing (𝓞 F) F)ˣ)) :=
      (measurable_partAt F S).aemeasurable
    rw [sPartMeasure] at hf ⊢
    exact ⟨(integrable_map_measure hf.aestronglyMeasurable hφm).mp hf,
      (integral_map hφm hf.aestronglyMeasurable).symm⟩
  | cons v L' IH =>
    intro hLS hL hφ
    have hvS : v ∉ S := hLS v (List.mem_cons.mpr (Or.inl rfl))
    have hLS' : ∀ w ∈ L', w ∉ S := fun w hw => hLS w (List.mem_cons.mpr (Or.inr hw))
    have hvL' : v ∉ L' := (List.nodup_cons.mp hL).1
    have hL' : L'.Nodup := (List.nodup_cons.mp hL).2
    have hφv : Summable fun m : ℤ => ‖φ v m‖ := hφ v (List.mem_cons.mpr (Or.inl rfl))
    have hφ' : ∀ w ∈ L', Summable fun m : ℤ => ‖φ w m‖ := fun w hw => hφ w (List.mem_cons.mpr (Or.inr hw))
    obtain ⟨IHi, IHe⟩ := IH hLS' hL' hφ'

    have hv' : v ∉ (↑S ∪ {w | w ∈ L'} : Set (HeightOneSpectrum (𝓞 F))) := by
      rintro (h | h)
      · exact hvS (Finset.mem_coe.mp h)
      · exact hvL' h
    have hT : (↑S ∪ {w | w ∈ v :: L'} : Set (HeightOneSpectrum (𝓞 F))) = insert v (↑S ∪ {w | w ∈ L'}) := by
      ext w
      simp only [Set.mem_union, Set.mem_setOf_eq, List.mem_cons, Set.mem_insert_iff, Finset.mem_coe]
      tauto
    rw [hT, ← iUnion_image_uniformizerIdele_zpow_mul F _ hv']

    have hkey : ∀ (n : ℤ) (b : (AdeleRing (𝓞 F) F)ˣ),
        b ∈ (NumberField.AdeleRing.unitIdelesOutside (𝓞 F) F (↑S ∪ {w | w ∈ L'}) : Set (AdeleRing (𝓞 F) F)ˣ) →
        f (partAt F S (AutomorphicForm.uniformizerIdele F v ^ n * b)) *
            ((v :: L').map fun w => φ w (ord F w (AutomorphicForm.uniformizerIdele F v ^ n * b))).prod =
          φ v n * (f (partAt F S b) * (L'.map fun w => φ w (ord F w b)).prod) := by
      intro n b hb
      rw [SetLike.mem_coe, mem_unitIdelesOutside_iff_ord] at hb
      have h1 : partAt F S (AutomorphicForm.uniformizerIdele F v ^ n * b) = partAt F S b := by
        rw [map_mul, map_zpow, partAt_uniformizerIdele_of_not_mem F S hvS, one_zpow, one_mul]
      have h2 : ord F v (AutomorphicForm.uniformizerIdele F v ^ n * b) = n := by
        rw [ord_mul, ord_zpow, ord_uniformizerIdele_self, mul_one, hb v hv', add_zero]
      have h3 : ((L'.map fun w => φ w (ord F w (AutomorphicForm.uniformizerIdele F v ^ n * b))) :
          List ℂ) = L'.map fun w => φ w (ord F w b) := by
        refine List.map_congr_left fun w hw => ?_
        have hwv : w ≠ v := fun h => hvL' (h ▸ hw)
        rw [ord_mul, ord_zpow, ord_uniformizerIdele_of_ne F hwv, mul_zero, zero_add]
      rw [List.map_cons, List.prod_cons, h1, h2, h3]
      ring

    have hmp : ∀ n : ℤ, MeasurePreserving
        (fun b : (AdeleRing (𝓞 F) F)ˣ => AutomorphicForm.uniformizerIdele F v ^ n * b) (idelicHaar F) (idelicHaar F) :=
      fun n => measurePreserving_mul_left (idelicHaar F) _
    have hme : ∀ n : ℤ, MeasurableEmbedding
        fun b : (AdeleRing (𝓞 F) F)ˣ => AutomorphicForm.uniformizerIdele F v ^ n * b :=
      fun n => (MeasurableEquiv.mulLeft (AutomorphicForm.uniformizerIdele F v ^ n)).measurableEmbedding
    have hU' : MeasurableSet
        (NumberField.AdeleRing.unitIdelesOutside (𝓞 F) F (↑S ∪ {w | w ∈ L'}) : Set (AdeleRing (𝓞 F) F)ˣ) :=
      (isOpen_unitIdelesOutside F _).measurableSet
    have hmeas : ∀ n : ℤ, MeasurableSet
        ((fun b : (AdeleRing (𝓞 F) F)ˣ => AutomorphicForm.uniformizerIdele F v ^ n * b) ''
          (NumberField.AdeleRing.unitIdelesOutside (𝓞 F) F (↑S ∪ {w | w ∈ L'}) : Set (AdeleRing (𝓞 F) F)ˣ)) :=
      fun n => (hme n).measurableSet_image.mpr hU'

    have hpi : ∀ n : ℤ, IntegrableOn (fun a => f (partAt F S a) * ((v :: L').map fun w => φ w (ord F w a)).prod)
        ((fun b : (AdeleRing (𝓞 F) F)ˣ => AutomorphicForm.uniformizerIdele F v ^ n * b) ''
          (NumberField.AdeleRing.unitIdelesOutside (𝓞 F) F (↑S ∪ {w | w ∈ L'}) : Set (AdeleRing (𝓞 F) F)ˣ))
        (idelicHaar F) := by
      intro n
      have hc0 : IntegrableOn (fun b => φ v n * (f (partAt F S b) * (L'.map fun w => φ w (ord F w b)).prod))
          (NumberField.AdeleRing.unitIdelesOutside (𝓞 F) F (↑S ∪ {w | w ∈ L'}) : Set (AdeleRing (𝓞 F) F)ˣ)
          (idelicHaar F) :=
        Integrable.const_mul IHi (φ v n)
      have hc : IntegrableOn (fun b => f (partAt F S (AutomorphicForm.uniformizerIdele F v ^ n * b)) *
            ((v :: L').map fun w => φ w (ord F w (AutomorphicForm.uniformizerIdele F v ^ n * b))).prod)
          (NumberField.AdeleRing.unitIdelesOutside (𝓞 F) F (↑S ∪ {w | w ∈ L'}) : Set (AdeleRing (𝓞 F) F)ˣ)
          (idelicHaar F) :=
        hc0.congr_fun (fun b hb => (hkey n b hb).symm) hU'
      exact (((hmp n).restrict_image_emb (hme n) _).integrable_comp_emb (hme n)
        (g := fun a => f (partAt F S a) * ((v :: L').map fun w => φ w (ord F w a)).prod)).mp hc
    have hnorm : ∀ n : ℤ, (∫ a in (fun b : (AdeleRing (𝓞 F) F)ˣ => AutomorphicForm.uniformizerIdele F v ^ n * b) ''
          (NumberField.AdeleRing.unitIdelesOutside (𝓞 F) F (↑S ∪ {w | w ∈ L'}) : Set (AdeleRing (𝓞 F) F)ˣ),
          ‖f (partAt F S a) * ((v :: L').map fun w => φ w (ord F w a)).prod‖ ∂(idelicHaar F)) =
        ‖φ v n‖ * ∫ b in (NumberField.AdeleRing.unitIdelesOutside (𝓞 F) F (↑S ∪ {w | w ∈ L'}) :
            Set (AdeleRing (𝓞 F) F)ˣ),
          ‖f (partAt F S b) * (L'.map fun w => φ w (ord F w b)).prod‖ ∂(idelicHaar F) := by
      intro n
      rw [(hmp n).setIntegral_image_emb (hme n), ← integral_const_mul]
      refine setIntegral_congr_fun hU' fun b hb => ?_
      show ‖f (partAt F S (AutomorphicForm.uniformizerIdele F v ^ n * b)) *
          ((v :: L').map fun w => φ w (ord F w (AutomorphicForm.uniformizerIdele F v ^ n * b))).prod‖ =
        ‖φ v n‖ * ‖f (partAt F S b) * (L'.map fun w => φ w (ord F w b)).prod‖
      rw [hkey n b hb, norm_mul]
    have hsum : Summable fun n : ℤ => ∫ a in (fun b : (AdeleRing (𝓞 F) F)ˣ =>
          AutomorphicForm.uniformizerIdele F v ^ n * b) ''
          (NumberField.AdeleRing.unitIdelesOutside (𝓞 F) F (↑S ∪ {w | w ∈ L'}) : Set (AdeleRing (𝓞 F) F)ˣ),
          ‖f (partAt F S a) * ((v :: L').map fun w => φ w (ord F w a)).prod‖ ∂(idelicHaar F) := by
      simp_rw [hnorm]
      exact hφv.mul_right _
    have hint := integrableOn_iUnion_of_summable_integral_norm hpi hsum
    refine ⟨hint, ?_⟩

    rw [integral_iUnion hmeas (pairwise_disjoint_image_uniformizerIdele_zpow_mul F _ hv') hint]
    have hval : ∀ n : ℤ, (∫ a in (fun b : (AdeleRing (𝓞 F) F)ˣ => AutomorphicForm.uniformizerIdele F v ^ n * b) ''
          (NumberField.AdeleRing.unitIdelesOutside (𝓞 F) F (↑S ∪ {w | w ∈ L'}) : Set (AdeleRing (𝓞 F) F)ˣ),
          f (partAt F S a) * ((v :: L').map fun w => φ w (ord F w a)).prod ∂(idelicHaar F)) =
        φ v n * ((∫ a, f a ∂(sPartMeasure F S)) * (L'.map fun w => ∑' m : ℤ, φ w m).prod) := by
      intro n
      rw [(hmp n).setIntegral_image_emb (hme n), ← IHe, ← integral_const_mul]
      exact setIntegral_congr_fun hU' fun b hb => hkey n b hb
    simp_rw [hval]
    rw [tsum_mul_right, List.map_cons, List.prod_cons]
    ring

def productMeasureData (S : Finset (HeightOneSpectrum (𝓞 F))) :
    @UnramifiedWhittaker.ProductMeasureData F _ _ (ideleBorel F) S (idelicHaar F) where
  c := 1
  c_pos := one_pos
  νS := sPartMeasure F S
  projS := partAt F S
  ord := ord F
  projS_off a _ hv := partAt_snd_of_not_mem F S a hv
  decomp L hLS hL a ha := ⟨unitPart F S a, unitPart_fst F S a, unitPart_snd_of_mem F S a,
    finitePartUnits_unitPart_mem_unitIdeles F S a, eq_partAt_mul_prod_mul_unitPart F S L hLS hL a ha⟩
  tonelli L hLS hL f φ hf hφ := by
    obtain ⟨h1, h2⟩ := integrableOn_and_integral_eq F S f φ hf L hLS hL hφ
    exact ⟨h1, by rw [h2, Complex.ofReal_one, one_mul]⟩
  measurableSet L _ _ := (isOpen_unitIdelesOutside F _).measurableSet

end NumberField.Idele


