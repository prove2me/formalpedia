-- Prove2me | Definitions.Def_LIDT_MIPStarRE_LDT_Basic_PMFAverages
-- name    : LIDT_MIPStarRE_LDT_Basic_PMFAverages
-- status  : Definition
-- author  : @Dengnifer
-- created : 2026-10-27T10:50:13.872006+00:00
-- url     : https://prove2.me/theorems/0a1140d5-5cf6-4dd9-97ab-4bfdbb96e036
-- title:
--   LIDT definitions: LDT / Basic / PMFAverages
-- statement:
--   This bundle provides finite probability-mass-function averaging tools used when the LDT distribution formulas are compared with standard probability notation. It supports push-forward and monadic composition calculations, total variation, and uniform product sampling.
--
--   Principal definitions:
--   - `realWeightedSum`: the finite real-weighted sum of a module-valued family against a PMF.
--   - `realWeightedSumLinearMap`: the same PMF-weighted operation packaged as a linear map in the family.
--   - `totalVariationDistance`: half of the finite L1 distance between the real weights of two PMFs.
--   - `map_apply_toReal`: the pointwise real-weight formula for a pushed-forward PMF.
--   - `map_sum_smul`: the weighted-sum formula that pulls a function back through a PMF map.
--   - `bind_apply_toReal`: the pointwise real-weight formula for PMF bind.
--   - `bind_sum_smul`: the iterated weighted-sum formula for PMF bind.
--   - `uniformOfFintype_prod_eq_bind`: the uniform PMF on a product as the bind of the coordinate-uniform PMFs.
--
--   Formalization credit: Sirui Lu, Ruixuan Deng, Yanqiao Zhu, and Zhengfeng Ji (arXiv:2609.19814). Mathematical source: Zhengfeng Ji, Anand Natarajan, Thomas Vidick, John Wright, and Henry Yuen (arXiv:2009.12982).
-- source:
--   https://github.com/LionSR/MIPStarRE/blob/f382c801026f53a9efc260fdee707cb35e0adb15/MIPStarRE/LDT/Basic/PMFAverages.lean#L56-L774

-- Generated from MIPStarRE/LDT/Basic/PMFAverages.lean by skeleton subtraction.
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_Distribution
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_ParametersBase
import Definitions.Def_LIDT_MIPStarRE_Quantum_FiniteMatrix_Basic
import Definitions.Def_LIDT_MIPStarRE_Quantum_FiniteMatrix_BlockDiagonal
import Definitions.Def_LIDT_MIPStarRE_Quantum_FiniteMatrix_NormalizedTrace
import Definitions.Def_LIDT_MIPStarRE_Quantum_FiniteMatrix_Order
import Definitions.Def_LIDT_MIPStarRE_Quantum_FiniteMatrix_TracePairing
import Mathlib
import Mathlib.Analysis.MeanInequalitiesPow
import Mathlib.Probability.ProbabilityMassFunction.Monad

namespace LIDT

/-!
# PMF-weighted finite expectation identities

This module contains finite expectation identities stated directly for
Mathlib probability mass functions.  They connect `PMF.map` and
`PMF.bind` to the real-weighted finite sums used by the
low individual degree test averaging layer.

## Main declarations

* `PMF.map_apply_toReal`
* `PMF.realWeightedSum`
* `PMF.realWeightedSumLinearMap`
* `PMF.realWeightedSum_map`
* `PMF.realWeightedSum_bind`
* `PMF.map_sum_smul`
* `PMF.bind_apply_toReal`
* `PMF.bind_sum_smul`
* `PMF.sum_toReal_eq_one`
* `PMF.sum_const_smul`
* `PMF.totalVariationDistance`
* `PMF.totalVariationDistance_eq_sum_max_sub`
* `PMF.totalVariationDistance_uniformOfFintype_uniformOfFinset_eq`
* `PMF.sum_le_sum_add_totalVariationDistance`
* `PMF.sum_rpow_one_div_le_rpow_sum`
* `PMF.realWeightedSum_rpow_one_div_le_rpow`
* `PMF.uniformOfFintype_map_equiv`
* `PMF.uniformOfFintype_prod_apply_toReal`
* `PMF.uniformOfFintype_prod_eq_bind`
* `PMF.uniformOfFintype_sum_equiv_smul`
* `PMF.uniformOfFintype_prod_sum_smul`
* `PMF.uniformOfFintype_sum_equiv_fst_smul`
* `PMF.uniformOfFintype_sum_equiv_snd_smul`
* `PMF.uniformOfFintype_sum_factor_equiv_smul`
* `PMF.uniformOfFintype_sum_factor_equiv_fst_smul`
* `PMF.uniformOfFintype_sum_factor_equiv_snd_smul`

## References

These are formalization-internal finite probability lemmas for the low
individual degree test development.
-/

@[expose] public section

open scoped BigOperators

namespace PMF

/-- The finite real-weighted expectation of a module-valued function against a
probability mass function.  This is the finite-sum form of expectation used in
the low individual degree test, stated directly in Mathlib's `PMF` language. -/
noncomputable def realWeightedSum {α M : Type*} [Fintype α]
    [AddCommMonoid M] [Module MIPStarRE.LDT.Error M]
    (p : PMF α) (f : α → M) : M :=
  ∑ a : α, (p a).toReal • f a

/-- The finite PMF-weighted expectation as a linear map in the averaged family.

This is the linear form of `PMF.realWeightedSum`; it records that the
probability weights are fixed and the averaged object varies linearly. -/
noncomputable def realWeightedSumLinearMap {α M : Type*} [Fintype α]
    [AddCommMonoid M] [Module MIPStarRE.LDT.Error M]
    (p : PMF α) : (α → M) →ₗ[MIPStarRE.LDT.Error] M where
  toFun := fun f => realWeightedSum p f
  map_add' := by
    intro f g
    simp only [realWeightedSum, Pi.add_apply, smul_add, Finset.sum_add_distrib]
  map_smul' := by
    intro c f
    simp only [realWeightedSum, Pi.smul_apply]
    calc
      ∑ a : α, (p a).toReal • c • f a =
          ∑ a : α, c • ((p a).toReal • f a) := by
            refine Finset.sum_congr rfl ?_
            intro a _
            rw [smul_smul, smul_smul, mul_comm]
      _ = c • ∑ a : α, (p a).toReal • f a := by
            rw [Finset.smul_sum]

@[simp]
theorem realWeightedSumLinearMap_apply {α M : Type*} [Fintype α]
    [AddCommMonoid M] [Module MIPStarRE.LDT.Error M]
    (p : PMF α) (f : α → M) :
    realWeightedSumLinearMap p f = realWeightedSum p f :=
  rfl

/-- The finite total-variation distance between two probability mass functions,
written as half the `L^1` distance between their real weights.

This is the PMF form of the finite total-variation comparison used in
Proposition `prop:ld-dnoteq` of `references/ldt-paper/ld-pasting.tex`. -/
noncomputable def totalVariationDistance {α : Type*} [Fintype α]
    (p q : PMF α) : MIPStarRE.LDT.Error :=
  (1 / 2) * ∑ a : α, |(p a).toReal - (q a).toReal|

end PMF

namespace PMF

open Classical in
/-- Pointwise real-weight formula for a finite push-forward probability mass
function.  This is the finite real-valued form of `PMF.map_apply`. -/
theorem map_apply_toReal {α β : Type*} [Fintype α]
    (p : PMF α) (e : α → β) (b : β) :
    ((p.map e) b).toReal = ∑ a : α, (if b = e a then (p a).toReal else 0) := by
  rw [PMF.map_apply]
  rw [tsum_eq_sum fun a ha => (ha (Finset.mem_univ a)).elim]
  rw [ENNReal.toReal_sum]
  · refine Finset.sum_congr rfl ?_
    intro a _
    by_cases h : b = e a
    · rw [if_pos h, if_pos h]
    · rw [if_neg h, if_neg h]
      rfl
  · intro a _
    by_cases h : b = e a
    · simp [h, p.apply_ne_top a]
    · simp [h]

/-- A finite PMF-weighted sum against a push-forward is the corresponding
PMF-weighted sum of the pulled-back family. -/
theorem map_sum_smul {α β M : Type*}
    [Fintype α] [Fintype β]
    [AddCommMonoid M] [Module MIPStarRE.LDT.Error M]
    (p : PMF α) (e : α → β) (f : β → M) :
    ∑ b : β, ((p.map e) b).toReal • f b =
      ∑ a : α, (p a).toReal • f (e a) := by
  classical
  calc
    ∑ b : β, ((p.map e) b).toReal • f b
        = ∑ b : β, (∑ a : α, if b = e a then (p a).toReal else 0) • f b := by
          refine Finset.sum_congr rfl ?_
          intro b _
          rw [map_apply_toReal]
    _ = ∑ b : β, ∑ a : α, (if b = e a then (p a).toReal else 0) • f b := by
          refine Finset.sum_congr rfl ?_
          intro b _
          rw [Finset.sum_smul]
    _ = ∑ a : α, ∑ b : β, (if b = e a then (p a).toReal else 0) • f b := by
          rw [Finset.sum_comm]
    _ = ∑ a : α, (p a).toReal • f (e a) := by
          refine Finset.sum_congr rfl ?_
          intro a _
          rw [Fintype.sum_eq_single (e a)]
          · rw [if_pos rfl]
          · intro b hb
            rw [if_neg hb, zero_smul]

/-- Pointwise real-weight formula for a finite monadic composition of
probability mass functions.  This is the finite real-valued form of
`PMF.bind_apply`. -/
theorem bind_apply_toReal {α β : Type*} [Fintype α]
    (p : PMF α) (q : α → PMF β) (b : β) :
    ((p.bind q) b).toReal = ∑ a : α, (p a).toReal * (q a b).toReal := by
  rw [PMF.bind_apply]
  rw [tsum_eq_sum fun a ha => (ha (Finset.mem_univ a)).elim]
  rw [ENNReal.toReal_sum]
  · refine Finset.sum_congr rfl ?_
    intro a _
    rw [ENNReal.toReal_mul]
  · intro a _
    exact ENNReal.mul_ne_top (p.apply_ne_top a) ((q a).apply_ne_top b)

/-- A finite PMF-weighted sum against a monadic composition is the iterated
PMF-weighted sum. -/
theorem bind_sum_smul {α β M : Type*}
    [Fintype α] [Fintype β]
    [AddCommMonoid M] [Module MIPStarRE.LDT.Error M]
    (p : PMF α) (q : α → PMF β) (f : β → M) :
    ∑ b : β, ((p.bind q) b).toReal • f b =
      ∑ a : α, (p a).toReal • ∑ b : β, (q a b).toReal • f b := by
  calc
    ∑ b : β, ((p.bind q) b).toReal • f b
        = ∑ b : β, (∑ a : α, (p a).toReal * (q a b).toReal) • f b := by
          refine Finset.sum_congr rfl ?_
          intro b _
          rw [bind_apply_toReal]
    _ = ∑ b : β, ∑ a : α, ((p a).toReal * (q a b).toReal) • f b := by
          refine Finset.sum_congr rfl ?_
          intro b _
          rw [Finset.sum_smul]
    _ = ∑ a : α, ∑ b : β, ((p a).toReal * (q a b).toReal) • f b := by
          rw [Finset.sum_comm]
    _ = ∑ a : α, ∑ b : β, (p a).toReal • ((q a b).toReal • f b) := by
          refine Finset.sum_congr rfl ?_
          intro a _
          refine Finset.sum_congr rfl ?_
          intro b _
          simp [smul_smul]
    _ = ∑ a : α, (p a).toReal • ∑ b : β, (q a b).toReal • f b := by
          refine Finset.sum_congr rfl ?_
          intro a _
          rw [Finset.smul_sum]



/-- The uniform probability mass function on a product is the monadic
composition of the two coordinate-uniform probability mass functions. -/
theorem uniformOfFintype_prod_eq_bind
    {α β : Type*} [Fintype α] [Nonempty α] [Fintype β] [Nonempty β] :
    PMF.uniformOfFintype (α × β) =
      (PMF.uniformOfFintype α).bind
        (fun a => (PMF.uniformOfFintype β).map fun b => (a, b)) := by
  classical
  ext ab
  rw [PMF.bind_apply]
  rw [tsum_eq_single ab.1 (fun a ha => by
    have hmap_zero :
        ((PMF.uniformOfFintype β).map (fun b => (a, b)) ab) = 0 := by
      rw [PMF.map_apply]
      rw [ENNReal.tsum_eq_zero]
      intro b
      rw [if_neg (by
        intro h
        exact ha (congrArg Prod.fst h).symm)]
    rw [hmap_zero, mul_zero])]
  have hmap :
      ((PMF.uniformOfFintype β).map (fun b => (ab.1, b)) ab) =
        PMF.uniformOfFintype β ab.2 := by
    rw [PMF.map_apply]
    rw [tsum_eq_single ab.2 (fun b hb => by
      rw [if_neg (by
        intro h
        exact hb (congrArg Prod.snd h).symm)])]
    simp
  rw [hmap]
  simp only [PMF.uniformOfFintype_apply, Fintype.card_prod, Nat.cast_mul]
  exact ENNReal.mul_inv
    (a := (Fintype.card α : ENNReal))
    (b := (Fintype.card β : ENNReal))
    (Or.inl (by exact_mod_cast Fintype.card_ne_zero (α := α)))
    (Or.inl (ENNReal.natCast_ne_top (Fintype.card α)))

/-- The real weights of a finite probability mass function sum to one.

This is a Lean-only normalization lemma for transporting finite probability
calculations to Mathlib's `PMF` language. -/
theorem sum_toReal_eq_one {α : Type*} [Fintype α] (p : PMF α) :
    ∑ a : α, (p a).toReal = (1 : MIPStarRE.LDT.Error) := by
  have hweight_enn : (∑ a : α, p a) = (1 : ENNReal) := by
    rw [← (tsum_fintype (fun a : α => p a) :
      (∑' a : α, p a) = ∑ a : α, p a)]
    exact p.tsum_coe
  rw [← ENNReal.toReal_sum (s := Finset.univ)
    (f := fun a : α => p a) (fun a _ => p.apply_ne_top a)]
  rw [hweight_enn]
  norm_num

/-- The PMF-weighted sum of a constant family is the constant value. -/
theorem sum_const_smul {α M : Type*}
    [Fintype α] [AddCommMonoid M] [Module MIPStarRE.LDT.Error M]
    (p : PMF α) (x : M) :
    ∑ a : α, (p a).toReal • x = x := by
  calc
    ∑ a : α, (p a).toReal • x =
        (∑ a : α, (p a).toReal) • x := by
          exact (Finset.sum_smul (s := Finset.univ)
            (f := fun a : α => (p a).toReal) (x := x)).symm
    _ = x := by rw [sum_toReal_eq_one p, one_smul]

/-- Jensen's inequality for the concave power `x ↦ x ^ (1 / n)`, stated for a
finite probability mass function. -/
theorem sum_rpow_one_div_le_rpow_sum {α : Type*}
    [Fintype α]
    (p : PMF α) (f : α → MIPStarRE.LDT.Error) (n : ℕ)
    (hn : 1 ≤ n) (hf : ∀ a, 0 ≤ f a) :
    ∑ a : α, (p a).toReal * Real.rpow (f a) (1 / (n : MIPStarRE.LDT.Error)) ≤
      Real.rpow (∑ a : α, (p a).toReal * f a) (1 / (n : MIPStarRE.LDT.Error)) := by
  let z : α → MIPStarRE.LDT.Error :=
    fun a => Real.rpow (f a) (1 / (n : MIPStarRE.LDT.Error))
  have hw_nonneg : ∀ a ∈ (Finset.univ : Finset α), 0 ≤ (p a).toReal := by
    intro a _
    exact ENNReal.toReal_nonneg
  have hw_sum : ∑ a ∈ (Finset.univ : Finset α), (p a).toReal = 1 := by
    simpa using (sum_const_smul (p := p) (x := (1 : MIPStarRE.LDT.Error)))
  have hz_nonneg : ∀ a ∈ (Finset.univ : Finset α), 0 ≤ z a := by
    intro a _
    exact Real.rpow_nonneg (hf a) _
  have hn_nat_pos : 0 < n := lt_of_lt_of_le (by decide : 0 < 1) hn
  have hn_pos : 0 < (n : MIPStarRE.LDT.Error) := by
    exact_mod_cast hn_nat_pos
  have hp : (1 : MIPStarRE.LDT.Error) ≤ (n : MIPStarRE.LDT.Error) := by
    exact_mod_cast hn
  have hzpow : ∀ a, z a ^ (n : MIPStarRE.LDT.Error) = f a := by
    intro a
    calc
      z a ^ (n : MIPStarRE.LDT.Error) =
          (Real.rpow (f a) (1 / (n : MIPStarRE.LDT.Error))) ^ (n : MIPStarRE.LDT.Error) := by
          rfl
      _ = Real.rpow (f a) ((1 / (n : MIPStarRE.LDT.Error)) * (n : MIPStarRE.LDT.Error)) := by
          symm
          exact Real.rpow_mul (hf a) _ _
      _ = Real.rpow (f a) 1 := by
          congr 1
          field_simp [hn_pos.ne']
      _ = f a := by
          simp
  have hsum_eq :
      ∑ a ∈ (Finset.univ : Finset α), (p a).toReal * z a ^ (n : MIPStarRE.LDT.Error) =
        ∑ a ∈ (Finset.univ : Finset α), (p a).toReal * f a := by
    refine Finset.sum_congr rfl ?_
    intro a _
    rw [hzpow a]
  have hmean :=
    Real.arith_mean_le_rpow_mean (s := (Finset.univ : Finset α))
      (fun a => (p a).toReal) z hw_nonneg hw_sum hz_nonneg
      (p := (n : MIPStarRE.LDT.Error)) hp
  rw [hsum_eq] at hmean
  simpa [z] using hmean

/-- The uniform probability mass function is invariant under transport by an
equivalence. -/
theorem uniformOfFintype_map_equiv
    {α β : Type*} [Fintype α] [Nonempty α] [Fintype β] [Nonempty β]
    (e : α ≃ β) :
    (PMF.uniformOfFintype α).map e = PMF.uniformOfFintype β := by
  classical
  ext b
  rw [PMF.map_apply]
  rw [tsum_eq_single (e.symm b)]
  · simp [PMF.uniformOfFintype_apply, Fintype.card_congr e]
  · intro a ha
    rw [if_neg]
    intro hb
    exact ha (by
      calc
        a = e.symm (e a) := by simp
        _ = e.symm b := by rw [← hb])

/-- Reindex a finite sum weighted by Mathlib's uniform PMF along an equivalence. -/
theorem uniformOfFintype_sum_equiv_smul {α β M : Type*}
    [Fintype α] [Nonempty α] [Fintype β] [Nonempty β]
    [AddCommMonoid M] [Module MIPStarRE.LDT.Error M]
    (e : α ≃ β) (f : α → M) :
    ∑ a : α, (PMF.uniformOfFintype α a).toReal • f a =
      ∑ b : β, (PMF.uniformOfFintype β b).toReal • f (e.symm b) := by
  calc
    ∑ a : α, (PMF.uniformOfFintype α a).toReal • f a =
        ∑ b : β, (((PMF.uniformOfFintype α).map e) b).toReal • f (e.symm b) := by
          simpa using
            (map_sum_smul
              (p := PMF.uniformOfFintype α) (e := e)
              (f := fun b : β => f (e.symm b))).symm
    _ = ∑ b : β, (PMF.uniformOfFintype β b).toReal • f (e.symm b) := by
          rw [uniformOfFintype_map_equiv e]

/-- Split a finite sum weighted by the uniform PMF on a product into iterated
uniform PMF-weighted sums. -/
theorem uniformOfFintype_prod_sum_smul {α β M : Type*}
    [Fintype α] [Nonempty α] [Fintype β] [Nonempty β]
    [AddCommMonoid M] [Module MIPStarRE.LDT.Error M]
    (f : α → β → M) :
    ∑ ab : α × β, (PMF.uniformOfFintype (α × β) ab).toReal • f ab.1 ab.2 =
      ∑ a : α, (PMF.uniformOfFintype α a).toReal •
        ∑ b : β, (PMF.uniformOfFintype β b).toReal • f a b := by
  rw [uniformOfFintype_prod_eq_bind]
  rw [bind_sum_smul]
  refine Finset.sum_congr rfl ?_
  intro a _
  rw [map_sum_smul]

/-- Marginalize a uniform PMF-weighted sum along the first coordinate of a
product equivalence. -/
theorem uniformOfFintype_sum_equiv_fst_smul {γ α β M : Type*}
    [Fintype γ] [Nonempty γ]
    [Fintype α] [Nonempty α]
    [Finite β] [Nonempty β]
    [AddCommMonoid M] [Module MIPStarRE.LDT.Error M]
    (e : γ ≃ α × β) (f : α → M) :
    ∑ x : γ, (PMF.uniformOfFintype γ x).toReal • f (e x).1 =
      ∑ a : α, (PMF.uniformOfFintype α a).toReal • f a := by
  classical
  have := Fintype.ofFinite β
  calc
    ∑ x : γ, (PMF.uniformOfFintype γ x).toReal • f (e x).1
        = ∑ ab : α × β,
            (PMF.uniformOfFintype (α × β) ab).toReal • f ab.1 := by
          simpa using
            (uniformOfFintype_sum_equiv_smul
              (e := e) (f := fun x : γ => f (e x).1))
    _ = ∑ a : α, (PMF.uniformOfFintype α a).toReal •
          ∑ b : β, (PMF.uniformOfFintype β b).toReal • f a := by
          exact uniformOfFintype_prod_sum_smul (fun a (_ : β) => f a)
    _ = ∑ a : α, (PMF.uniformOfFintype α a).toReal • f a := by
          refine Finset.sum_congr rfl ?_
          intro a _
          rw [sum_const_smul]

/-- Marginalize a uniform PMF-weighted sum along the second coordinate of a
product equivalence. -/
theorem uniformOfFintype_sum_equiv_snd_smul {γ α β M : Type*}
    [Fintype γ] [Nonempty γ]
    [Finite α] [Nonempty α]
    [Fintype β] [Nonempty β]
    [AddCommMonoid M] [Module MIPStarRE.LDT.Error M]
    (e : γ ≃ α × β) (f : β → M) :
    ∑ x : γ, (PMF.uniformOfFintype γ x).toReal • f (e x).2 =
      ∑ b : β, (PMF.uniformOfFintype β b).toReal • f b := by
  classical
  have := Fintype.ofFinite α
  simpa using
    (uniformOfFintype_sum_equiv_fst_smul
      (e := e.trans (Equiv.prodComm α β)) (f := f))







end PMF

namespace PMF







/-- Reindex a finite expectation against Mathlib's uniform PMF along an
equivalence. -/
theorem realWeightedSum_uniformOfFintype_equiv {α β M : Type*}
    [Fintype α] [Nonempty α] [Fintype β] [Nonempty β]
    [AddCommMonoid M] [Module MIPStarRE.LDT.Error M]
    (e : α ≃ β) (f : α → M) :
    realWeightedSum (PMF.uniformOfFintype α) f =
      realWeightedSum (PMF.uniformOfFintype β) (fun b => f (e.symm b)) := by
  simpa [realWeightedSum] using
    uniformOfFintype_sum_equiv_smul (e := e) (f := f)

/-- Split a finite expectation against the uniform PMF on a product into
iterated finite expectations against the coordinate-uniform PMFs. -/
theorem realWeightedSum_uniformOfFintype_prod {α β M : Type*}
    [Fintype α] [Nonempty α] [Fintype β] [Nonempty β]
    [AddCommMonoid M] [Module MIPStarRE.LDT.Error M]
    (f : α → β → M) :
    realWeightedSum (PMF.uniformOfFintype (α × β)) (fun ab => f ab.1 ab.2) =
      realWeightedSum (PMF.uniformOfFintype α)
        (fun a => realWeightedSum (PMF.uniformOfFintype β) (fun b => f a b)) := by
  simpa [realWeightedSum] using
    uniformOfFintype_prod_sum_smul (f := f)













/-- Jensen's inequality for the concave power `x ↦ x ^ (1 / n)`, stated for the
finite expectation associated to a probability mass function. -/
theorem realWeightedSum_rpow_one_div_le_rpow {α : Type*}
    [Fintype α]
    (p : PMF α) (f : α → MIPStarRE.LDT.Error) (n : ℕ)
    (hn : 1 ≤ n) (hf : ∀ a, 0 ≤ f a) :
    realWeightedSum p (fun a => Real.rpow (f a) (1 / (n : MIPStarRE.LDT.Error))) ≤
      Real.rpow (realWeightedSum p f) (1 / (n : MIPStarRE.LDT.Error)) := by
  simpa [realWeightedSum, smul_eq_mul] using
    sum_rpow_one_div_le_rpow_sum
      (p := p) (f := f) (n := n) hn hf

end PMF

end

end LIDT


