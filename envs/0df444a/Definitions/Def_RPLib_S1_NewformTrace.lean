-- Prove2me | Definitions.Def_RPLib_S1_NewformTrace
-- name    : RPLib_S1_NewformTrace
-- status  : Definition
-- author  : @Nickrobbins95
-- created : 2026-11-13T05:34:47.928351+00:00
-- url     : https://prove2.me/theorems/565c412a-e175-4b53-8f05-33d0622485af
-- title:
--   Newforms are orthogonal to forms of lower level and have zero trace
-- statement:
--   For finite-index groups $\Gamma' \le \Gamma \le \mathrm{SL}_2(\mathbb{Z})$ and $g \in S_k(\Gamma')$ orthogonal to $S_k(\Gamma)$ for the Petersson product, the trace $$\operatorname{Tr}^{\Gamma}_{\Gamma'} g = \sum_{\gamma \in \Gamma'\backslash\Gamma} g|_k\gamma$$ vanishes. In particular every newform $f$ of level $M$ satisfies $\operatorname{Tr}_{M \to M/p} f = 0$ for each prime $p \mid M$.
--
--   **Formalization note.** This file is a library module of a formalization of the Ramanujan-Petersson conjecture for holomorphic cusp forms on $\Gamma_1(M)$. It contains definitions together with proved lemmas (no `sorry`), so that later solution files can import them.
-- source:
--   W.-C. W. Li, Newforms and functional equations, Math. Ann. 212 (1975) 285-315, doi:10.1007/BF01344468; F. Diamond and J. Shurman, A First Course in Modular Forms, GTM 228, Springer 2005, doi:10.1007/978-0-387-27226-9, Section 5.6

import Mathlib
import Definitions.Def_RPLib_S1_Newforms

/-!
# Newforms are killed by the trace to lower level

* Orthogonality API: `⟪h, f⟫ = ⟪f, h⟫ = 0` for `h` old (in particular `incl g`, `ι_p g`) and `f` new.
* `trace_eq_zero_of_orth`: for `Γ' ≤ Γ ≤ SL(2, ℤ)` (`Γ'` of finite index) and `g ∈ S_k(Γ')` Petersson
  orthogonal on `Γ'` to `S_k(Γ)`, the trace `Tr_{Γ'}^{Γ} g` (Mathlib `CuspForm.trace`) vanishes. This holds
  with no condition on `-1`: when `-1 ∈ Γ \ Γ'` and `k` is odd, `S_k(Γ) = 0`; when `k` is even, `g` is a
  cusp form for `±Γ'` (`toPm`), `Tr_{Γ'}^{Γ} g = n • Tr_{±Γ'}^{Γ} g` (`coe_trace_eq_card_smul`), and the
  trace adjointness for `±Γ' ≤ Γ` applies (`fdom (±Γ') = fdom Γ'`).
* `trace_G1_eq_zero_of_orth` (levels `L ∣ M`), `trace_eq_zero` (`Tr_{M → M/p} f = 0` for `f ∈ S^new(M)`),
  `IsNewform.trace_eq_zero`.
-/

set_option autoImplicit false
set_option linter.style.haveILetI false

open UpperHalfPlane ModularForm CongruenceSubgroup Matrix.SpecialLinearGroup
open scoped MatrixGroups

noncomputable section

namespace RP.NewformTrace

open RamanujanPetersson RamanujanPetersson.Diamond RP.Petersson RP.Adjoint RP.Newforms RP.FundDomain

/-! ## Orthogonality of old and new forms -/

section orth

variable {M : ℕ} [NeZero M] {k : ℤ}

theorem peterssonInner_old_new {h f : S1 M k} (hh : h ∈ oldSpace M k) (hf : f ∈ newSpace M k) :
    peterssonInner (Gamma1 M) k h f = 0 :=
  hf h hh

theorem peterssonInner_new_old {h f : S1 M k} (hh : h ∈ oldSpace M k) (hf : f ∈ newSpace M k) :
    peterssonInner (Gamma1 M) k f h = 0 := by
  rw [← peterssonInner_conj_symm, peterssonInner_old_new hh hf, map_zero]

theorem peterssonInner_inclP_new {p : ℕ} (hp : p ∈ M.primeFactors) (g : S1 (M / p) k) {f : S1 M k}
    (hf : f ∈ newSpace M k) : peterssonInner (Gamma1 M) k (inclP M k p g) f = 0 :=
  peterssonInner_old_new (inclP_mem_oldSpace hp g) hf

theorem peterssonInner_new_inclP {p : ℕ} (hp : p ∈ M.primeFactors) (g : S1 (M / p) k) {f : S1 M k}
    (hf : f ∈ newSpace M k) : peterssonInner (Gamma1 M) k f (inclP M k p g) = 0 :=
  peterssonInner_new_old (inclP_mem_oldSpace hp g) hf

theorem peterssonInner_iotaP_new {p : ℕ} (hp : p ∈ M.primeFactors) (g : S1 (M / p) k) {f : S1 M k}
    (hf : f ∈ newSpace M k) : peterssonInner (Gamma1 M) k (MainLemma.iotaP M p k g) f = 0 :=
  peterssonInner_old_new (iotaP_mem_oldSpace hp g) hf

theorem peterssonInner_new_iotaP {p : ℕ} (hp : p ∈ M.primeFactors) (g : S1 (M / p) k) {f : S1 M k}
    (hf : f ∈ newSpace M k) : peterssonInner (Gamma1 M) k f (MainLemma.iotaP M p k g) = 0 :=
  peterssonInner_new_old (iotaP_mem_oldSpace hp g) hf

end orth

/-! ## `±Γ` -/

section pm

lemma neg_one_mem_pmSL (Γ : Subgroup SL(2, ℤ)) : (-1 : SL(2, ℤ)) ∈ pmSL Γ :=
  mem_pmSL.2 (Or.inr (by rw [neg_neg]; exact Γ.one_mem))

lemma pmSL_le {Γ Γ' : Subgroup SL(2, ℤ)} (hle : Γ' ≤ Γ) (h1 : (-1 : SL(2, ℤ)) ∈ Γ) : pmSL Γ' ≤ Γ := by
  intro g hg
  rcases mem_pmSL.1 hg with h | h
  · exact hle h
  · have := Γ.mul_mem h1 (hle h)
    rwa [neg_one_mul, neg_neg] at this

lemma pmSL_pmSL (Γ : Subgroup SL(2, ℤ)) : pmSL (pmSL Γ) = pmSL Γ := by
  ext g
  constructor
  · intro h
    simp only [mem_pmSL, neg_neg] at h ⊢
    tauto
  · intro h
    exact le_pmSL _ h

lemma fdom_pmSL (Γ : Subgroup SL(2, ℤ)) : fdom (pmSL Γ) = fdom Γ := by
  unfold fdom
  rw [pmSL_pmSL]

lemma peterssonInner_pmSL (Γ : Subgroup SL(2, ℤ)) (k : ℤ) (f g : ℍ → ℂ) :
    peterssonInner (pmSL Γ) k f g = peterssonInner Γ k f g := by
  unfold peterssonInner
  rw [fdom_pmSL]

/-- In odd weight, a group containing `-1` has no nonzero cusp forms. -/
theorem cuspForm_eq_zero_of_odd {Γ : Subgroup SL(2, ℤ)} (h1 : (-1 : SL(2, ℤ)) ∈ Γ) {k : ℤ} (hk : Odd k)
    (F : CuspForm (Γ : Subgroup (GL (Fin 2) ℝ)) k) : F = 0 := by
  have h := slash_SL_eq (k := k) F h1
  rw [slash_neg_one, hk.neg_one_zpow, neg_one_smul] at h
  refine CuspForm.ext fun z => ?_
  have hz := congrFun h z
  rw [Pi.neg_apply] at hz
  show F z = 0
  linear_combination (-1 / 2 : ℂ) * hz

/-- In even weight, a cusp form for `Γ` is a cusp form for `±Γ` (same function). -/
def toPm {Γ : Subgroup SL(2, ℤ)} [Γ.FiniteIndex] {k : ℤ} (hk : Even k)
    (F : CuspForm (Γ : Subgroup (GL (Fin 2) ℝ)) k) :
    CuspForm (pmSL Γ : Subgroup (GL (Fin 2) ℝ)) k where
  toFun := ⇑F
  slash_action_eq' γ hγ := by
    obtain ⟨x, hx, rfl⟩ := Subgroup.mem_map.1 hγ
    rcases mem_pmSL.1 hx with h | h
    · exact SlashInvariantFormClass.slash_action_eq F _ (Subgroup.mem_map_of_mem _ h)
    · have e : x = (-1) * (-x) := by rw [neg_one_mul, neg_neg]
      have h1 : (⇑F : ℍ → ℂ) ∣[k] (mapGL ℝ (-1 : SL(2, ℤ))) = ⇑F := by
        have := slash_neg_one k (⇑F)
        rw [hk.neg_one_zpow, one_smul] at this
        exact this
      rw [e, map_mul, SlashAction.slash_mul, h1]
      exact SlashInvariantFormClass.slash_action_eq F _ (Subgroup.mem_map_of_mem _ h)
  holo' := CuspFormClass.holo F
  zero_at_cusps' hc := by
    haveI : (Γ : Subgroup (GL (Fin 2) ℝ)).IsFiniteRelIndex (pmSL Γ : Subgroup (GL (Fin 2) ℝ)) :=
      isFiniteRelIndex_coe
    exact CuspFormClass.zero_at_cusps F hc.of_isFiniteRelIndex

@[simp] lemma coe_toPm {Γ : Subgroup SL(2, ℤ)} [Γ.FiniteIndex] {k : ℤ} (hk : Even k)
    (F : CuspForm (Γ : Subgroup (GL (Fin 2) ℝ)) k) : ⇑(toPm hk F) = ⇑F := rfl

end pm

/-! ## Trace through an intermediate group -/

/-- For `𝒢 ≤ 𝒢''` and forms `g` on `𝒢`, `g''` on `𝒢''` with the same function,
`Tr_𝒢^ℋ g = n • Tr_{𝒢''}^ℋ g''` with `n = [𝒢'' ∩ ℋ : 𝒢 ∩ ℋ]`. -/
theorem coe_trace_eq_card_smul {𝒢 𝒢'' ℋ : Subgroup (GL (Fin 2) ℝ)} (h : 𝒢 ≤ 𝒢'') {k : ℤ}
    [𝒢.IsFiniteRelIndex ℋ] [𝒢''.IsFiniteRelIndex ℋ]
    (g : CuspForm 𝒢 k) (g'' : CuspForm 𝒢'' k) (hg : ⇑g'' = ⇑g) :
    ∃ n : ℕ, ⇑(CuspForm.trace ℋ g) = (n : ℂ) • ⇑(CuspForm.trace ℋ g'') := by
  classical
  have hst : 𝒢.subgroupOf ℋ ≤ 𝒢''.subgroupOf ℋ := fun x hx =>
    Subgroup.mem_subgroupOf.2 (h (Subgroup.mem_subgroupOf.1 hx))
  let e := Subgroup.quotientEquivProdOfLE hst
  letI : Fintype (ℋ ⧸ 𝒢.subgroupOf ℋ) := Fintype.ofFinite _
  letI : Fintype (ℋ ⧸ 𝒢''.subgroupOf ℋ) := Fintype.ofFinite _
  haveI : Finite (𝒢''.subgroupOf ℋ ⧸ (𝒢.subgroupOf ℋ).subgroupOf (𝒢''.subgroupOf ℋ)) :=
    Finite.of_injective (fun b => e.symm (QuotientGroup.mk (1 : ℋ), b))
      (fun b b' hb => (Prod.ext_iff.1 (e.symm.injective hb)).2)
  letI : Fintype (𝒢''.subgroupOf ℋ ⧸ (𝒢.subgroupOf ℋ).subgroupOf (𝒢''.subgroupOf ℋ)) :=
    Fintype.ofFinite _
  refine ⟨Fintype.card (𝒢''.subgroupOf ℋ ⧸ (𝒢.subgroupOf ℋ).subgroupOf (𝒢''.subgroupOf ℋ)), ?_⟩
  have h1 : ⇑(CuspForm.trace ℋ g) =
      ∑ q : ℋ ⧸ 𝒢.subgroupOf ℋ, SlashInvariantForm.quotientFunc (k := k) g q := rfl
  have h2 : ⇑(CuspForm.trace ℋ g'') =
      ∑ a : ℋ ⧸ 𝒢''.subgroupOf ℋ, SlashInvariantForm.quotientFunc (k := k) g'' a := rfl
  have hq : ∀ q : ℋ ⧸ 𝒢.subgroupOf ℋ, SlashInvariantForm.quotientFunc (k := k) g q =
      SlashInvariantForm.quotientFunc (k := k) g'' (e q).1 := by
    intro q
    induction q using Quotient.inductionOn with
    | h r =>
      show (⇑g : ℍ → ℂ) ∣[k] r.val⁻¹ = (⇑g'' : ℍ → ℂ) ∣[k] r.val⁻¹
      rw [hg]
  rw [h1, h2]
  calc (∑ q : ℋ ⧸ 𝒢.subgroupOf ℋ, SlashInvariantForm.quotientFunc (k := k) g q)
      = ∑ q : ℋ ⧸ 𝒢.subgroupOf ℋ, SlashInvariantForm.quotientFunc (k := k) g'' (e q).1 :=
        Finset.sum_congr rfl fun q _ => hq q
    _ = ∑ p : (ℋ ⧸ 𝒢''.subgroupOf ℋ) ×
          (𝒢''.subgroupOf ℋ ⧸ (𝒢.subgroupOf ℋ).subgroupOf (𝒢''.subgroupOf ℋ)),
          SlashInvariantForm.quotientFunc (k := k) g'' p.1 :=
        Fintype.sum_equiv e _ _ (fun q => rfl)
    _ = ∑ a : ℋ ⧸ 𝒢''.subgroupOf ℋ,
          ∑ _b : 𝒢''.subgroupOf ℋ ⧸ (𝒢.subgroupOf ℋ).subgroupOf (𝒢''.subgroupOf ℋ),
          SlashInvariantForm.quotientFunc (k := k) g'' a :=
        Fintype.sum_prod_type _
    _ = ∑ a : ℋ ⧸ 𝒢''.subgroupOf ℋ,
          (Fintype.card (𝒢''.subgroupOf ℋ ⧸ (𝒢.subgroupOf ℋ).subgroupOf (𝒢''.subgroupOf ℋ)) : ℂ) •
            SlashInvariantForm.quotientFunc (k := k) g'' a := by
        simp only [Finset.sum_const, Finset.card_univ, Nat.cast_smul_eq_nsmul]
    _ = _ := by rw [Finset.smul_sum]

/-! ## Trace vanishing -/

/-- **Trace vanishing.** For `Γ' ≤ Γ ≤ SL(2, ℤ)` with `Γ'` of finite index and `g ∈ S_k(Γ')` Petersson
orthogonal (on `Γ'`) to every `h ∈ S_k(Γ)` viewed on `Γ'`: `Tr_{Γ'}^{Γ} g = 0`. No condition on `-1`. -/
theorem trace_eq_zero_of_orth {Γ Γ' : Subgroup SL(2, ℤ)} (hle : Γ' ≤ Γ) [Γ'.FiniteIndex] {k : ℤ}
    [(Γ' : Subgroup (GL (Fin 2) ℝ)).IsFiniteRelIndex Γ]
    (g : CuspForm (Γ' : Subgroup (GL (Fin 2) ℝ)) k)
    (hg : ∀ h : CuspForm (Γ : Subgroup (GL (Fin 2) ℝ)) k, peterssonInner Γ' k h g = 0) :
    CuspForm.trace (Γ : Subgroup (GL (Fin 2) ℝ)) g = 0 := by
  have : Γ.FiniteIndex := Subgroup.finiteIndex_of_le hle
  by_cases hneg : (-1 : SL(2, ℤ)) ∈ Γ → (-1 : SL(2, ℤ)) ∈ Γ'
  · refine eq_zero_of_peterssonInner_self_eq_zero _ ?_
    rw [peterssonInner_trace hle hneg]
    exact hg _
  · push Not at hneg
    rcases Int.even_or_odd k with hk | hk
    · -- `k` even: pass through `±Γ'`
      have hle'' : pmSL Γ' ≤ Γ := pmSL_le hle hneg.1
      haveI : (pmSL Γ').FiniteIndex := Subgroup.finiteIndex_of_le (le_pmSL Γ')
      haveI : (pmSL Γ' : Subgroup (GL (Fin 2) ℝ)).IsFiniteRelIndex Γ := isFiniteRelIndex_coe
      obtain ⟨n, hn⟩ := coe_trace_eq_card_smul (ℋ := (Γ : Subgroup (GL (Fin 2) ℝ)))
        (Subgroup.map_mono (le_pmSL Γ')) g (toPm hk g) rfl
      have hT : CuspForm.trace (Γ : Subgroup (GL (Fin 2) ℝ)) g =
          (n : ℂ) • CuspForm.trace (Γ : Subgroup (GL (Fin 2) ℝ)) (toPm hk g) :=
        DFunLike.coe_injective (by rw [hn]; rfl)
      have key : peterssonInner Γ k (CuspForm.trace (Γ : Subgroup (GL (Fin 2) ℝ)) g)
          (CuspForm.trace (Γ : Subgroup (GL (Fin 2) ℝ)) g) = 0 := by
        calc peterssonInner Γ k (CuspForm.trace (Γ : Subgroup (GL (Fin 2) ℝ)) g)
              (CuspForm.trace (Γ : Subgroup (GL (Fin 2) ℝ)) g)
            = peterssonInner Γ k (CuspForm.trace (Γ : Subgroup (GL (Fin 2) ℝ)) g)
              ⇑((n : ℂ) • CuspForm.trace (Γ : Subgroup (GL (Fin 2) ℝ)) (toPm hk g)) := by
              rw [← hT]
          _ = (n : ℂ) * peterssonInner (pmSL Γ') k
              (CuspForm.trace (Γ : Subgroup (GL (Fin 2) ℝ)) g) (toPm hk g) := by
              rw [peterssonInner_smul_right, peterssonInner_trace hle'' (fun _ => neg_one_mem_pmSL Γ')]
          _ = 0 := by
              rw [peterssonInner_pmSL]
              exact mul_eq_zero_of_right _ (hg _)
      exact eq_zero_of_peterssonInner_self_eq_zero _ key
    · exact cuspForm_eq_zero_of_odd hneg.1 hk _

/-- `Γ₁(M)` has finite relative index in `Γ₁(L)` (as subgroups of `GL(2, ℝ)`). -/
instance instIsFiniteRelIndexG1 {L M : ℕ} [NeZero M] : (G1 M).IsFiniteRelIndex (G1 L) :=
  isFiniteRelIndex_coe (Γ := Gamma1 L) (Γ' := Gamma1 M)

/-- Trace vanishing between levels `L ∣ M`: if `g ∈ S_k(Γ₁(M))` is orthogonal to `incl S_k(Γ₁(L))`,
then `Tr_{M → L} g = 0`. -/
theorem trace_G1_eq_zero_of_orth {L M : ℕ} [NeZero M] (hLM : L ∣ M) {k : ℤ} (g : S1 M k)
    (hg : ∀ h : S1 L k, peterssonInner (Gamma1 M) k (Level.inclCF hLM k h) g = 0) :
    CuspForm.trace (G1 L) g = 0 :=
  trace_eq_zero_of_orth (Γ := Gamma1 L) (Γ' := Gamma1 M) (Level.Gamma1_le_of_dvd hLM) g
    (fun h => hg h)

/-- **Newforms have zero trace:** `Tr_{Γ₁(M) → Γ₁(M/p)} f = 0` for `f ∈ S^new(M)` and `p ∣ M`. -/
theorem trace_eq_zero {M : ℕ} [NeZero M] {k : ℤ} {p : ℕ} (hp : p ∈ M.primeFactors) {f : S1 M k}
    (hf : f ∈ newSpace M k) : CuspForm.trace (G1 (M / p)) f = 0 :=
  trace_G1_eq_zero_of_orth (Nat.div_dvd_of_dvd (Nat.dvd_of_mem_primeFactors hp)) f fun h => by
    have := peterssonInner_inclP_new hp h hf
    rwa [inclP_eq M k (Nat.dvd_of_mem_primeFactors hp)] at this

/-- A newform has zero trace to every level `M/p`, `p ∣ M`. -/
theorem _root_.RP.Newforms.IsNewform.trace_eq_zero {M : ℕ} [NeZero M] {k : ℤ}
    {χ : DirichletCharacter ℂ M} {f : S1 M k} (hf : IsNewform χ f) {p : ℕ} (hp : p ∈ M.primeFactors) :
    CuspForm.trace (G1 (M / p)) f = 0 :=
  RP.NewformTrace.trace_eq_zero hp hf.mem_new

end RP.NewformTrace


