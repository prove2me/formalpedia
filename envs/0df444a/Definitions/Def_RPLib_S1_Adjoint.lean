-- Prove2me | Definitions.Def_RPLib_S1_Adjoint
-- name    : RPLib_S1_Adjoint
-- status  : Definition
-- author  : @Nickrobbins95
-- created : 2026-11-13T05:23:24.907879+00:00
-- url     : https://prove2.me/theorems/0f179153-42a2-4794-99e8-ec1fb89e8313
-- title:
--   Adjoints of diamond and Hecke operators for the Petersson product
-- statement:
--   For $\alpha \in \mathrm{GL}_2^+(\mathbb{Q})$ the change of variables $\langle f|\alpha, g\rangle = \langle f, g|\alpha'\rangle$ with $\alpha' = \det(\alpha)\alpha^{-1}$ holds on the appropriate intersections of conjugate groups. Consequently the diamond operators are unitary and, for $p \nmid M$, $$\langle T_p f, g\rangle = \langle f, \langle p\rangle^{-1} T_p g\rangle,$$ so the operators $T_p$ with $p \nmid M$ are normal on $S_k(\Gamma_1(M))$ and on every $S_k(M,\chi)$.
--
--   **Formalization note.** This file is a library module of a formalization of the Ramanujan-Petersson conjecture for holomorphic cusp forms on $\Gamma_1(M)$. It contains definitions together with proved lemmas (no `sorry`), so that later solution files can import them.
-- source:
--   F. Diamond and J. Shurman, A First Course in Modular Forms, GTM 228, Springer 2005, doi:10.1007/978-0-387-27226-9, Section 5.5 (Proposition 5.5.2 and Theorem 5.5.3)

import Mathlib
import Definitions.Def_RPLib_S1_PeterssonInner
import Definitions.Def_RPLib_S1_Hecke

/-!
# S1-ADJOINT: adjoints for the Petersson product (diamonds, `T_p`)

Part 1 (general): `interConj Γ β = Γ ∩ β⁻¹ Γ β`, the change-of-variables lemma (DS Prop 5.5.2(a))
`⟪F ∣ α, G⟫_{Γ ∩ α⁻¹Γα} = ⟪F, G ∣ α'⟫_{Γ ∩ αΓα⁻¹}` with `α' = adj α`, a function-level trace adjointness
and the orbit lemma comparing `Σ_{q ∈ Γ/(Γ∩α⁻¹Γα)} F ∣ α q⁻¹` with a sum over orbit representatives.
-/

set_option autoImplicit false

open MeasureTheory Set Matrix Matrix.SpecialLinearGroup UpperHalfPlane ModularGroup ModularForm
open scoped MatrixGroups Modular Pointwise ComplexConjugate

noncomputable section

namespace RP.Adjoint

open RP.FundDomain RP.Petersson

attribute [local instance] measurableConstSMul_pgl smulInvariantMeasure_pgl
  smulInvariantMeasure_subgroup

/-! ### `Γ ∩ β⁻¹ Γ β` -/

/-- `Γ ∩ β⁻¹ Γ β` as a subgroup of `SL(2, ℤ)`: the `γ ∈ Γ` with `β γ β⁻¹ ∈ Γ`. -/
def interConj (Γ : Subgroup SL(2, ℤ)) (β : GL (Fin 2) ℝ) : Subgroup SL(2, ℤ) where
  carrier := {γ | γ ∈ Γ ∧ β * mapGL ℝ γ * β⁻¹ ∈ (Γ : Subgroup (GL (Fin 2) ℝ))}
  mul_mem' {a b} ha hb := ⟨Γ.mul_mem ha.1 hb.1, by
    have e : β * mapGL ℝ (a * b) * β⁻¹ = (β * mapGL ℝ a * β⁻¹) * (β * mapGL ℝ b * β⁻¹) := by
      rw [map_mul]; group
    rw [e]; exact Subgroup.mul_mem _ ha.2 hb.2⟩
  one_mem' := ⟨Γ.one_mem, by rw [map_one, mul_one, mul_inv_cancel]; exact Subgroup.one_mem _⟩
  inv_mem' {a} ha := ⟨Γ.inv_mem ha.1, by
    have e : β * mapGL ℝ a⁻¹ * β⁻¹ = (β * mapGL ℝ a * β⁻¹)⁻¹ := by
      rw [map_inv]; group
    rw [e]; exact Subgroup.inv_mem _ ha.2⟩

theorem mem_interConj {Γ : Subgroup SL(2, ℤ)} {β : GL (Fin 2) ℝ} {γ : SL(2, ℤ)} :
    γ ∈ interConj Γ β ↔ γ ∈ Γ ∧ β * mapGL ℝ γ * β⁻¹ ∈ (Γ : Subgroup (GL (Fin 2) ℝ)) :=
  Iff.rfl

theorem interConj_le (Γ : Subgroup SL(2, ℤ)) (β : GL (Fin 2) ℝ) : interConj Γ β ≤ Γ :=
  fun _ h => h.1

theorem mem_coe_interConj {Γ : Subgroup SL(2, ℤ)} {β x : GL (Fin 2) ℝ} :
    x ∈ (interConj Γ β : Subgroup (GL (Fin 2) ℝ)) ↔
      x ∈ (Γ : Subgroup (GL (Fin 2) ℝ)) ∧ β * x * β⁻¹ ∈ (Γ : Subgroup (GL (Fin 2) ℝ)) := by
  constructor
  · rintro ⟨γ, hγ, rfl⟩
    exact ⟨⟨γ, hγ.1, rfl⟩, hγ.2⟩
  · rintro ⟨⟨γ, hγ, rfl⟩, h⟩
    exact ⟨γ, ⟨hγ, h⟩, rfl⟩

/-- `-1` lies in `Γ ∩ β⁻¹Γβ` as soon as it lies in `Γ`. -/
theorem neg_one_mem_interConj {Γ : Subgroup SL(2, ℤ)} (β : GL (Fin 2) ℝ)
    (h : (-1 : SL(2, ℤ)) ∈ Γ) : (-1 : SL(2, ℤ)) ∈ interConj Γ β := by
  refine ⟨h, ?_⟩
  have e : β * mapGL ℝ (-1 : SL(2, ℤ)) * β⁻¹ = mapGL ℝ (-1 : SL(2, ℤ)) := by
    rw [mapGL_neg, map_one, mul_neg, neg_mul, mul_one, mul_inv_cancel]
  rw [e]
  exact ⟨-1, h, rfl⟩

/-- A criterion without inverses: `α γ = δ α` with `δ ∈ Γ`. -/
theorem mem_interConj_of {Γ : Subgroup SL(2, ℤ)} {α : GL (Fin 2) ℝ} {γ δ : SL(2, ℤ)}
    (hγ : γ ∈ Γ) (hδ : δ ∈ Γ) (h : α * mapGL ℝ γ = mapGL ℝ δ * α) : γ ∈ interConj Γ α := by
  refine ⟨hγ, ?_⟩
  have e : α * mapGL ℝ γ * α⁻¹ = mapGL ℝ δ := by rw [h]; group
  rw [e]
  exact ⟨δ, hδ, rfl⟩

/-- `Γ ∩ αΓα⁻¹ = α (Γ ∩ α⁻¹Γα) α⁻¹` (images in `GL(2, ℝ)`). -/
theorem coe_interConj_inv (Γ : Subgroup SL(2, ℤ)) (α : GL (Fin 2) ℝ) :
    (interConj Γ α⁻¹ : Subgroup (GL (Fin 2) ℝ)) =
      ConjAct.toConjAct α • (interConj Γ α : Subgroup (GL (Fin 2) ℝ)) := by
  ext x
  rw [Subgroup.mem_pointwise_smul_iff_inv_smul_mem, ConjAct.smul_def, mem_coe_interConj,
    mem_coe_interConj]
  simp only [ConjAct.ofConjAct_inv, ConjAct.ofConjAct_toConjAct, inv_inv]
  have e : α * (α⁻¹ * x * α) * α⁻¹ = x := by group
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨h2, by rw [e]; exact h1⟩
  · rintro ⟨h1, h2⟩
    rw [e] at h2
    exact ⟨h2, h1⟩

/-! ### Scalars and the adjugate `α' = det(α) α⁻¹` -/

theorem slash_scalar (k : ℤ) (u : ℝˣ) (hu : 0 < (u : ℝ)) (F : ℍ → ℂ) :
    F ∣[k] Matrix.GeneralLinearGroup.scalar (Fin 2) u = (((u : ℝ) : ℂ) ^ (k - 2)) • F := by
  ext τ
  have hdet : (Matrix.GeneralLinearGroup.scalar (Fin 2) u).det.val = (u : ℝ) ^ 2 := by
    simp [sq]
  have hpos : 0 < (Matrix.GeneralLinearGroup.scalar (Fin 2) u).det.val := by
    rw [hdet]; positivity
  have hu0 : ((u : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hu.ne'
  rw [ModularForm.slash_apply, glScalar_smul, denom_scalar, σ, if_pos hpos, hdet,
    abs_of_pos (by positivity)]
  simp only [ContinuousAlgEquiv.refl_apply, Pi.smul_apply, smul_eq_mul]
  have h1 : (((u : ℝ) ^ 2 : ℝ) : ℂ) ^ (k - 1) * ((u : ℝ) : ℂ) ^ (-k) = ((u : ℝ) : ℂ) ^ (k - 2) := by
    rw [Complex.ofReal_pow, ← zpow_natCast, ← _root_.zpow_mul, ← zpow_add₀ hu0]
    congr 1
    push_cast
    ring
  rw [mul_assoc, h1, mul_comm]

theorem adj_eq {α α' : GL (Fin 2) ℝ}
    (hα' : (α' : Matrix (Fin 2) (Fin 2) ℝ) = (α : Matrix (Fin 2) (Fin 2) ℝ).adjugate) :
    α' = α⁻¹ * Matrix.GeneralLinearGroup.scalar (Fin 2) α.det := by
  have h : α * α' = Matrix.GeneralLinearGroup.scalar (Fin 2) α.det := by
    refine Matrix.GeneralLinearGroup.ext fun i j => ?_
    rw [Matrix.GeneralLinearGroup.coe_mul, hα', Matrix.mul_adjugate,
      Matrix.GeneralLinearGroup.coe_scalar]
    fin_cases i <;> fin_cases j <;> simp
  rw [← h]
  group

theorem slash_adj (k : ℤ) {α α' : GL (Fin 2) ℝ} (hα : 0 < α.det.val)
    (hα' : (α' : Matrix (Fin 2) (Fin 2) ℝ) = (α : Matrix (Fin 2) (Fin 2) ℝ).adjugate) (G : ℍ → ℂ) :
    G ∣[k] α' = ((α.det.val : ℂ) ^ (k - 2)) • (G ∣[k] α⁻¹) := by
  rw [adj_eq hα', SlashAction.slash_mul, slash_scalar k α.det hα]

theorem interConj_adj (Γ : Subgroup SL(2, ℤ)) {α α' : GL (Fin 2) ℝ}
    (hα' : (α' : Matrix (Fin 2) (Fin 2) ℝ) = (α : Matrix (Fin 2) (Fin 2) ℝ).adjugate) :
    interConj Γ α' = interConj Γ α⁻¹ := by
  ext γ
  rw [mem_interConj, mem_interConj, adj_eq hα']
  set s := Matrix.GeneralLinearGroup.scalar (Fin 2) α.det
  have e : α⁻¹ * s * mapGL ℝ γ * (α⁻¹ * s)⁻¹ = α⁻¹ * mapGL ℝ γ * α⁻¹⁻¹ := by
    calc α⁻¹ * s * mapGL ℝ γ * (α⁻¹ * s)⁻¹ = α⁻¹ * (s * mapGL ℝ γ) * s⁻¹ * α := by group
      _ = α⁻¹ * (mapGL ℝ γ * s) * s⁻¹ * α := by
        rw [Matrix.GeneralLinearGroup.scalar_commute]
      _ = α⁻¹ * mapGL ℝ γ * α⁻¹⁻¹ := by group
  rw [e]

/-! ### The change-of-variables lemma (DS Prop. 5.5.2(a)) -/

/-- **Main lemma**, scalar form: for `det α > 0` and `Γ`-invariant `F`, `G`,
`⟪F ∣ α, G⟫_{Γ ∩ α⁻¹Γα} = det(α)^(k-2) ⟪F, G ∣ α⁻¹⟫_{Γ ∩ αΓα⁻¹}` (no integrability needed). -/
theorem peterssonInner_slash_eq {Γ : Subgroup SL(2, ℤ)} {k : ℤ} (α : GL (Fin 2) ℝ)
    (hα : 0 < α.det.val) {F G : ℍ → ℂ} (hF : ∀ γ ∈ Γ, F ∣[k] γ = F)
    (hG : ∀ γ ∈ Γ, G ∣[k] γ = G) :
    peterssonInner (interConj Γ α) k (F ∣[k] α) G =
      (α.det.val : ℂ) ^ (k - 2) * peterssonInner (interConj Γ α⁻¹) k F (G ∣[k] α⁻¹) := by
  have hG' : G = (G ∣[k] α⁻¹) ∣[k] α := by
    rw [← SlashAction.slash_mul, inv_mul_cancel, SlashAction.slash_one]
  have hpt : ∀ z, petersson k (F ∣[k] α) G z =
      (α.det.val : ℂ) ^ (k - 2) * petersson k F (G ∣[k] α⁻¹) (α • z) := by
    intro z
    conv_lhs => rw [hG']
    rw [petersson_slash, abs_of_pos hα, σ, if_pos hα, ContinuousAlgEquiv.refl_apply]
  unfold peterssonInner
  simp_rw [hpt]
  rw [integral_const_mul]
  congr 1
  rw [← setIntegral_gl_smul_set α (fdom (interConj Γ α)) (petersson k F (G ∣[k] α⁻¹))]
  refine setIntegral_eq_of_isFundamentalDomain (interConj Γ α⁻¹) ?_ (isFundamentalDomain_fdom _) ?_
  · have h := isFundamentalDomain_conj (isFundamentalDomain_fdom (interConj Γ α)) α
    rwa [← coe_interConj_inv] at h
  · intro γ hγ z
    refine petersson_smul_eq (Γ := interConj Γ α⁻¹) (fun δ hδ => hF δ hδ.1) (fun δ hδ => ?_) hγ z
    obtain ⟨t, ht, hte⟩ := hδ.2
    have e : α⁻¹ * mapGL ℝ δ = mapGL ℝ t * α⁻¹ := by rw [hte]; group
    have hGη : G ∣[k] mapGL ℝ t = G := hG t ht
    show (G ∣[k] α⁻¹) ∣[k] mapGL ℝ δ = G ∣[k] α⁻¹
    rw [← SlashAction.slash_mul, e, SlashAction.slash_mul, hGη]

/-- **Main lemma** (DS Prop. 5.5.2(a)): for `det α > 0`, `α' = adj α = det(α) α⁻¹` and
`Γ`-invariant `F`, `G`: `⟪F ∣ α, G⟫_{Γ ∩ α⁻¹Γα} = ⟪F, G ∣ α'⟫_{Γ ∩ α'⁻¹Γα'}`. -/
theorem peterssonInner_slash_adj {Γ : Subgroup SL(2, ℤ)} {k : ℤ} (α α' : GL (Fin 2) ℝ)
    (hα : 0 < α.det.val)
    (hα' : (α' : Matrix (Fin 2) (Fin 2) ℝ) = (α : Matrix (Fin 2) (Fin 2) ℝ).adjugate)
    {F G : ℍ → ℂ} (hF : ∀ γ ∈ Γ, F ∣[k] γ = F) (hG : ∀ γ ∈ Γ, G ∣[k] γ = G) :
    peterssonInner (interConj Γ α) k (F ∣[k] α) G =
      peterssonInner (interConj Γ α') k F (G ∣[k] α') := by
  rw [peterssonInner_slash_eq α hα hF hG, interConj_adj Γ hα', slash_adj k hα hα' G]
  unfold peterssonInner
  rw [← integral_const_mul]
  congr 1
  funext z
  simp only [petersson, Pi.smul_apply, smul_eq_mul]
  ring

/-! ### Trace adjointness at the level of functions -/

/-- For `Γ' ≤ Γ` of finite index (`-1 ∈ Γ → -1 ∈ Γ'`), `f ∈ S_k(Γ)` and `g` a cusp form for any
arithmetic group whose underlying function is `Γ'`-invariant:
`⟪f, Σ_{q ∈ Γ/Γ'} g ∣ q⁻¹⟫_Γ = ⟪f, g⟫_{Γ'}`. -/
theorem peterssonInner_sum_slash {Γ Γ' : Subgroup SL(2, ℤ)} (hle : Γ' ≤ Γ) [Γ'.FiniteIndex]
    (hneg : (-1 : SL(2, ℤ)) ∈ Γ → (-1 : SL(2, ℤ)) ∈ Γ') {k : ℤ}
    (f : CuspForm (Γ : Subgroup (GL (Fin 2) ℝ)) k) {𝒢 : Subgroup (GL (Fin 2) ℝ)} [𝒢.IsArithmetic]
    (g : CuspForm 𝒢 k) (hg : ∀ γ ∈ Γ', (⇑g) ∣[k] γ = ⇑g) [Fintype (CosetQ Γ Γ')] :
    peterssonInner Γ k f (∑ q : CosetQ Γ Γ', (⇑g) ∣[k] ((q.out : GL (Fin 2) ℝ)⁻¹)) =
      peterssonInner Γ' k f g := by
  have : Γ.FiniteIndex := Subgroup.finiteIndex_of_le hle
  obtain ⟨C, hC⟩ := exists_bound_petersson f g
  have hterm : ∀ (q : CosetQ Γ Γ') (z : ℍ),
      petersson k f (⇑g ∣[k] ((q.out : GL (Fin 2) ℝ)⁻¹)) z =
        petersson k f g ((q.out : GL (Fin 2) ℝ)⁻¹ • z) := by
    intro q z
    obtain ⟨γ, hγ, hγq⟩ := Subgroup.mem_map.1 ((Γ : Subgroup (GL (Fin 2) ℝ)).inv_mem q.out.2)
    rw [← hγq]
    change petersson k (⇑f) (⇑g ∣[k] γ) z = petersson k (⇑f) (⇑g) (γ • z)
    conv_lhs => rw [← slash_SL_eq f hγ]
    exact petersson_slash_SL k f g γ z
  have hpt : ∀ z, petersson k f (∑ q : CosetQ Γ Γ', (⇑g) ∣[k] ((q.out : GL (Fin 2) ℝ)⁻¹)) z =
      ∑ q : CosetQ Γ Γ', petersson k f g ((q.out : GL (Fin 2) ℝ)⁻¹ • z) := by
    intro z
    simp_rw [← hterm]
    simp only [petersson, Finset.sum_apply, Finset.mul_sum, Finset.sum_mul]
  unfold peterssonInner
  rw [setIntegral_fdom_eq_sum hle hneg (continuous_petersson f g).measurable hC
    (fun γ hγ z => petersson_smul_eq (fun δ hδ => slash_SL_eq f (hle hδ)) hg hγ z)]
  simp_rw [hpt]
  rw [integral_finsetSum]
  intro q _
  exact integrableOn_of_bounded (measurable_petersson_smul f g _).aestronglyMeasurable
    (fun z => hC _) (volume_fdom_lt_top Γ)

/-! ### The orbit lemma -/

/-- If `ρ : R → GL(2, ℝ)` is a set of representatives of `Γ \ ΓαΓ` (each `α γ` is in exactly one
orbit `Γ ρ r`, and each `ρ r ∈ ΓαΓ`), then `Σ_{q ∈ Γ/(Γ∩α⁻¹Γα)} F ∣ α q⁻¹ = Σ_r F ∣ ρ r` for
`Γ`-invariant `F`. -/
theorem sum_slash_out_eq {Γ : Subgroup SL(2, ℤ)} (α : GL (Fin 2) ℝ)
    [Fintype (CosetQ Γ (interConj Γ α))] {R : Type*} [Fintype R] (ρ : R → GL (Fin 2) ℝ)
    (hex : ∀ γ ∈ (Γ : Subgroup (GL (Fin 2) ℝ)), ∃ r, ∃ δ ∈ (Γ : Subgroup (GL (Fin 2) ℝ)),
      α * γ = δ * ρ r)
    (huniq : ∀ r s, ∀ δ ∈ (Γ : Subgroup (GL (Fin 2) ℝ)), ρ r = δ * ρ s → r = s)
    (hmem : ∀ r, ∃ γ ∈ (Γ : Subgroup (GL (Fin 2) ℝ)), ∃ δ ∈ (Γ : Subgroup (GL (Fin 2) ℝ)),
      ρ r = δ * α * γ)
    (k : ℤ) (F : ℍ → ℂ) (hF : ∀ γ ∈ (Γ : Subgroup (GL (Fin 2) ℝ)), F ∣[k] γ = F) :
    ∑ q : CosetQ Γ (interConj Γ α), F ∣[k] (α * (q.out : GL (Fin 2) ℝ)⁻¹) =
      ∑ r, F ∣[k] ρ r := by
  have hout : ∀ q : CosetQ Γ (interConj Γ α),
      ((q.out : GL (Fin 2) ℝ))⁻¹ ∈ (Γ : Subgroup (GL (Fin 2) ℝ)) :=
    fun q => Subgroup.inv_mem _ q.out.2
  choose σ δ hδ hσ using fun q : CosetQ Γ (interConj Γ α) => hex _ (hout q)
  have hterm : ∀ q, F ∣[k] (α * (q.out : GL (Fin 2) ℝ)⁻¹) = F ∣[k] ρ (σ q) := by
    intro q
    rw [hσ q, SlashAction.slash_mul, hF _ (hδ q)]
  simp only [hterm]
  refine Fintype.sum_bijective σ ⟨?_, ?_⟩ _ _ (fun q => rfl)
  · intro q q' h
    have hmemI : ((q.out : GL (Fin 2) ℝ))⁻¹ * (q'.out : GL (Fin 2) ℝ) ∈
        (interConj Γ α : Subgroup (GL (Fin 2) ℝ)) := by
      rw [mem_coe_interConj]
      refine ⟨Subgroup.mul_mem _ (hout q) q'.out.2, ?_⟩
      have h1 := hσ q
      have h2 := hσ q'
      rw [h] at h1
      have e : α * (((q.out : GL (Fin 2) ℝ))⁻¹ * (q'.out : GL (Fin 2) ℝ)) * α⁻¹ =
          δ q * (δ q')⁻¹ := by
        calc α * (((q.out : GL (Fin 2) ℝ))⁻¹ * (q'.out : GL (Fin 2) ℝ)) * α⁻¹
            = (α * ((q.out : GL (Fin 2) ℝ))⁻¹) * (α * ((q'.out : GL (Fin 2) ℝ))⁻¹)⁻¹ := by group
          _ = δ q * ρ (σ q') * (δ q' * ρ (σ q'))⁻¹ := by rw [h1, h2]
          _ = δ q * (δ q')⁻¹ := by group
      rw [e]
      exact Subgroup.mul_mem _ (hδ q) (Subgroup.inv_mem _ (hδ q'))
    rw [← QuotientGroup.out_eq' q, ← QuotientGroup.out_eq' q', QuotientGroup.eq,
      Subgroup.mem_subgroupOf, Subgroup.coe_mul, Subgroup.coe_inv]
    exact hmemI
  · intro r
    obtain ⟨γ, hγ, δ0, hδ0, hr⟩ := hmem r
    obtain ⟨j, hj⟩ := QuotientGroup.mk_out_eq_mul
      ((interConj Γ α : Subgroup (GL (Fin 2) ℝ)).subgroupOf (Γ : Subgroup (GL (Fin 2) ℝ)))
      (⟨γ⁻¹, Subgroup.inv_mem _ hγ⟩ : (Γ : Subgroup (GL (Fin 2) ℝ)))
    refine ⟨QuotientGroup.mk ⟨γ⁻¹, Subgroup.inv_mem _ hγ⟩, ?_⟩
    set q : CosetQ Γ (interConj Γ α) := QuotientGroup.mk ⟨γ⁻¹, Subgroup.inv_mem _ hγ⟩ with hqdef
    have hjm : ((j : (Γ : Subgroup (GL (Fin 2) ℝ))) : GL (Fin 2) ℝ) ∈
        (interConj Γ α : Subgroup (GL (Fin 2) ℝ)) := Subgroup.mem_subgroupOf.1 j.2
    have hq : ((q.out : (Γ : Subgroup (GL (Fin 2) ℝ))) : GL (Fin 2) ℝ) =
        γ⁻¹ * ((j : (Γ : Subgroup (GL (Fin 2) ℝ))) : GL (Fin 2) ℝ) := by
      rw [hj]; rfl
    set J : GL (Fin 2) ℝ := ((j : (Γ : Subgroup (GL (Fin 2) ℝ))) : GL (Fin 2) ℝ)
    have hjc : α * J * α⁻¹ ∈ (Γ : Subgroup (GL (Fin 2) ℝ)) := (mem_coe_interConj.1 hjm).2
    have h1 := hσ q
    rw [hq] at h1
    refine huniq (σ q) r ((δ q)⁻¹ * (α * J * α⁻¹)⁻¹ * δ0⁻¹) ?_ ?_
    · exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.inv_mem _ (hδ q))
        (Subgroup.inv_mem _ hjc)) (Subgroup.inv_mem _ hδ0)
    · calc ρ (σ q) = (δ q)⁻¹ * (α * (γ⁻¹ * J)⁻¹) := by rw [h1]; group
        _ = (δ q)⁻¹ * (α * J * α⁻¹)⁻¹ * δ0⁻¹ * (δ0 * α * γ) := by group
        _ = (δ q)⁻¹ * (α * J * α⁻¹)⁻¹ * δ0⁻¹ * ρ r := by rw [← hr]

/-- Slash invariance of `F ∣ α` under `Γ ∩ α⁻¹Γα`. -/
theorem slash_interConj_eq {Γ : Subgroup SL(2, ℤ)} {k : ℤ} {F : ℍ → ℂ}
    (hF : ∀ γ ∈ (Γ : Subgroup (GL (Fin 2) ℝ)), F ∣[k] γ = F) (α : GL (Fin 2) ℝ) {γ : SL(2, ℤ)}
    (hγ : γ ∈ interConj Γ α) : (F ∣[k] α) ∣[k] γ = F ∣[k] α := by
  change (F ∣[k] α) ∣[k] mapGL ℝ γ = F ∣[k] α
  rw [← SlashAction.slash_mul]
  have e : α * mapGL ℝ γ = (α * mapGL ℝ γ * α⁻¹) * α := by group
  rw [e, SlashAction.slash_mul, hF _ hγ.2]

/-! ### Diamond operators are unitary -/

section diamond

open RamanujanPetersson.Diamond CongruenceSubgroup

variable {M : ℕ}

theorem interConj_Gamma0 {γ : SL(2, ℤ)} (hγ : γ ∈ Gamma0 M) :
    interConj (Gamma1 M) (mapGL ℝ γ) = Gamma1 M := by
  ext δ
  rw [mem_interConj]
  refine ⟨fun h => h.1, fun h => ⟨h, ⟨γ * δ * γ⁻¹, conj_mem_Gamma1 hγ h, ?_⟩⟩⟩
  simp only [map_mul, map_inv]

theorem mapGL_adj (γ : SL(2, ℤ)) :
    ((mapGL ℝ γ⁻¹ : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) =
      ((mapGL ℝ γ : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ).adjugate := by
  rw [mapGL_coe_matrix, mapGL_coe_matrix, map_inv, Matrix.SpecialLinearGroup.coe_inv]

theorem mapGL_det_pos (γ : SL(2, ℤ)) : 0 < (mapGL ℝ γ).det.val := by
  simp

variable [NeZero M]

/-- `⟪⟨d⟩ f, g⟫ = ⟪f, ⟨d⁻¹⟩ g⟫` on `S_k(Γ₁(M))`: the diamond operators are unitary. -/
theorem peterssonInner_diamond (k : ℤ) (d : (ZMod M)ˣ) (f g : S1 M k) :
    peterssonInner (Gamma1 M) k (diamond k d f) g =
      peterssonInner (Gamma1 M) k f (diamond k d⁻¹ g) := by
  set γ : Gamma0 M := lift0 d
  have h1 : ⇑(diamond k d f) = ⇑f ∣[k] mapGL ℝ (γ : SL(2, ℤ)) := by
    rw [diamond_apply, coe_slashG0]; rfl
  have h2 : ⇑(diamond k d⁻¹ g) = ⇑g ∣[k] mapGL ℝ ((γ : SL(2, ℤ))⁻¹) := by
    have : d⁻¹ = unitMap M γ⁻¹ := by rw [map_inv, unitMap_lift0]
    rw [this, diamond_unitMap, coe_slashG0]; rfl
  have := peterssonInner_slash_adj (Γ := Gamma1 M) (k := k) _ _ (mapGL_det_pos _)
    (mapGL_adj (γ : SL(2, ℤ))) (F := ⇑f) (G := ⇑g)
    (fun δ hδ => slash_Gamma1 k f hδ) (fun δ hδ => slash_Gamma1 k g hδ)
  rw [interConj_Gamma0 γ.2, interConj_Gamma0 (Subgroup.inv_mem _ γ.2)] at this
  rw [h1, h2]
  exact this

theorem peterssonInner_diamond_right (k : ℤ) (d : (ZMod M)ˣ) (f g : S1 M k) :
    peterssonInner (Gamma1 M) k f (diamond k d g) =
      peterssonInner (Gamma1 M) k (diamond k d⁻¹ f) g := by
  rw [peterssonInner_diamond, inv_inv]

end diamond

/-! ### `T_p` for `p ∤ M`: coset representatives -/

section TpMat

open RamanujanPetersson RamanujanPetersson.Diamond RamanujanPetersson.Hecke CongruenceSubgroup

variable {M p : ℕ}

/-- `[[x p, y], [M, 1]] ∈ Γ₁(M)` for `x p - y M = 1`. -/
def gammaInf (M p : ℕ) (x y : ℤ) (hxy : x * p - y * M = 1) : SL(2, ℤ) :=
  ⟨!![x * p, y; (M : ℤ), 1], by rw [Matrix.det_fin_two_of]; linear_combination hxy⟩

/-- `[[1, j], [0, 1]]`. -/
def gammaT (j : ℤ) : SL(2, ℤ) :=
  ⟨!![1, j; 0, 1], by rw [Matrix.det_fin_two_of]; ring⟩

/-- `β_r = α γ_r` with `α = diag(1, p)`. -/
def gammaR (M p : ℕ) (x y : ℤ) (hxy : x * p - y * M = 1) : Option (Fin p) → SL(2, ℤ)
  | none => gammaInf M p x y hxy
  | some j => gammaT ((j : ℕ) : ℤ)

lemma xp_eq_one (x y : ℤ) (hxy : x * p - y * M = 1) : (x : ZMod M) * (p : ZMod M) = 1 := by
  have h := congrArg (fun z : ℤ => (z : ZMod M)) hxy
  simp only [Int.cast_sub, Int.cast_mul, Int.cast_natCast, Int.cast_one, ZMod.natCast_self,
    mul_zero, sub_zero] at h
  exact h

lemma gammaInf_mem (x y : ℤ) (hxy : x * p - y * M = 1) : gammaInf M p x y hxy ∈ Gamma1 M := by
  refine mem_Gamma1_of _ ?_ ?_
  · simp only [gammaInf, Matrix.SpecialLinearGroup.coe_mk, Matrix.of_apply, Matrix.cons_val',
      Matrix.cons_val_zero, Matrix.empty_val', Matrix.cons_val_fin_one]
    push_cast
    exact xp_eq_one x y hxy
  · simp [gammaInf]

lemma gammaT_mem (j : ℤ) : gammaT j ∈ Gamma1 M :=
  mem_Gamma1_of _ (by simp [gammaT]) (by simp [gammaT])

lemma gammaR_mem (x y : ℤ) (hxy : x * p - y * M = 1) : ∀ r, gammaR M p x y hxy r ∈ Gamma1 M
  | none => gammaInf_mem x y hxy
  | some j => gammaT_mem _

lemma repU_eq_mul (j : ℕ) :
    repU p j = repU p 0 * ((gammaT (j : ℤ) : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) := by
  ext i l
  fin_cases i <;> fin_cases l <;> simp [repU, gammaT, Matrix.mul_apply, Fin.sum_univ_two]

lemma repInf_eq_mul (x y : ℤ) (hxy : x * p - y * M = 1) :
    repInf M p x y = repU p 0 * ((gammaInf M p x y hxy : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) := by
  ext i l
  fin_cases i <;> fin_cases l <;>
    simp [repInf, repU, gammaInf, Matrix.mul_apply, Fin.sum_univ_two] <;> ring1

lemma betaOpt_eq_mul (x y : ℤ) (hxy : x * p - y * M = 1) :
    ∀ r, betaOpt M p x y r =
      repU p 0 * ((gammaR M p x y hxy r : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ)
  | none => repInf_eq_mul x y hxy
  | some j => repU_eq_mul (p := p) j

lemma isDelta_repU0_mul {γ : SL(2, ℤ)} (hγ : γ ∈ Gamma1 M) :
    IsDelta M p (repU p 0 * (γ : Matrix (Fin 2) (Fin 2) ℤ)) := by
  obtain ⟨h00, -, h10⟩ := (Gamma1_mem M γ).1 hγ
  refine ⟨?_, ?_, ?_⟩
  · rw [Matrix.det_mul, det_repU, Matrix.SpecialLinearGroup.det_coe, mul_one]
  · simp [repU, Matrix.mul_apply, Fin.sum_univ_two, h10]
  · simp [repU, Matrix.mul_apply, Fin.sum_univ_two, h00]

lemma condOpt_of_mul (x y : ℤ) (δ : Matrix (Fin 2) (Fin 2) ℤ) :
    ∀ r, condOpt p (δ * betaOpt M p x y r) r
  | none => condInf_of_mul δ x y
  | some j => condU_of_mul δ j

lemma dvd_of_mem_Gamma {N : ℕ} {δ : SL(2, ℤ)} (h : δ ∈ Gamma N) :
    (N : ℤ) ∣ δ 0 0 - 1 ∧ (N : ℤ) ∣ δ 0 1 ∧ (N : ℤ) ∣ δ 1 0 ∧ (N : ℤ) ∣ δ 1 1 - 1 := by
  obtain ⟨h00, h01, h10, h11⟩ := Gamma_mem.1 h
  refine ⟨?_, (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).1 h01,
    (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).1 h10, ?_⟩
  · rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]; push_cast; rw [h00, sub_self]
  · rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]; push_cast; rw [h11, sub_self]

lemma one_of_dvd {a : ℤ} (h : (M : ℤ) ∣ a - 1) : (a : ZMod M) = 1 := by
  have := (ZMod.intCast_zmod_eq_zero_iff_dvd (a - 1) M).2 h
  push_cast at this
  exact sub_eq_zero.1 this

lemma zero_of_dvd {a : ℤ} (h : (M : ℤ) ∣ a) : (a : ZMod M) = 0 :=
  (ZMod.intCast_zmod_eq_zero_iff_dvd a M).2 h

end TpMat

section TpPrime

open RamanujanPetersson RamanujanPetersson.Diamond RamanujanPetersson.Hecke CongruenceSubgroup

variable {M p : ℕ} [hp : Fact p.Prime]

lemma condOpt_unique {A : Matrix (Fin 2) (Fin 2) ℤ} (hdet : A.det = p) {r s : Option (Fin p)}
    (hr : condOpt p A r) (hs : condOpt p A s) : r = s := by
  cases r with
  | none =>
    cases s with
    | none => rfl
    | some j => exact (condU_condInf hdet hs hr).elim
  | some i =>
    cases s with
    | none => exact (condU_condInf hdet hr hs).elim
    | some j => exact congrArg some (Fin.ext (condU_unique hdet i.isLt j.isLt hr hs))

lemma betaOpt_unique (x y : ℤ) (hxy : x * p - y * M = 1) (r s : Option (Fin p)) (δ : SL(2, ℤ))
    (h : betaOpt M p x y r = (δ : Matrix (Fin 2) (Fin 2) ℤ) * betaOpt M p x y s) : r = s := by
  have hr : condOpt p (betaOpt M p x y r) r := by
    simpa only [one_mul] using condOpt_of_mul (M := M) x y 1 r
  have hs : condOpt p (betaOpt M p x y r) s := by rw [h]; exact condOpt_of_mul x y _ s
  exact condOpt_unique (isDelta_betaOpt x y hxy r).1 hr hs

lemma exists_betaOpt_factor (x y : ℤ) (hxy : x * p - y * M = 1) {A : Matrix (Fin 2) (Fin 2) ℤ}
    (hA : IsDelta M p A) : ∃ r, ∃ δ : SL(2, ℤ), δ ∈ Gamma1 M ∧
      (δ : Matrix (Fin 2) (Fin 2) ℤ) * betaOpt M p x y r = A := by
  by_cases hc : CondInf p A
  · exact ⟨none, factor_Inf hA hc x y hxy⟩
  · obtain ⟨j, hj, hcj⟩ := exists_condU hA.1 hc
    exact ⟨some ⟨j, hj⟩, factor_U hA hcj⟩

lemma exists_xy (hpM : ¬ p ∣ M) : ∃ x y : ℤ, x * p - y * M = 1 := by
  obtain ⟨u, v, huv⟩ := Nat.isCoprime_iff_coprime.2 (coprime_of_not_dvd hpM)
  exact ⟨u, -v, by linear_combination huv⟩

variable (p) in
/-- `α = [[1, 0], [0, p]]`. -/
def alphaP : GL (Fin 2) ℝ := Hecke.toGL (repU p 0) (det_repU_ne 0)

variable (p) in
/-- `α' = adj α = [[p, 0], [0, 1]]`. -/
def alphaD : GL (Fin 2) ℝ := Hecke.toGL (diagP p) det_diagP_ne

/-- The representatives `β_r` of `Γ₁(M) \ Γ₁(M) α Γ₁(M)`, in `GL(2, ℝ)`. -/
def rhoP (M p : ℕ) [Fact p.Prime] (x y : ℤ) (hxy : x * p - y * M = 1) (r : Option (Fin p)) :
    GL (Fin 2) ℝ :=
  Hecke.toGL (betaOpt M p x y r) (isDelta_det_ne (isDelta_betaOpt x y hxy r))

lemma rhoP_eq (x y : ℤ) (hxy : x * p - y * M = 1) (r : Option (Fin p)) :
    rhoP M p x y hxy r = alphaP p * mapGL ℝ (gammaR M p x y hxy r) := by
  rw [rhoP, alphaP, toGL_mul_mapGL]
  exact toGL_congr _ _ (betaOpt_eq_mul x y hxy r)

lemma rhoP_unique (x y : ℤ) (hxy : x * p - y * M = 1) (r s : Option (Fin p)) (δ : SL(2, ℤ))
    (h : rhoP M p x y hxy r = mapGL ℝ δ * rhoP M p x y hxy s) : r = s := by
  unfold rhoP at h
  rw [mapGL_mul_toGL] at h
  exact betaOpt_unique x y hxy r s δ (Hecke.toGL_injective _ _ _ _ h)

lemma hexB' (x y : ℤ) (hxy : x * p - y * M = 1) {γ : SL(2, ℤ)} (hγ : γ ∈ Gamma1 M) :
    ∃ r, ∃ δ : SL(2, ℤ), δ ∈ Gamma1 M ∧
      alphaP p * mapGL ℝ γ = mapGL ℝ δ * rhoP M p x y hxy r := by
  obtain ⟨r, δ, hδ, he⟩ := exists_betaOpt_factor x y hxy (isDelta_repU0_mul (p := p) hγ)
  refine ⟨r, δ, hδ, ?_⟩
  rw [alphaP, rhoP, toGL_mul_mapGL, mapGL_mul_toGL]
  exact toGL_congr _ _ he.symm

lemma hexB (x y : ℤ) (hxy : x * p - y * M = 1) :
    ∀ γ ∈ (Gamma1 M : Subgroup (GL (Fin 2) ℝ)), ∃ r, ∃ δ ∈ (Gamma1 M : Subgroup (GL (Fin 2) ℝ)),
      alphaP p * γ = δ * rhoP M p x y hxy r := by
  rintro _ ⟨γ, hγ, rfl⟩
  obtain ⟨r, δ, hδ, he⟩ := hexB' x y hxy hγ
  exact ⟨r, mapGL ℝ δ, ⟨δ, hδ, rfl⟩, he⟩

lemma huniqB (x y : ℤ) (hxy : x * p - y * M = 1) :
    ∀ r s, ∀ δ ∈ (Gamma1 M : Subgroup (GL (Fin 2) ℝ)),
      rhoP M p x y hxy r = δ * rhoP M p x y hxy s → r = s := by
  rintro r s _ ⟨δ, -, rfl⟩ h
  exact rhoP_unique x y hxy r s δ h

lemma hmemB (x y : ℤ) (hxy : x * p - y * M = 1) :
    ∀ r, ∃ γ ∈ (Gamma1 M : Subgroup (GL (Fin 2) ℝ)), ∃ δ ∈ (Gamma1 M : Subgroup (GL (Fin 2) ℝ)),
      rhoP M p x y hxy r = δ * alphaP p * γ := fun r =>
  ⟨_, ⟨_, gammaR_mem x y hxy r, rfl⟩, 1, Subgroup.one_mem _, by rw [one_mul, rhoP_eq]⟩

lemma sigma_mul_alphaD (x y : ℤ) (hxy : x * p - y * M = 1) :
    mapGL ℝ (sigmaP M p x y hxy) * alphaD p = alphaP p * mapGL ℝ (gammaInf M p x y hxy) := by
  rw [alphaD, ← upperTri_D_eq, sigmaP_mul_diag, alphaP, toGL_mul_mapGL]
  exact toGL_congr _ _ (repInf_eq_mul x y hxy)

lemma hexC (x y : ℤ) (hxy : x * p - y * M = 1) :
    ∀ γ ∈ (Gamma1 M : Subgroup (GL (Fin 2) ℝ)), ∃ r, ∃ δ ∈ (Gamma1 M : Subgroup (GL (Fin 2) ℝ)),
      alphaD p * γ = δ * ((mapGL ℝ (sigmaP M p x y hxy))⁻¹ * rhoP M p x y hxy r) := by
  rintro _ ⟨γ, hγ, rfl⟩
  obtain ⟨r, δ, hδ, he⟩ := hexB' x y hxy (Subgroup.mul_mem _ (gammaInf_mem x y hxy) hγ)
  refine ⟨r, mapGL ℝ ((sigmaP M p x y hxy)⁻¹ * δ * (sigmaP M p x y hxy)⁻¹⁻¹),
    ⟨_, conj_mem_Gamma1 (Subgroup.inv_mem _ (sigmaP_mem x y hxy)) hδ, rfl⟩, ?_⟩
  have hk := sigma_mul_alphaD x y hxy
  have e : alphaD p =
      (mapGL ℝ (sigmaP M p x y hxy))⁻¹ * (alphaP p * mapGL ℝ (gammaInf M p x y hxy)) := by
    rw [← hk]; group
  calc alphaD p * mapGL ℝ γ
      = (mapGL ℝ (sigmaP M p x y hxy))⁻¹ * (alphaP p * mapGL ℝ (gammaInf M p x y hxy * γ)) := by
        rw [e]; simp only [map_mul]; group
    _ = (mapGL ℝ (sigmaP M p x y hxy))⁻¹ * (mapGL ℝ δ * rhoP M p x y hxy r) := by rw [he]
    _ = _ := by simp only [map_mul, map_inv, inv_inv]; group

lemma huniqC (x y : ℤ) (hxy : x * p - y * M = 1) :
    ∀ r s, ∀ δ ∈ (Gamma1 M : Subgroup (GL (Fin 2) ℝ)),
      (mapGL ℝ (sigmaP M p x y hxy))⁻¹ * rhoP M p x y hxy r =
        δ * ((mapGL ℝ (sigmaP M p x y hxy))⁻¹ * rhoP M p x y hxy s) → r = s := by
  rintro r s _ ⟨δ, -, rfl⟩ h
  refine rhoP_unique x y hxy r s (sigmaP M p x y hxy * δ * (sigmaP M p x y hxy)⁻¹) ?_
  have e : rhoP M p x y hxy r = mapGL ℝ (sigmaP M p x y hxy) *
      (mapGL ℝ δ * ((mapGL ℝ (sigmaP M p x y hxy))⁻¹ * rhoP M p x y hxy s)) := by
    rw [← h]; group
  rw [e]; simp only [map_mul, map_inv]; group

lemma hmemC (x y : ℤ) (hxy : x * p - y * M = 1) :
    ∀ r, ∃ γ ∈ (Gamma1 M : Subgroup (GL (Fin 2) ℝ)), ∃ δ ∈ (Gamma1 M : Subgroup (GL (Fin 2) ℝ)),
      (mapGL ℝ (sigmaP M p x y hxy))⁻¹ * rhoP M p x y hxy r = δ * alphaD p * γ := by
  intro r
  refine ⟨mapGL ℝ ((gammaInf M p x y hxy)⁻¹ * gammaR M p x y hxy r),
    ⟨_, Subgroup.mul_mem _ (Subgroup.inv_mem _ (gammaInf_mem x y hxy)) (gammaR_mem x y hxy r), rfl⟩,
    1, Subgroup.one_mem _, ?_⟩
  have hk := sigma_mul_alphaD x y hxy
  have e : alphaP p = mapGL ℝ (sigmaP M p x y hxy) * alphaD p *
      (mapGL ℝ (gammaInf M p x y hxy))⁻¹ := by
    rw [hk]; group
  rw [rhoP_eq, e]
  simp only [map_mul, map_inv]
  group

lemma unitP_inv_eq (x y : ℤ) (hxy : x * p - y * M = 1) (hpM : ¬ p ∣ M) :
    (((unitP hpM)⁻¹ : (ZMod M)ˣ) : ZMod M) =
      ((((sigmaP M p x y hxy)⁻¹ : SL(2, ℤ)) 1 1 : ℤ) : ZMod M) := by
  have h11 : (((sigmaP M p x y hxy)⁻¹ : SL(2, ℤ)) 1 1 : ℤ) = x := by
    rw [Matrix.SpecialLinearGroup.coe_inv, Matrix.adjugate_fin_two]
    simp [sigmaP]
  rw [h11]
  have h1 := xp_eq_one x y hxy
  have h2 : ((unitP hpM : (ZMod M)ˣ) : ZMod M) = p := ZMod.coe_unitOfCoprime _ _
  calc (((unitP hpM)⁻¹ : (ZMod M)ˣ) : ZMod M)
      = (((unitP hpM)⁻¹ : (ZMod M)ˣ) : ZMod M) *
          ((x : ZMod M) * ((unitP hpM : (ZMod M)ˣ) : ZMod M)) := by rw [h2, h1, mul_one]
    _ = (x : ZMod M) := by rw [mul_left_comm, Units.inv_mul, mul_one]

lemma alphaP_det_pos : 0 < (alphaP p).det.val := by
  rw [alphaP, ← upperTri_U_eq, QExp.upperTri_det, one_mul]; exact_mod_cast prime_pos p

lemma alphaD_adj : ((alphaD p : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) =
    ((alphaP p : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ).adjugate := by
  rw [Matrix.adjugate_fin_two]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [alphaD, alphaP, toGL_apply, diagP, repU]

lemma Gamma_le_interConj_alphaP : Gamma (M * p) ≤ interConj (Gamma1 M) (alphaP p) := by
  intro δ hδ
  obtain ⟨h00, h01, h10, -⟩ := dvd_of_mem_Gamma hδ
  push_cast at h00 h01 h10
  have hdvd : ∀ a : ℤ, (M : ℤ) * p ∣ a → (M : ℤ) ∣ a := fun a h => (dvd_mul_right _ _).trans h
  obtain ⟨t, ht⟩ := h01
  have hd := Matrix.SpecialLinearGroup.det_coe δ
  rw [Matrix.det_fin_two, ht] at hd
  let δ' : SL(2, ℤ) := ⟨!![δ 0 0, (M : ℤ) * t; (p : ℤ) * δ 1 0, δ 1 1], by
    rw [Matrix.det_fin_two_of]; linear_combination hd⟩
  have hδ1 : δ ∈ Gamma1 M := mem_Gamma1_of δ (one_of_dvd (hdvd _ h00)) (zero_of_dvd (hdvd _ h10))
  refine mem_interConj_of hδ1 (δ := δ') (mem_Gamma1_of δ' ?_ ?_) ?_
  · simpa [δ'] using one_of_dvd (hdvd _ h00)
  · have : (M : ℤ) ∣ p * δ 1 0 := (hdvd _ h10).mul_left _
    simpa [δ'] using zero_of_dvd this
  · rw [alphaP, toGL_mul_mapGL, mapGL_mul_toGL]
    apply toGL_congr
    ext i j
    fin_cases i <;> fin_cases j <;> simp [δ', repU, Matrix.mul_apply, Fin.sum_univ_two] <;>
      first | ring1 | (rw [ht]; ring1)

lemma Gamma_le_interConj_alphaD : Gamma (M * p) ≤ interConj (Gamma1 M) (alphaD p) := by
  intro δ hδ
  obtain ⟨h00, h01, h10, -⟩ := dvd_of_mem_Gamma hδ
  push_cast at h00 h01 h10
  have hdvd : ∀ a : ℤ, (M : ℤ) * p ∣ a → (M : ℤ) ∣ a := fun a h => (dvd_mul_right _ _).trans h
  obtain ⟨s, hs⟩ := h10
  have hd := Matrix.SpecialLinearGroup.det_coe δ
  rw [Matrix.det_fin_two, hs] at hd
  let δ' : SL(2, ℤ) := ⟨!![δ 0 0, (p : ℤ) * δ 0 1; (M : ℤ) * s, δ 1 1], by
    rw [Matrix.det_fin_two_of]; linear_combination hd⟩
  have hδ1 : δ ∈ Gamma1 M := mem_Gamma1_of δ (one_of_dvd (hdvd _ h00))
    (zero_of_dvd (by rw [hs]; exact (dvd_mul_right _ _).mul_right _))
  refine mem_interConj_of hδ1 (δ := δ') (mem_Gamma1_of δ' ?_ ?_) ?_
  · simpa [δ'] using one_of_dvd (hdvd _ h00)
  · simpa [δ'] using zero_of_dvd (dvd_mul_right (M : ℤ) s)
  · rw [alphaD, toGL_mul_mapGL, mapGL_mul_toGL]
    apply toGL_congr
    ext i j
    fin_cases i <;> fin_cases j <;> simp [δ', diagP, Matrix.mul_apply, Fin.sum_univ_two] <;>
      first | ring1 | (rw [hs]; ring1)

lemma isArithmetic_conj_toGL [NeZero M] (A : Matrix (Fin 2) (Fin 2) ℤ) (hA : A.det ≠ 0) :
    (ConjAct.toConjAct (Hecke.toGL A hA)⁻¹ • G1 M).IsArithmetic := by
  have e : (Hecke.toGL A hA)⁻¹ = ((toGLQ A hA)⁻¹).map (Rat.castHom ℝ) := by
    rw [Hecke.toGL, map_inv]
  rw [e]
  exact Subgroup.IsArithmetic.conj (G1 M) (toGLQ A hA)⁻¹

variable [NeZero M]

lemma finiteIndex_interConj_alphaP : (interConj (Gamma1 M) (alphaP p)).FiniteIndex := by
  haveI : NeZero (M * p) := ⟨mul_ne_zero (NeZero.ne M) hp.out.ne_zero⟩
  exact Subgroup.finiteIndex_of_le Gamma_le_interConj_alphaP

lemma finiteIndex_interConj_alphaD : (interConj (Gamma1 M) (alphaD p)).FiniteIndex := by
  haveI : NeZero (M * p) := ⟨mul_ne_zero (NeZero.ne M) hp.out.ne_zero⟩
  exact Subgroup.finiteIndex_of_le Gamma_le_interConj_alphaD

/-- `T_p f = Σ_{q ∈ Γ₁/(Γ₁ ∩ α⁻¹Γ₁α)} f ∣ α q⁻¹` for `p ∤ M`. -/
theorem heckeFun_eq_sum_out (k : ℤ) (hpM : ¬ p ∣ M)
    [Fintype (CosetQ (Gamma1 M) (interConj (Gamma1 M) (alphaP p)))] (f : S1 M k) :
    heckeFun p k f = ∑ q : CosetQ (Gamma1 M) (interConj (Gamma1 M) (alphaP p)),
      ⇑f ∣[k] (alphaP p * (q.out : GL (Fin 2) ℝ)⁻¹) := by
  obtain ⟨x, y, hxy⟩ := exists_xy hpM
  rw [heckeFun_eq_sum_ndvd k hpM x y hxy]
  exact (sum_slash_out_eq (alphaP p) (rhoP M p x y hxy) (hexB x y hxy) (huniqB x y hxy)
    (hmemB x y hxy) k ⇑f (fun γ hγ => SlashInvariantFormClass.slash_action_eq f γ hγ)).symm

/-- `Σ_{q ∈ Γ₁/(Γ₁ ∩ α'⁻¹Γ₁α')} g ∣ α' q⁻¹ = T_p (⟨p⟩⁻¹ g)` for `p ∤ M`. -/
theorem sum_out_alphaD_eq (k : ℤ) (hpM : ¬ p ∣ M)
    [Fintype (CosetQ (Gamma1 M) (interConj (Gamma1 M) (alphaD p)))] (g : S1 M k) :
    ∑ q : CosetQ (Gamma1 M) (interConj (Gamma1 M) (alphaD p)),
      ⇑g ∣[k] (alphaD p * (q.out : GL (Fin 2) ℝ)⁻¹) =
      heckeFun p k (diamond k (unitP hpM)⁻¹ g) := by
  obtain ⟨x, y, hxy⟩ := exists_xy hpM
  have hcoe : ⇑(diamond k (unitP hpM)⁻¹ g) = ⇑g ∣[k] (mapGL ℝ (sigmaP M p x y hxy))⁻¹ := by
    rw [coe_diamond_of_mem k (Subgroup.inv_mem _ (sigmaP_mem x y hxy)) _
      (unitP_inv_eq x y hxy hpM) g, ← map_inv (mapGL ℝ) (sigmaP M p x y hxy)]
    rfl
  rw [heckeFun_eq_sum_ndvd k hpM x y hxy, hcoe]
  simp only [← SlashAction.slash_mul]
  exact sum_slash_out_eq (alphaD p) (fun r => (mapGL ℝ (sigmaP M p x y hxy))⁻¹ * rhoP M p x y hxy r)
    (hexC x y hxy) (huniqC x y hxy) (hmemC x y hxy) k ⇑g
    (fun γ hγ => SlashInvariantFormClass.slash_action_eq g γ hγ)

/-- **Adjoint of `T_p`** (`p ∤ M`): `⟪T_p f, g⟫ = ⟪f, T_p (⟨p⟩⁻¹ g)⟫` on `S_k(Γ₁(M))`. -/
theorem peterssonInner_heckeT (k : ℤ) (hpM : ¬ p ∣ M) (f g : S1 M k) :
    peterssonInner (Gamma1 M) k (heckeT p k f) g =
      peterssonInner (Gamma1 M) k f (heckeT p k (diamond k (unitP hpM)⁻¹ g)) := by
  haveI := finiteIndex_interConj_alphaP (M := M) (p := p)
  haveI := finiteIndex_interConj_alphaD (M := M) (p := p)
  haveI := isFiniteRelIndex_coe (Γ := Gamma1 M) (Γ' := interConj (Gamma1 M) (alphaP p))
  haveI := isFiniteRelIndex_coe (Γ := Gamma1 M) (Γ' := interConj (Gamma1 M) (alphaD p))
  let _ : Fintype (CosetQ (Gamma1 M) (interConj (Gamma1 M) (alphaP p))) := Fintype.ofFinite _
  let _ : Fintype (CosetQ (Gamma1 M) (interConj (Gamma1 M) (alphaD p))) := Fintype.ofFinite _
  haveI : (ConjAct.toConjAct (alphaP p)⁻¹ • G1 M).IsArithmetic := isArithmetic_conj_toGL _ _
  haveI : (ConjAct.toConjAct (alphaD p)⁻¹ • G1 M).IsArithmetic := isArithmetic_conj_toGL _ _
  have hf : ∀ γ ∈ (Gamma1 M : Subgroup (GL (Fin 2) ℝ)), ⇑f ∣[k] γ = ⇑f :=
    fun γ hγ => SlashInvariantFormClass.slash_action_eq f γ hγ
  have hg : ∀ γ ∈ (Gamma1 M : Subgroup (GL (Fin 2) ℝ)), ⇑g ∣[k] γ = ⇑g :=
    fun γ hγ => SlashInvariantFormClass.slash_action_eq g γ hγ
  have s1 : peterssonInner (Gamma1 M) k g (heckeT p k f) =
      peterssonInner (interConj (Gamma1 M) (alphaP p)) k g (⇑f ∣[k] alphaP p) := by
    have h := peterssonInner_sum_slash (interConj_le (Gamma1 M) (alphaP p))
      (neg_one_mem_interConj _) g (CuspForm.translate f (alphaP p))
      (fun γ hγ => slash_interConj_eq hf (alphaP p) hγ)
    rw [coe_heckeT, heckeFun_eq_sum_out k hpM f]
    simp only [SlashAction.slash_mul]
    exact h
  have s2 : peterssonInner (interConj (Gamma1 M) (alphaD p)) k f (⇑g ∣[k] alphaD p) =
      peterssonInner (Gamma1 M) k f (heckeT p k (diamond k (unitP hpM)⁻¹ g)) := by
    have h := peterssonInner_sum_slash (interConj_le (Gamma1 M) (alphaD p))
      (neg_one_mem_interConj _) f (CuspForm.translate g (alphaD p))
      (fun γ hγ => slash_interConj_eq hg (alphaD p) hγ)
    rw [coe_heckeT, ← sum_out_alphaD_eq k hpM g]
    simp only [SlashAction.slash_mul]
    exact h.symm
  calc peterssonInner (Gamma1 M) k (heckeT p k f) g
      = conj (peterssonInner (Gamma1 M) k g (heckeT p k f)) :=
        (peterssonInner_conj_symm _ _ _).symm
    _ = conj (peterssonInner (interConj (Gamma1 M) (alphaP p)) k g (⇑f ∣[k] alphaP p)) := by
        rw [s1]
    _ = peterssonInner (interConj (Gamma1 M) (alphaP p)) k (⇑f ∣[k] alphaP p) g :=
        peterssonInner_conj_symm _ _ _
    _ = peterssonInner (interConj (Gamma1 M) (alphaD p)) k f (⇑g ∣[k] alphaD p) :=
        peterssonInner_slash_adj (alphaP p) (alphaD p) alphaP_det_pos alphaD_adj
          (fun δ hδ => slash_Gamma1 k f hδ) (fun δ hδ => slash_Gamma1 k g hδ)
    _ = _ := s2

end TpPrime

section Consequences

open RamanujanPetersson RamanujanPetersson.Diamond RamanujanPetersson.Hecke CongruenceSubgroup

variable {M : ℕ} [NeZero M]

lemma diamond_inv_apply (k : ℤ) (d : (ZMod M)ˣ) (g : S1 M k) : diamond k d⁻¹ (diamond k d g) = g := by
  rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply]

/-- The diamond operators are unitary: `⟪⟨d⟩ f, ⟨d⟩ g⟫ = ⟪f, g⟫`. -/
theorem peterssonInner_diamond_diamond (k : ℤ) (d : (ZMod M)ˣ) (f g : S1 M k) :
    peterssonInner (Gamma1 M) k (diamond k d f) (diamond k d g) = peterssonInner (Gamma1 M) k f g := by
  rw [peterssonInner_diamond, diamond_inv_apply]

variable {p : ℕ} [Fact p.Prime]

/-- `(⟨p⟩⁻¹ T_p)^* = T_p`: `⟪⟨p⟩⁻¹ T_p f, g⟫ = ⟪f, T_p g⟫`. -/
theorem peterssonInner_heckeT_adj_left (k : ℤ) (hpM : ¬ p ∣ M) (f g : S1 M k) :
    peterssonInner (Gamma1 M) k (diamond k (unitP hpM)⁻¹ (heckeT p k f)) g =
      peterssonInner (Gamma1 M) k f (heckeT p k g) := by
  rw [peterssonInner_diamond, inv_inv, peterssonInner_heckeT k hpM, diamond_inv_apply]

/-- **`T_p^* = ⟨p⟩⁻¹ T_p`** (`p ∤ M`): `⟪T_p f, g⟫ = ⟪f, ⟨p⟩⁻¹ T_p g⟫`. -/
theorem peterssonInner_heckeT' (k : ℤ) (hpM : ¬ p ∣ M) (f g : S1 M k) :
    peterssonInner (Gamma1 M) k (heckeT p k f) g =
      peterssonInner (Gamma1 M) k f (diamond k (unitP hpM)⁻¹ (heckeT p k g)) := by
  rw [peterssonInner_heckeT k hpM, heckeT_diamond]

/-- On `S_k(M, χ)`: `⟪T_p f, g⟫ = χ(p)⁻¹ ⟪f, T_p g⟫` (`p ∤ M`). -/
theorem peterssonInner_heckeT_chi (k : ℤ) (hpM : ¬ p ∣ M) {χ : DirichletCharacter ℂ M}
    (f : S1 M k) {g : S1 M k} (hg : g ∈ chiSubspace k χ) :
    peterssonInner (Gamma1 M) k (heckeT p k f) g =
      (χ (p : ZMod M))⁻¹ * peterssonInner (Gamma1 M) k f (heckeT p k g) := by
  rw [peterssonInner_heckeT k hpM, (mem_chiSubspace_iff_diamond k χ g).1 hg, map_smul,
    peterssonInner_smul_right]
  congr 1
  have h1 : χ (((unitP hpM)⁻¹ : (ZMod M)ˣ) : ZMod M) * χ ((unitP hpM : (ZMod M)ˣ) : ZMod M) = 1 := by
    rw [← map_mul, Units.inv_mul, map_one]
  rw [ZMod.coe_unitOfCoprime] at h1
  exact eq_inv_of_mul_eq_one_left h1

/-- `T_p` is normal (`p ∤ M`): `⟪T_p f, T_p g⟫ = ⟪T_p^* f, T_p^* g⟫` with `T_p^* = ⟨p⟩⁻¹ T_p`. -/
theorem peterssonInner_heckeT_normal (k : ℤ) (hpM : ¬ p ∣ M) (f g : S1 M k) :
    peterssonInner (Gamma1 M) k (heckeT p k f) (heckeT p k g) =
      peterssonInner (Gamma1 M) k (diamond k (unitP hpM)⁻¹ (heckeT p k f))
        (diamond k (unitP hpM)⁻¹ (heckeT p k g)) := by
  rw [peterssonInner_heckeT_adj_left, peterssonInner_heckeT k hpM]

/-- `T_p` commutes with its adjoint `⟨p⟩⁻¹ T_p`. -/
theorem heckeT_commute_adjoint (k : ℤ) (hpM : ¬ p ∣ M) :
    Commute (heckeT p k) (diamond k (unitP hpM)⁻¹ * heckeT p k) :=
  by rw [Commute, SemiconjBy, ← mul_assoc, (heckeT_commute_diamond k (unitP hpM)⁻¹).eq]

variable (k : ℤ)

/-- The Petersson orthogonal complement `W^⊥` in `S_k(Γ₁(M))`. -/
def perp (W : Submodule ℂ (S1 M k)) : Submodule ℂ (S1 M k) where
  carrier := {g | ∀ f ∈ W, peterssonInner (Gamma1 M) k f g = 0}
  add_mem' {g g'} hg hg' f hf := by
    rw [peterssonInner_add_right, hg f hf, hg' f hf, add_zero]
  zero_mem' f _ := by
    have h := peterssonInner_smul_right (Γ := Gamma1 M) (0 : ℂ) f (0 : S1 M k)
    rwa [zero_smul, zero_mul] at h
  smul_mem' c g hg f hf := by
    rw [peterssonInner_smul_right, hg f hf, mul_zero]

variable {k}

lemma mem_perp {W : Submodule ℂ (S1 M k)} {g : S1 M k} :
    g ∈ perp k W ↔ ∀ f ∈ W, peterssonInner (Gamma1 M) k f g = 0 :=
  Iff.rfl

theorem heckeT_mem_perp (hpM : ¬ p ∣ M) {W : Submodule ℂ (S1 M k)}
    (hT : ∀ f ∈ W, heckeT p k f ∈ W) (hD : ∀ f ∈ W, diamond k (unitP hpM)⁻¹ f ∈ W)
    {g : S1 M k} (hg : g ∈ perp k W) : heckeT p k g ∈ perp k W := by
  rw [mem_perp] at hg ⊢
  intro f hf
  rw [← peterssonInner_heckeT_adj_left k hpM]
  exact hg _ (hD _ (hT f hf))

theorem diamond_mem_perp {W : Submodule ℂ (S1 M k)} (d : (ZMod M)ˣ)
    (hD : ∀ f ∈ W, diamond k d⁻¹ f ∈ W) {g : S1 M k} (hg : g ∈ perp k W) :
    diamond k d g ∈ perp k W := by
  rw [mem_perp] at hg ⊢
  intro f hf
  rw [peterssonInner_diamond_right]
  exact hg _ (hD f hf)

/-- **Stability of orthogonal complements**: if `W ≤ S_k(Γ₁(M))` is stable under every `T_q`
(`q ∤ M` prime) and every `⟨d⟩`, then so is `W^⊥`. -/
theorem perp_stable {W : Submodule ℂ (S1 M k)}
    (hT : ∀ (q : ℕ) [Fact q.Prime], ¬ q ∣ M → ∀ f ∈ W, heckeT q k f ∈ W)
    (hD : ∀ d : (ZMod M)ˣ, ∀ f ∈ W, diamond k d f ∈ W) :
    (∀ (q : ℕ) [Fact q.Prime], ¬ q ∣ M → ∀ g ∈ perp k W, heckeT q k g ∈ perp k W) ∧
      (∀ d : (ZMod M)ˣ, ∀ g ∈ perp k W, diamond k d g ∈ perp k W) :=
  ⟨fun q _ hqM _ hg => heckeT_mem_perp hqM (hT q hqM) (hD _) hg,
    fun d _ hg => diamond_mem_perp d (hD _) hg⟩

end Consequences

end RP.Adjoint


