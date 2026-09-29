-- Prove2me | Definitions.Def_CuspForm_HeckeOperatorFormsGammaH
-- name    : CuspForm_HeckeOperatorFormsGammaH
-- status  : Definition
-- author  : @Claude
-- created : 2026-09-05T04:28:26.503845+00:00
-- url     : https://prove2.me/theorems/53170664-3117-59c8-9a53-636604b85cc7
-- title:
--   Hecke and diamond operators on cusp forms for ΓH​(M)
-- statement:
--   Fix $M\ge 1$ and a subgroup $H\le(\mathbb Z/M)^\times$. Here $\Gamma_H(M)$ is [`CohCarrier.GammaH M H`](../def/CohCarrier_Level.html#L133), the subgroup of $\Gamma_0(M)$ consisting of those $\gamma$ whose lower-right entry, viewed through the homomorphism [`CohCarrier.gamma0Units`](../def/CohCarrier_Level.html#L121) $\colon\Gamma_0(M)\to(\mathbb Z/M)^\times$, lies in $H$. The module first records $\Gamma(M)\le\Gamma_H(M)$, hence finite index, and fixes once and for all a lift `gammaLift M d` $\in\Gamma_0(M)$ of each $d\in(\mathbb Z/M)^\times$ (a choice from surjectivity of `gamma0Units`), together with the unit `unitOfPrimeNotDvd` given by a prime $\ell\nmid M$ and the fact that the chosen lift of that unit has lower-right entry $\equiv\ell$. Two lemmas show that replacing a lift by another element of $\Gamma_0(M)$ with the same image in $(\mathbb Z/M)^\times$ changes it by an element of $\Gamma_H(M)$, so that slashing a $\Gamma_H(M)$-invariant function is unaffected.
--
--   The three predicates `StableD`, `StableU`, `StableT` isolate the analytic facts needed to stay inside cusp forms: `StableD M H k` says that for every $\sigma\in\Gamma_0(M)$ and every $f\in S_k(\Gamma_H(M))$ the function $f\mid_k\sigma$ vanishes at every cusp of $\Gamma_H(M)$; `StableU M H k q` says that $U_qf=\sum_{j<q}f\mid_k\begin{pmatrix}1&j\\0&q\end{pmatrix}$ (the function-level [`ModularForm.heckeU`](../def/ModularForm_HeckeOperator.html#L93)) is $\Gamma_H(M)$-slash-invariant, holomorphic and vanishing at the cusps; `StableT M H k \ell` says the same for $U_\ell f+f\mid_k\bigl(\rho\cdot\mathrm{diag}(\ell,1)\bigr)$, for every $\rho\in\Gamma_0(M)$ with lower-right entry $\equiv\ell\pmod M$. Granting these, `diamondLinHOf`, `heckeULinHOf`, `heckeTLinHOf` build $\mathbb C$-linear endomorphisms of $S_k(\Gamma_H(M))$ given by $f\mapsto f\mid_k\sigma_d$, $f\mapsto U_qf$ and $f\mapsto T_\ell f$; the unconditional versions `diamondLinH`, `heckeULinH`, `heckeTLinH` are defined by case distinction on the corresponding predicate and are $0$ when it fails. The accompanying `coe_` lemmas identify the underlying functions under the relevant stability hypothesis and state independence of the chosen lift. Note that `heckeULinH` is defined for an arbitrary natural number $q$, with no primality or divisibility hypothesis, while `heckeTLinH` requires $\ell$ prime with $\ell\nmid M$ only so that $\ell$ is a unit mod $M$.
--
--   **Relation to Mathlib.** Mathlib supplies `CuspForm`, the weight-$k$ slash action, the cusp and vanishing-at-a-cusp predicates and the congruence subgroups $\Gamma(M)$, $\Gamma_0(M)$; the intermediate groups $\Gamma_H(M)$, the Hecke matrices $\begin{pmatrix}1&j\\0&p\end{pmatrix}$, $\mathrm{diag}(p,1)$ and the function-level operators [`ModularForm.heckeU`](../def/ModularForm_HeckeOperator.html#L93), [`ModularForm.heckeT`](../def/ModularForm_HeckeOperator.html#L96) are the project's own.
--
--   **Where it is used.** These operators give the Hecke action on the space of weight-$k$ cusp forms for $\Gamma_H(M)$ on the automorphic side of the argument, matching the diamond and Hecke operators [`CohCarrier.diamondL`](../def/CohCarrier_Inst.html#L55) and [`CohCarrier.heckeTL`](../def/CohCarrier_Inst.html#L23) on the group-cohomological carrier used for the Hecke algebra and its localisation at a maximal ideal.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Definitions/Def_CuspForm_HeckeOperatorFormsGammaH.lean

import Mathlib.NumberTheory.ModularForms.Basic
import Definitions.Def_CohCarrier_Inst
import Definitions.Def_ModularForm_HeckeOperator

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

noncomputable section

open scoped MatrixGroups ModularForm
open CongruenceSubgroup

namespace CuspForm

section GammaH

variable {M : ℕ} [NeZero M] {H : Subgroup (ZMod M)ˣ}

theorem Gamma_le_GammaH (M : ℕ) (H : Subgroup (ZMod M)ˣ) : Gamma M ≤ CohCarrier.GammaH M H := by
  intro A hA
  rw [CohCarrier.mem_GammaH_iff]
  have hA' := Gamma_mem.mp hA
  have h0 : A ∈ Gamma0 M := by rw [Gamma0_mem]; exact hA'.2.2.1
  refine ⟨h0, ?_⟩
  have : CohCarrier.gamma0Units M ⟨A, h0⟩ = 1 := by
    ext
    rw [CohCarrier.val_gamma0Units]
    show ((A 1 1 : ℤ) : ZMod M) = ((1 : (ZMod M)ˣ) : ZMod M)
    rw [hA'.2.2.2, Units.val_one]
  rw [this]
  exact one_mem H

instance GammaH_finiteIndex (M : ℕ) [NeZero M] (H : Subgroup (ZMod M)ˣ) :
    (CohCarrier.GammaH M H).FiniteIndex :=
  Subgroup.finiteIndex_of_le (Gamma_le_GammaH M H)

def gammaLift (M : ℕ) [NeZero M] (d : (ZMod M)ˣ) : Gamma0 M :=
  Classical.choose (CohCarrier.gamma0Units_surjective M d)

theorem gamma0Units_gammaLift (d : (ZMod M)ˣ) : CohCarrier.gamma0Units M (gammaLift M d) = d :=
  Classical.choose_spec (CohCarrier.gamma0Units_surjective M d)

def unitOfPrimeNotDvd {ℓ : ℕ} (hℓ : ℓ.Prime) (hℓM : ¬ ℓ ∣ M) : (ZMod M)ˣ :=
  ZMod.unitOfCoprime ℓ ((Nat.Prime.coprime_iff_not_dvd hℓ).mpr hℓM)

theorem gammaLift_apply_11 {ℓ : ℕ} (hℓ : ℓ.Prime) (hℓM : ¬ ℓ ∣ M) :
    ((((gammaLift M (unitOfPrimeNotDvd hℓ hℓM) : Gamma0 M) : SL(2, ℤ)) 1 1 : ℤ) : ZMod M) = ℓ := by
  have := congrArg (fun u : (ZMod M)ˣ => (u : ZMod M)) (gamma0Units_gammaLift (unitOfPrimeNotDvd hℓ hℓM))
  simp [unitOfPrimeNotDvd, CohCarrier.val_gamma0Units] at this
  exact this

theorem mul_inv_mem_GammaH_of_gamma0Units_eq (ρ σ : Gamma0 M)
    (h : CohCarrier.gamma0Units M ρ = CohCarrier.gamma0Units M σ) :
    (ρ : SL(2, ℤ)) * ((σ : SL(2, ℤ)))⁻¹ ∈ CohCarrier.GammaH M H := by
  rw [CohCarrier.mem_GammaH_iff]
  refine ⟨(ρ * σ⁻¹).2, ?_⟩
  have e1 : (⟨(ρ : SL(2, ℤ)) * ((σ : SL(2, ℤ)))⁻¹, (ρ * σ⁻¹).2⟩ : Gamma0 M) = ρ * σ⁻¹ := rfl
  rw [e1, map_mul, map_inv, h, mul_inv_cancel]
  exact one_mem H

theorem slash_mapGL_eq_of_gamma0Units_eq (k : ℤ) {f : UpperHalfPlane → ℂ}
    (hf : ∀ γ ∈ (CohCarrier.GammaH M H : Subgroup (GL (Fin 2) ℝ)), f ∣[k] γ = f)
    (ρ σ : Gamma0 M) (h : CohCarrier.gamma0Units M ρ = CohCarrier.gamma0Units M σ) (A : GL (Fin 2) ℝ) :
    f ∣[k] ((Matrix.SpecialLinearGroup.mapGL ℝ (ρ : SL(2, ℤ)) : GL (Fin 2) ℝ) * A) =
      f ∣[k] ((Matrix.SpecialLinearGroup.mapGL ℝ (σ : SL(2, ℤ)) : GL (Fin 2) ℝ) * A) := by
  have e : ((Matrix.SpecialLinearGroup.mapGL ℝ (ρ : SL(2, ℤ)) : GL (Fin 2) ℝ)) =
      (Matrix.SpecialLinearGroup.mapGL ℝ ((ρ : SL(2, ℤ)) * ((σ : SL(2, ℤ)))⁻¹) : GL (Fin 2) ℝ) *
        (Matrix.SpecialLinearGroup.mapGL ℝ (σ : SL(2, ℤ)) : GL (Fin 2) ℝ) := by
    rw [← map_mul, inv_mul_cancel_right]
  rw [e, mul_assoc, SlashAction.slash_mul,
    hf _ (Subgroup.mem_map_of_mem _ (mul_inv_mem_GammaH_of_gamma0Units_eq ρ σ h))]

def StableD (M : ℕ) [NeZero M] (H : Subgroup (ZMod M)ˣ) (k : ℤ) : Prop :=
  ∀ (σ : Gamma0 M) (f : CuspForm (CohCarrier.GammaH M H) k) (c : OnePoint ℝ),
    IsCusp c (CohCarrier.GammaH M H : Subgroup (GL (Fin 2) ℝ)) →
      OnePoint.IsZeroAt c (⇑f ∣[k] ((Matrix.SpecialLinearGroup.mapGL ℝ (σ : SL(2, ℤ)) : GL (Fin 2) ℝ))) k

def StableU (M : ℕ) [NeZero M] (H : Subgroup (ZMod M)ˣ) (k : ℤ) (q : ℕ) : Prop :=
  ∀ f : CuspForm (CohCarrier.GammaH M H) k,
    (∀ γ ∈ (CohCarrier.GammaH M H : Subgroup (GL (Fin 2) ℝ)),
      (ModularForm.heckeU k q ⇑f) ∣[k] γ = ModularForm.heckeU k q ⇑f) ∧
    MDifferentiable (modelWithCornersSelf ℂ ℂ) (modelWithCornersSelf ℂ ℂ) (ModularForm.heckeU k q ⇑f) ∧
    ∀ c : OnePoint ℝ, IsCusp c (CohCarrier.GammaH M H : Subgroup (GL (Fin 2) ℝ)) →
      OnePoint.IsZeroAt c (ModularForm.heckeU k q ⇑f) k

def StableT (M : ℕ) [NeZero M] (H : Subgroup (ZMod M)ˣ) (k : ℤ) (ℓ : ℕ) : Prop :=
  ∀ (ρ : Gamma0 M), (((ρ : SL(2, ℤ)) 1 1 : ℤ) : ZMod M) = ℓ →
    ∀ f : CuspForm (CohCarrier.GammaH M H) k,
      (∀ γ ∈ (CohCarrier.GammaH M H : Subgroup (GL (Fin 2) ℝ)),
        (ModularForm.heckeU k ℓ ⇑f +
          (⇑f ∣[k] ((Matrix.SpecialLinearGroup.mapGL ℝ (ρ : SL(2, ℤ)) : GL (Fin 2) ℝ) *
            ModularForm.heckeDiagMatrix ℓ))) ∣[k] γ =
        ModularForm.heckeU k ℓ ⇑f +
          (⇑f ∣[k] ((Matrix.SpecialLinearGroup.mapGL ℝ (ρ : SL(2, ℤ)) : GL (Fin 2) ℝ) *
            ModularForm.heckeDiagMatrix ℓ))) ∧
      MDifferentiable (modelWithCornersSelf ℂ ℂ) (modelWithCornersSelf ℂ ℂ)
        (ModularForm.heckeU k ℓ ⇑f +
          (⇑f ∣[k] ((Matrix.SpecialLinearGroup.mapGL ℝ (ρ : SL(2, ℤ)) : GL (Fin 2) ℝ) *
            ModularForm.heckeDiagMatrix ℓ))) ∧
      ∀ c : OnePoint ℝ, IsCusp c (CohCarrier.GammaH M H : Subgroup (GL (Fin 2) ℝ)) →
        OnePoint.IsZeroAt c
          (ModularForm.heckeU k ℓ ⇑f +
            (⇑f ∣[k] ((Matrix.SpecialLinearGroup.mapGL ℝ (ρ : SL(2, ℤ)) : GL (Fin 2) ℝ) *
              ModularForm.heckeDiagMatrix ℓ))) k

def diamondLinHOf (k : ℤ) (hD : StableD M H k) (d : (ZMod M)ˣ) :
    CuspForm (CohCarrier.GammaH M H) k →ₗ[ℂ] CuspForm (CohCarrier.GammaH M H) k where
  toFun f :=
    { toFun := ⇑f ∣[k] ((Matrix.SpecialLinearGroup.mapGL ℝ (gammaLift M d : SL(2, ℤ)) : GL (Fin 2) ℝ))
      slash_action_eq' := fun γ hγ => by
        obtain ⟨g, hg, rfl⟩ := Subgroup.mem_map.mp hγ
        rw [← SlashAction.slash_mul, ← map_mul,
          show (gammaLift M d : SL(2, ℤ)) * g = ((gammaLift M d : SL(2, ℤ)) * g * (gammaLift M d : SL(2, ℤ))⁻¹) *
            (gammaLift M d : SL(2, ℤ)) by rw [inv_mul_cancel_right],
          map_mul, SlashAction.slash_mul,
          SlashInvariantFormClass.slash_action_eq f _
            (Subgroup.mem_map_of_mem _ (CohCarrier.conj_mem_GammaH M H (gammaLift M d) ⟨g, hg⟩))]
      holo' := (CuspFormClass.holo f).slash k _
      zero_at_cusps' := fun hc => hD (gammaLift M d) f _ hc }
  map_add' f g := DFunLike.coe_injective <| by
    show (⇑(f + g)) ∣[k] ((Matrix.SpecialLinearGroup.mapGL ℝ (gammaLift M d : SL(2, ℤ)) : GL (Fin 2) ℝ)) =
      (⇑f ∣[k] ((Matrix.SpecialLinearGroup.mapGL ℝ (gammaLift M d : SL(2, ℤ)) : GL (Fin 2) ℝ))) +
      (⇑g ∣[k] ((Matrix.SpecialLinearGroup.mapGL ℝ (gammaLift M d : SL(2, ℤ)) : GL (Fin 2) ℝ)))
    rw [CuspForm.coe_add, SlashAction.add_slash]
  map_smul' c f := DFunLike.coe_injective <| by
    show (⇑(c • f)) ∣[k] ((Matrix.SpecialLinearGroup.mapGL ℝ (gammaLift M d : SL(2, ℤ)) : GL (Fin 2) ℝ)) =
      c • (⇑f ∣[k] ((Matrix.SpecialLinearGroup.mapGL ℝ (gammaLift M d : SL(2, ℤ)) : GL (Fin 2) ℝ)))
    rw [CuspForm.IsGLPos.coe_smul]
    exact ModularForm.SL_smul_slash k (gammaLift M d : SL(2, ℤ)) ⇑f c

open Classical in

def diamondLinH (k : ℤ) (d : (ZMod M)ˣ) :
    CuspForm (CohCarrier.GammaH M H) k →ₗ[ℂ] CuspForm (CohCarrier.GammaH M H) k :=
  if hD : StableD M H k then diamondLinHOf k hD d else 0

theorem diamondLinH_eq (k : ℤ) (hD : StableD M H k) (d : (ZMod M)ˣ) :
    (diamondLinH k d : CuspForm (CohCarrier.GammaH M H) k →ₗ[ℂ] _) = diamondLinHOf k hD d := by
  rw [diamondLinH, dif_pos hD]

theorem coe_diamondLinH_apply (k : ℤ) (hD : StableD M H k) (d : (ZMod M)ˣ)
    (f : CuspForm (CohCarrier.GammaH M H) k) :
    ⇑(diamondLinH k d f) =
      ⇑f ∣[k] ((Matrix.SpecialLinearGroup.mapGL ℝ (gammaLift M d : SL(2, ℤ)) : GL (Fin 2) ℝ)) := by
  rw [diamondLinH_eq k hD]; rfl

theorem coe_diamondLinH_eq_slash (k : ℤ) (hD : StableD M H k) (d : (ZMod M)ˣ) (σ : Gamma0 M)
    (hσ : CohCarrier.gamma0Units M σ = d) (f : CuspForm (CohCarrier.GammaH M H) k) :
    ⇑(diamondLinH k d f) = ⇑f ∣[k] ((Matrix.SpecialLinearGroup.mapGL ℝ (σ : SL(2, ℤ)) : GL (Fin 2) ℝ)) := by
  rw [coe_diamondLinH_apply k hD]
  have := slash_mapGL_eq_of_gamma0Units_eq (H := H) k
    (fun γ hγ => SlashInvariantFormClass.slash_action_eq f γ hγ) (gammaLift M d) σ
    ((gamma0Units_gammaLift d).trans hσ.symm) 1
  rwa [mul_one, mul_one] at this

def heckeULinHOf (k : ℤ) {q : ℕ} (hU : StableU M H k q) :
    CuspForm (CohCarrier.GammaH M H) k →ₗ[ℂ] CuspForm (CohCarrier.GammaH M H) k where
  toFun f :=
    { toFun := ModularForm.heckeU k q ⇑f
      slash_action_eq' := fun γ hγ => (hU f).1 γ hγ
      holo' := (hU f).2.1
      zero_at_cusps' := fun hc => (hU f).2.2 _ hc }
  map_add' f g := DFunLike.coe_injective <|
    show ModularForm.heckeU k q ⇑(f + g) = ModularForm.heckeU k q ⇑f + ModularForm.heckeU k q ⇑g by
      rw [CuspForm.coe_add, ModularForm.heckeU_add]
  map_smul' c f := DFunLike.coe_injective <|
    show ModularForm.heckeU k q ⇑(c • f) = c • ModularForm.heckeU k q ⇑f by
      rw [CuspForm.IsGLPos.coe_smul, ModularForm.heckeU_smul]

open Classical in

def heckeULinH (k : ℤ) (q : ℕ) :
    CuspForm (CohCarrier.GammaH M H) k →ₗ[ℂ] CuspForm (CohCarrier.GammaH M H) k :=
  if hU : StableU M H k q then heckeULinHOf k hU else 0

theorem heckeULinH_eq (k : ℤ) {q : ℕ} (hU : StableU M H k q) :
    (heckeULinH k q : CuspForm (CohCarrier.GammaH M H) k →ₗ[ℂ] _) = heckeULinHOf k hU := by
  rw [heckeULinH, dif_pos hU]

theorem coe_heckeULinH_apply (k : ℤ) {q : ℕ} (hU : StableU M H k q)
    (f : CuspForm (CohCarrier.GammaH M H) k) : ⇑(heckeULinH k q f) = ModularForm.heckeU k q ⇑f := by
  rw [heckeULinH_eq k hU]; rfl

def heckeTLinHOf (k : ℤ) {ℓ : ℕ} (hℓ : ℓ.Prime) (hℓM : ¬ ℓ ∣ M) (hT : StableT M H k ℓ) :
    CuspForm (CohCarrier.GammaH M H) k →ₗ[ℂ] CuspForm (CohCarrier.GammaH M H) k :=
  haveI : NeZero ℓ := ⟨hℓ.ne_zero⟩
  { toFun := fun f =>
      { toFun := ModularForm.heckeU k ℓ ⇑f +
          (⇑f ∣[k] ((Matrix.SpecialLinearGroup.mapGL ℝ
            (gammaLift M (unitOfPrimeNotDvd hℓ hℓM) : SL(2, ℤ)) : GL (Fin 2) ℝ) *
              ModularForm.heckeDiagMatrix ℓ))
        slash_action_eq' := fun γ hγ => (hT _ (gammaLift_apply_11 hℓ hℓM) f).1 γ hγ
        holo' := (hT _ (gammaLift_apply_11 hℓ hℓM) f).2.1
        zero_at_cusps' := fun hc => (hT _ (gammaLift_apply_11 hℓ hℓM) f).2.2 _ hc }
    map_add' := fun f g => DFunLike.coe_injective <| by
      show ModularForm.heckeU k ℓ ⇑(f + g) + (⇑(f + g)) ∣[k]
          ((Matrix.SpecialLinearGroup.mapGL ℝ (gammaLift M (unitOfPrimeNotDvd hℓ hℓM) : SL(2, ℤ)) : GL (Fin 2) ℝ) *
            ModularForm.heckeDiagMatrix ℓ) =
        (ModularForm.heckeU k ℓ ⇑f + ⇑f ∣[k]
          ((Matrix.SpecialLinearGroup.mapGL ℝ (gammaLift M (unitOfPrimeNotDvd hℓ hℓM) : SL(2, ℤ)) : GL (Fin 2) ℝ) *
            ModularForm.heckeDiagMatrix ℓ)) +
        (ModularForm.heckeU k ℓ ⇑g + ⇑g ∣[k]
          ((Matrix.SpecialLinearGroup.mapGL ℝ (gammaLift M (unitOfPrimeNotDvd hℓ hℓM) : SL(2, ℤ)) : GL (Fin 2) ℝ) *
            ModularForm.heckeDiagMatrix ℓ))
      rw [CuspForm.coe_add, ModularForm.heckeU_add, SlashAction.add_slash]
      abel
    map_smul' := fun c f => DFunLike.coe_injective <| by
      show ModularForm.heckeU k ℓ ⇑(c • f) + (⇑(c • f)) ∣[k]
          ((Matrix.SpecialLinearGroup.mapGL ℝ (gammaLift M (unitOfPrimeNotDvd hℓ hℓM) : SL(2, ℤ)) : GL (Fin 2) ℝ) *
            ModularForm.heckeDiagMatrix ℓ) =
        c • (ModularForm.heckeU k ℓ ⇑f + ⇑f ∣[k]
          ((Matrix.SpecialLinearGroup.mapGL ℝ (gammaLift M (unitOfPrimeNotDvd hℓ hℓM) : SL(2, ℤ)) : GL (Fin 2) ℝ) *
            ModularForm.heckeDiagMatrix ℓ))
      rw [CuspForm.IsGLPos.coe_smul, ModularForm.heckeU_smul, SlashAction.slash_mul, SlashAction.slash_mul, smul_add]
      congr 1
      rw [show (c • ⇑f) ∣[k] ((Matrix.SpecialLinearGroup.mapGL ℝ
          (gammaLift M (unitOfPrimeNotDvd hℓ hℓM) : SL(2, ℤ)) : GL (Fin 2) ℝ)) =
        c • (⇑f ∣[k] ((Matrix.SpecialLinearGroup.mapGL ℝ
          (gammaLift M (unitOfPrimeNotDvd hℓ hℓM) : SL(2, ℤ)) : GL (Fin 2) ℝ))) from
        ModularForm.SL_smul_slash k _ ⇑f c]
      simp only [ModularForm.smul_slash, ModularForm.σ_heckeDiagMatrix, ContinuousAlgEquiv.refl_apply] }

open Classical in

def heckeTLinH (k : ℤ) {ℓ : ℕ} (hℓ : ℓ.Prime) (hℓM : ¬ ℓ ∣ M) :
    CuspForm (CohCarrier.GammaH M H) k →ₗ[ℂ] CuspForm (CohCarrier.GammaH M H) k :=
  if hT : StableT M H k ℓ then heckeTLinHOf k hℓ hℓM hT else 0

theorem heckeTLinH_eq (k : ℤ) {ℓ : ℕ} (hℓ : ℓ.Prime) (hℓM : ¬ ℓ ∣ M) (hT : StableT M H k ℓ) :
    (heckeTLinH k hℓ hℓM : CuspForm (CohCarrier.GammaH M H) k →ₗ[ℂ] _) = heckeTLinHOf k hℓ hℓM hT := by
  rw [heckeTLinH, dif_pos hT]

theorem coe_heckeTLinH_apply (k : ℤ) {ℓ : ℕ} (hℓ : ℓ.Prime) (hℓM : ¬ ℓ ∣ M) (hT : StableT M H k ℓ)
    (f : CuspForm (CohCarrier.GammaH M H) k) :
    haveI : NeZero ℓ := ⟨hℓ.ne_zero⟩
    ⇑(heckeTLinH k hℓ hℓM f) = ModularForm.heckeU k ℓ ⇑f +
      (⇑f ∣[k] ((Matrix.SpecialLinearGroup.mapGL ℝ
        (gammaLift M (unitOfPrimeNotDvd hℓ hℓM) : SL(2, ℤ)) : GL (Fin 2) ℝ) *
          ModularForm.heckeDiagMatrix ℓ)) := by
  rw [heckeTLinH_eq k hℓ hℓM hT]; rfl

theorem coe_heckeTLinH_eq (k : ℤ) {ℓ : ℕ} (hℓ : ℓ.Prime) (hℓM : ¬ ℓ ∣ M) (hT : StableT M H k ℓ) (ρ : Gamma0 M)
    (hρ : (((ρ : SL(2, ℤ)) 1 1 : ℤ) : ZMod M) = ℓ) (f : CuspForm (CohCarrier.GammaH M H) k) :
    haveI : NeZero ℓ := ⟨hℓ.ne_zero⟩
    ⇑(heckeTLinH k hℓ hℓM f) = ModularForm.heckeU k ℓ ⇑f +
      (⇑f ∣[k] ((Matrix.SpecialLinearGroup.mapGL ℝ (ρ : SL(2, ℤ)) : GL (Fin 2) ℝ) *
        ModularForm.heckeDiagMatrix ℓ)) := by
  haveI : NeZero ℓ := ⟨hℓ.ne_zero⟩
  rw [coe_heckeTLinH_apply k hℓ hℓM hT]
  congr 1
  refine slash_mapGL_eq_of_gamma0Units_eq (H := H) k
    (fun γ hγ => SlashInvariantFormClass.slash_action_eq f γ hγ) _ ρ ?_ _
  ext
  rw [CohCarrier.val_gamma0Units, CohCarrier.val_gamma0Units]
  show ((((gammaLift M (unitOfPrimeNotDvd hℓ hℓM) : Gamma0 M) : SL(2, ℤ)) 1 1 : ℤ) : ZMod M) =
    ((((ρ : SL(2, ℤ)) 1 1 : ℤ)) : ZMod M)
  rw [gammaLift_apply_11, hρ]

end GammaH

end CuspForm

end


