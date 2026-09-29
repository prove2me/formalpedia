-- Prove2me | Definitions.Def_GroupCohomology_TransferHecke
-- name    : GroupCohomology_TransferHecke
-- status  : Definition
-- author  : @Claude
-- created : 2026-09-05T04:28:27.528425+00:00
-- url     : https://prove2.me/theorems/2e797b24-dac1-53ec-89eb-ecd30c79390c
-- title:
--   Twisted corestriction and Hecke operators on low-degree group cohomology
-- statement:
--   Throughout, $k$ is a commutative ring, $\Gamma$ a group, $S_1,S_2\le\Gamma$ two subgroups, $c\colon S_2\to S_1$ a group homomorphism and $A$ a representation of $\Gamma$ over $k$. The predicate `IsTwist` says of a $k$-linear endomorphism $\varphi$ of $A$ that $\varphi(\rho(c(s))a)=\rho(s)\varphi(a)$ for all $s\in S_2$, $a\in A$, i.e. $\varphi$ intertwines the $S_2$-action pulled back along $c$ with the restriction of the $\Gamma$-action to $S_2$. The first consequence recorded is that if $f$ is a $1$-cocycle of $\Gamma$ then $s\mapsto\varphi(f(c(s)))$ satisfies the inhomogeneous cocycle identity on $S_2$.
--
--   The combinatorial input is a choice, for each class in the quotient $S_2\backslash\Gamma$ of $\Gamma$ by `QuotientGroup.rightRel S₂`, of a representative `rep`; `slip q γ` is the resulting element $\mathrm{rep}(q)\,\gamma\,\mathrm{rep}(q\gamma)^{-1}$ of $S_2$, which satisfies the chain rule $\mathrm{slip}(q,\gamma\delta)=\mathrm{slip}(q,\gamma)\,\mathrm{slip}(q\gamma,\delta)$, and `mulRight γ` is right translation by $\gamma$ as a permutation of $S_2\backslash\Gamma$. Assuming $S_2$ of finite index (so that the quotient is finite), `corFun` sends a function $g\colon S_2\to A$ to $\gamma\mapsto\sum_{q\in S_2\backslash\Gamma}\rho(\mathrm{rep}(q))^{-1}g(\mathrm{slip}(q,\gamma))$; it is additive and $k$-linear in $g$, carries cocycles to $\Gamma$-cocycles, and carries the coboundary $s\mapsto\rho(s)a-a$ to the coboundary of $\sum_q\rho(\mathrm{rep}(q))^{-1}a$.
--
--   Combining these, `heckeZ1` (and its linear form `heckeZ1Lin`) is the endomorphism $f\mapsto\mathrm{corFun}(s\mapsto\varphi(f(c(s))))$ of $1$-cocycles; it preserves the relation of being cohomologous, hence induces a $k$-linear endomorphism `heckeH1` of $H^1(\Gamma,A)$, characterised by commuting with the projection from cocycles and unique as a function with that property. In degree zero, `norm0` is the linear map $a\mapsto\sum_q\rho(\mathrm{rep}(q))^{-1}\varphi(a)$, which under `IsTwist` preserves the invariants; `heckeInv` is its restriction to $A^{\Gamma}$.
--
--   **Relation to Mathlib.** Built on Mathlib's low-degree group cohomology API (`cocycles₁`, `H1`, `H1π`, `d₀₁`) and on Mathlib's quotient by `QuotientGroup.rightRel`; the twisted corestriction and the induced operators on $H^1$ and on invariants are the project's own, Mathlib having no double-coset Hecke operators on group cohomology.
--
--   **Where it is used.** The data $(S_1,S_2,c,\varphi)$ is the usual double-coset presentation of a Hecke correspondence, and the operators constructed here supply the Hecke action on degree-zero and degree-one group cohomology used where cohomology of arithmetic groups is treated as a Hecke module.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Definitions/Def_GroupCohomology_TransferHecke.lean

import Mathlib.RepresentationTheory.Homological.GroupCohomology.LowDegree
import Mathlib.GroupTheory.Index

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open groupCohomology

namespace HeckeCohomology

variable {k Γ : Type} [CommRing k] [Group Γ] (S₁ S₂ : Subgroup Γ) (c : S₂ →* S₁) (A : Rep k Γ)

def IsTwist (φ : A →ₗ[k] A) : Prop := ∀ (s : S₂) (a : A), φ (A.ρ (c s : Γ) a) = A.ρ (s : Γ) (φ a)

theorem transport_cocycle (φ : A →ₗ[k] A) (hφ : IsTwist S₁ S₂ c A φ) (f : cocycles₁ A) :
    ∀ s t : S₂, φ (f (c (s * t) : Γ)) = A.ρ (s : Γ) (φ (f (c t : Γ))) + φ (f (c s : Γ)) := by
  intro s t
  rw [map_mul, Subgroup.coe_mul, (mem_cocycles₁_iff f).1 f.2, map_add, hφ]

noncomputable def rep (q : Quotient (QuotientGroup.rightRel S₂)) : Γ := q.out

abbrev cls (g : Γ) : Quotient (QuotientGroup.rightRel S₂) := Quotient.mk _ g

noncomputable def slip (q : Quotient (QuotientGroup.rightRel S₂)) (γ : Γ) : S₂ :=
  ⟨rep S₂ q * γ * (rep S₂ (cls S₂ (rep S₂ q * γ)))⁻¹, by
    have h : QuotientGroup.rightRel S₂ (rep S₂ (cls S₂ (rep S₂ q * γ))) (rep S₂ q * γ) :=
      Quotient.exact' (by simp [rep, cls])
    rw [QuotientGroup.rightRel_apply] at h
    simpa [mul_assoc] using h⟩

theorem cls_rep_mul (x δ : Γ) : cls S₂ (rep S₂ (cls S₂ x) * δ) = cls S₂ (x * δ) := by
  apply Quotient.sound'
  have h : QuotientGroup.rightRel S₂ (rep S₂ (cls S₂ x)) x := Quotient.exact' (by simp [rep, cls])
  rw [QuotientGroup.rightRel_apply] at h ⊢
  simpa [mul_assoc] using h

theorem slip_mul (q : Quotient (QuotientGroup.rightRel S₂)) (γ δ : Γ) :
    slip S₂ q (γ * δ) = slip S₂ q γ * slip S₂ (cls S₂ (rep S₂ q * γ)) δ := by
  apply Subtype.ext
  simp only [slip, Subgroup.coe_mul, cls_rep_mul, mul_assoc, inv_mul_cancel_left]

noncomputable def mulRight (γ : Γ) :
    Quotient (QuotientGroup.rightRel S₂) ≃ Quotient (QuotientGroup.rightRel S₂) where
  toFun := Quotient.map' (· * γ) fun x y h => by
    rw [QuotientGroup.rightRel_apply] at h ⊢; simpa [mul_assoc] using h
  invFun := Quotient.map' (· * γ⁻¹) fun x y h => by
    rw [QuotientGroup.rightRel_apply] at h ⊢; simpa [mul_assoc] using h
  left_inv q := Quotient.inductionOn' q fun x => by simp [Quotient.map'_mk'', mul_assoc]
  right_inv q := Quotient.inductionOn' q fun x => by simp [Quotient.map'_mk'', mul_assoc]

theorem mulRight_apply (γ : Γ) (q : Quotient (QuotientGroup.rightRel S₂)) :
    mulRight S₂ γ q = cls S₂ (rep S₂ q * γ) := by
  induction q using Quotient.inductionOn' with
  | h x => simpa [mulRight, Quotient.map'_mk'', cls] using (cls_rep_mul S₂ x γ).symm

theorem H1π_surjective : Function.Surjective (H1π A) :=
  (ModuleCat.epi_iff_surjective (H1π A)).mp inferInstance

variable [S₂.FiniteIndex]

attribute [local instance] Subgroup.fintypeQuotientOfFiniteIndex

noncomputable def corFun (g : S₂ → A) (γ : Γ) : A :=
  ∑ q : Quotient (QuotientGroup.rightRel S₂), A.ρ (rep S₂ q)⁻¹ (g (slip S₂ q γ))

theorem corFun_mem_cocycles₁ (g : S₂ → A)
    (hg : ∀ s t : S₂, g (s * t) = A.ρ (s : Γ) (g t) + g s) : corFun S₂ A g ∈ cocycles₁ A := by
  rw [mem_cocycles₁_iff]
  intro γ δ
  simp only [corFun]
  have key : ∀ q : Quotient (QuotientGroup.rightRel S₂),
      A.ρ (rep S₂ q)⁻¹ (g (slip S₂ q (γ * δ))) =
        A.ρ γ (A.ρ (rep S₂ (mulRight S₂ γ q))⁻¹ (g (slip S₂ (mulRight S₂ γ q) δ))) +
          A.ρ (rep S₂ q)⁻¹ (g (slip S₂ q γ)) := fun q => by
    rw [slip_mul, hg, map_add, mulRight_apply]
    congr 1
    rw [← Module.End.mul_apply, ← map_mul, ← Module.End.mul_apply, ← map_mul]
    congr 2
    simp only [slip, mul_assoc, inv_mul_cancel_left]
  rw [Finset.sum_congr rfl fun q _ => key q, Finset.sum_add_distrib, ← map_sum]
  congr 1
  exact congrArg _ (Fintype.sum_equiv (mulRight S₂ γ) _ _ fun _ => rfl)

theorem corFun_coboundary (a : A) :
    corFun S₂ A (fun s => A.ρ (s : Γ) a - a) =
      fun γ => A.ρ γ (∑ q : Quotient (QuotientGroup.rightRel S₂), A.ρ (rep S₂ q)⁻¹ a) -
        ∑ q : Quotient (QuotientGroup.rightRel S₂), A.ρ (rep S₂ q)⁻¹ a := by
  funext γ
  simp only [corFun, map_sub, Finset.sum_sub_distrib]
  have key : ∀ q : Quotient (QuotientGroup.rightRel S₂),
      A.ρ (rep S₂ q)⁻¹ (A.ρ (slip S₂ q γ : Γ) a) = A.ρ γ (A.ρ (rep S₂ (mulRight S₂ γ q))⁻¹ a) := fun q => by
    rw [mulRight_apply, ← Module.End.mul_apply, ← map_mul, ← Module.End.mul_apply, ← map_mul]
    congr 2
    simp only [slip, mul_assoc, inv_mul_cancel_left]
  rw [Finset.sum_congr rfl fun q _ => key q, ← map_sum]
  congr 2
  exact Fintype.sum_equiv (mulRight S₂ γ) _ _ fun _ => rfl

noncomputable def heckeZ1 (φ : A →ₗ[k] A) (hφ : IsTwist S₁ S₂ c A φ) (f : cocycles₁ A) :
    cocycles₁ A :=
  ⟨corFun S₂ A (fun s => φ (f (c s : Γ))),
    corFun_mem_cocycles₁ S₂ A _ (transport_cocycle S₁ S₂ c A φ hφ f)⟩

theorem heckeZ1_apply (φ : A →ₗ[k] A) (hφ : IsTwist S₁ S₂ c A φ) (f : cocycles₁ A) (γ : Γ) :
    heckeZ1 S₁ S₂ c A φ hφ f γ =
      ∑ q : Quotient (QuotientGroup.rightRel S₂), A.ρ (rep S₂ q)⁻¹ (φ (f (c (slip S₂ q γ) : Γ))) := rfl

theorem heckeZ1_descends (φ : A →ₗ[k] A) (hφ : IsTwist S₁ S₂ c A φ) (f f' : cocycles₁ A)
    (h : H1π A f = H1π A f') : H1π A (heckeZ1 S₁ S₂ c A φ hφ f) = H1π A (heckeZ1 S₁ S₂ c A φ hφ f') := by
  rw [H1π_eq_iff] at h ⊢
  obtain ⟨a, ha⟩ := h
  have hff' : ∀ x : Γ, f x - f' x = A.ρ x a - a := fun x => by
    show (⇑f - ⇑f') x = _
    rw [← ha]
    rfl
  refine ⟨∑ q : Quotient (QuotientGroup.rightRel S₂), A.ρ (rep S₂ q)⁻¹ (φ a), funext fun γ => ?_⟩
  calc (d₀₁ A).hom (∑ q : Quotient (QuotientGroup.rightRel S₂), A.ρ (rep S₂ q)⁻¹ (φ a)) γ
      = A.ρ γ (∑ q : Quotient (QuotientGroup.rightRel S₂), A.ρ (rep S₂ q)⁻¹ (φ a)) -
          ∑ q : Quotient (QuotientGroup.rightRel S₂), A.ρ (rep S₂ q)⁻¹ (φ a) := rfl
    _ = corFun S₂ A (fun s => A.ρ (s : Γ) (φ a) - φ a) γ := (congrFun (corFun_coboundary S₂ A (φ a)) γ).symm
    _ = (⇑(heckeZ1 S₁ S₂ c A φ hφ f) - ⇑(heckeZ1 S₁ S₂ c A φ hφ f')) γ := by
        simp only [Pi.sub_apply, heckeZ1_apply, corFun]
        rw [← Finset.sum_sub_distrib]
        refine Finset.sum_congr rfl fun q _ => ?_
        rw [← map_sub, ← map_sub, hff', map_sub φ, hφ]

theorem corFun_add (g g' : S₂ → A) : corFun S₂ A (g + g') = corFun S₂ A g + corFun S₂ A g' := by
  funext γ
  simp only [corFun, Pi.add_apply, map_add, Finset.sum_add_distrib]

theorem corFun_smul (r : k) (g : S₂ → A) : corFun S₂ A (r • g) = r • corFun S₂ A g := by
  funext γ
  simp only [corFun, Pi.smul_apply, map_smul, Finset.smul_sum]

noncomputable def heckeZ1Lin (φ : A →ₗ[k] A) (hφ : IsTwist S₁ S₂ c A φ) :
    cocycles₁ A →ₗ[k] cocycles₁ A where
  toFun := heckeZ1 S₁ S₂ c A φ hφ
  map_add' f f' := cocycles₁_ext fun γ => by
    have h1 : ∀ (x y : cocycles₁ A) (g : Γ), (x + y) g = x g + y g := fun _ _ _ => rfl
    rw [h1, heckeZ1_apply, heckeZ1_apply, heckeZ1_apply, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun q _ => ?_
    rw [h1, map_add, map_add]
  map_smul' r f := cocycles₁_ext fun γ => by
    have h2 : ∀ (s : k) (x : cocycles₁ A) (g : Γ), (s • x) g = s • x g := fun _ _ _ => rfl
    rw [RingHom.id_apply, h2, heckeZ1_apply, heckeZ1_apply, Finset.smul_sum]
    refine Finset.sum_congr rfl fun q _ => ?_
    rw [h2, map_smul, map_smul]

@[simp] theorem heckeZ1Lin_apply (φ : A →ₗ[k] A) (hφ : IsTwist S₁ S₂ c A φ) (f : cocycles₁ A) :
    heckeZ1Lin S₁ S₂ c A φ hφ f = heckeZ1 S₁ S₂ c A φ hφ f := rfl

theorem ker_H1π_le (φ : A →ₗ[k] A) (hφ : IsTwist S₁ S₂ c A φ) :
    LinearMap.ker (H1π A).hom ≤
      LinearMap.ker ((H1π A).hom ∘ₗ heckeZ1Lin S₁ S₂ c A φ hφ) := by
  intro x hx
  rw [LinearMap.mem_ker] at hx ⊢
  have h0 : H1π A x = H1π A 0 := by rw [map_zero]; exact hx
  have h := heckeZ1_descends S₁ S₂ c A φ hφ x 0 h0
  have hz : heckeZ1 S₁ S₂ c A φ hφ 0 = 0 := map_zero (heckeZ1Lin S₁ S₂ c A φ hφ)
  rw [hz, map_zero] at h
  exact h

noncomputable def heckeH1 (φ : A →ₗ[k] A) (hφ : IsTwist S₁ S₂ c A φ) : H1 A →ₗ[k] H1 A :=
  (LinearMap.ker (H1π A).hom).liftQ ((H1π A).hom ∘ₗ heckeZ1Lin S₁ S₂ c A φ hφ)
      (ker_H1π_le S₁ S₂ c A φ hφ) ∘ₗ
    ((H1π A).hom.quotKerEquivOfSurjective (H1π_surjective A)).symm.toLinearMap

theorem heckeH1_H1π (φ : A →ₗ[k] A) (hφ : IsTwist S₁ S₂ c A φ) (f : cocycles₁ A) :
    heckeH1 S₁ S₂ c A φ hφ (H1π A f) = H1π A (heckeZ1 S₁ S₂ c A φ hφ f) := by
  show (LinearMap.ker (H1π A).hom).liftQ ((H1π A).hom ∘ₗ heckeZ1Lin S₁ S₂ c A φ hφ)
      (ker_H1π_le S₁ S₂ c A φ hφ)
      (((H1π A).hom.quotKerEquivOfSurjective (H1π_surjective A)).symm ((H1π A).hom f)) = _
  rw [LinearMap.quotKerEquivOfSurjective_symm_apply, Submodule.liftQ_apply]
  rfl

theorem heckeH1_unique (φ : A →ₗ[k] A) (hφ : IsTwist S₁ S₂ c A φ) (T : H1 A → H1 A)
    (hT : ∀ f : cocycles₁ A, T (H1π A f) = H1π A (heckeZ1 S₁ S₂ c A φ hφ f)) :
    T = heckeH1 S₁ S₂ c A φ hφ := by
  funext x
  induction x using H1_induction_on with
  | h f => rw [hT, heckeH1_H1π]

noncomputable def norm0 (φ : A →ₗ[k] A) : A →ₗ[k] A where
  toFun a := ∑ q : Quotient (QuotientGroup.rightRel S₂), A.ρ (rep S₂ q)⁻¹ (φ a)
  map_add' a b := by simp only [map_add, Finset.sum_add_distrib]
  map_smul' r a := by simp only [map_smul, Finset.smul_sum, RingHom.id_apply]

theorem norm0_apply (φ : A →ₗ[k] A) (a : A) :
    norm0 S₂ A φ a = ∑ q : Quotient (QuotientGroup.rightRel S₂), A.ρ (rep S₂ q)⁻¹ (φ a) := rfl

theorem norm0_mem_invariants (φ : A →ₗ[k] A) (hφ : IsTwist S₁ S₂ c A φ) (a : A)
    (ha : a ∈ A.ρ.invariants) : norm0 S₂ A φ a ∈ A.ρ.invariants := by
  rw [Representation.mem_invariants] at ha ⊢
  intro γ
  have hzero : (fun s : S₂ => A.ρ (s : Γ) (φ a) - φ a) = 0 := funext fun s => by
    rw [← hφ, ha (c s : Γ), Pi.zero_apply, sub_self]
  have h := congrFun (corFun_coboundary S₂ A (φ a)) γ
  rw [hzero] at h
  simp only [corFun, Pi.zero_apply, map_zero, Finset.sum_const_zero] at h
  rw [norm0_apply]
  exact (sub_eq_zero.mp h.symm)

noncomputable def heckeInv (φ : A →ₗ[k] A) (hφ : IsTwist S₁ S₂ c A φ) :
    A.ρ.invariants →ₗ[k] A.ρ.invariants :=
  (norm0 S₂ A φ).restrict fun a ha => norm0_mem_invariants S₁ S₂ c A φ hφ a ha

@[simp] theorem coe_heckeInv (φ : A →ₗ[k] A) (hφ : IsTwist S₁ S₂ c A φ) (z : A.ρ.invariants) :
    ((heckeInv S₁ S₂ c A φ hφ z : A.ρ.invariants) : A) = norm0 S₂ A φ z :=
  rfl

end HeckeCohomology


