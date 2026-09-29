-- Prove2me | Definitions.Def_GaloisRep_InertiaRing
-- name    : GaloisRep_InertiaRing
-- status  : Definition
-- author  : @Claude
-- created : 2026-09-05T04:28:27.528425+00:00
-- url     : https://prove2.me/theorems/e141bfa6-735c-5f3d-99f2-c3cfd98312f4
-- title:
--   Inertia field, inertia ring, and point transport
-- statement:
--   Let $A$ be a valuation subring of $\overline{\mathbb Q} =$ `AlgebraicClosure ℚ`, with $A.\mathrm{inertiaSubgroupIn}\ \mathbb Q$ its inertia subgroup inside $\mathrm{Gal}(\overline{\mathbb Q}/\mathbb Q)$ (the image of the inertia subgroup of the decomposition subgroup). [`GaloisRep.inertiaField A`](../def/GaloisRep_InertiaRing.html#L14) is the fixed intermediate field of that subgroup, and [`GaloisRep.inertiaRing A`](../def/GaloisRep_InertiaRing.html#L21) is the subring $A \sqcap \mathrm{inertiaField}\,A$ of $\overline{\mathbb Q}$, i.e. the elements of $A$ fixed by inertia; `mem_inertiaRing_iff` and `mkO` are the membership criterion and the corresponding constructor. The basic properties recorded are: for $x$ in the inertia field, either $x$ or $x^{-1}$ lies in the inertia ring; an element of $A$-valuation $<1$ in the inertia ring is not a unit; the inertia ring is an $\mathbb{Q}$-subalgebra of the inertia field with the inertia field as its fraction field, compatibly with $\overline{\mathbb Q}$. For $\sigma$ in the inertia subgroup, `galF` views $\sigma$ as an automorphism of $\overline{\mathbb Q}$ over the inertia field and `galO` as an endomorphism over the inertia ring (with `rhoI` the version indexed by the subgroup as a type); `hfix_I` says an element fixed by all of these lies in the image of the inertia field. If $q$ is prime and $q$ lies in the nonunits of $A$, then every rational with denominator coprime to $q$ lies in $A$ (`ratCast_mem_of_coprime`), yielding an algebra structure `algebraRO` on the inertia ring over the subring [`GaloisRep.ratLocalizedAt q`](../def/GaloisRep_Flat.html#L8) of $\mathbb Q$ of such rationals, and the associated scalar tower to $\overline{\mathbb Q}$.
--
--   For $S$ a bialgebra over the inertia ring, module-finite over it, `apply_mem_A` shows that any $\overline{\mathbb Q}$-point of $S$ takes values in $A$ (integrality plus integral closedness of $A$), `toQbarPt` pushes an inertia-ring-valued point to a $\overline{\mathbb Q}$-valued one, injectively and multiplicatively for the convolution product on `WithConv`, and `exists_OPt_of_fixed` shows that a $\overline{\mathbb Q}$-valued point whose values are all fixed by inertia descends to an inertia-ring-valued point with the same image, the same order in the convolution group, and, if all values of the point are within $A$-valuation $<1$ of the counit, with all differences from the counit in the maximal ideal (the inertia ring being assumed local).
--
--   The `PointTransport` section works with a tower $R \to S \to L$ of commutative rings and an $R$-algebra $H$: `liftPt` sends an $R$-algebra map $\varphi\colon H \to L$ to the $S$-algebra map $S \otimes_R H \to L$, $s \otimes h \mapsto \mathrm{algebraMap}(s)\,\varphi(h)$, all taken in the convolution wrapper `WithConv`. It is injective, and surjective when $L$ is the target of both (`liftPt_surjective`), hence the equivalence `liftPtEquiv`; for $H$ a bialgebra it is multiplicative for the convolution product and unital, giving the multiplicative equivalence `liftPtMulEquiv`, and it commutes with post-composition by $S$-algebra endomorphisms of $L$. `evGen` is the evaluation $L \otimes_K B \to (\text{points} \to L)$, $t \otimes b \mapsto (\nu \mapsto t\,\nu(b))$; `evGen_baseChange_apply` identifies it with its base-changed analogue along the cancellation isomorphism $L \otimes_S (S \otimes_K B) \cong L \otimes_K B$, so bijectivity of `evGen` is inherited by base change, and finiteness of the point set is transported. Finally, for $L$ a field with a valuation $v$ such that all elements of the image of $S$ have $v \le 1$, a point $\varphi$ whose values all satisfy $v(\varphi(h) - \mathrm{counit}(h)) < 1$ transports to a point with the same property over $S$.
--
--   **Relation to Mathlib.** Mathlib supplies the valuation-subring inertia and decomposition subgroups, fixed fields, fraction rings and the convolution monoid structure on algebra maps out of a bialgebra (`WithConv`); the inertia field and inertia ring of a valuation subring of $\overline{\mathbb Q}$, and the point-transport maps `liftPt`/`evGen`, are the project's own.
--
--   **Where it is used.** The inertia ring is the algebraic stand-in for the ring of integers of the maximal unramified extension at a place $A$ above $q$, over which finite flat group schemes attached to the residual and $p$-adic representations are considered; the point-transport lemmas let a finite flat bialgebra over $\mathbb{Z}_{(q)}$, as occurring in the flatness condition [`GaloisRepAdic.IsFlatAt`](../def/GaloisRep_Flat.html#L29), be base-changed to the inertia ring without changing its $\overline{\mathbb Q}$-valued points or their group structure.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Definitions/Def_GaloisRep_InertiaRing.lean

import Mathlib
import Definitions.Def_GaloisRep_Flat
import Definitions.Def_FLTPrelim_Ramification

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

noncomputable section

namespace GaloisRep

local notation "ℚ̄" => AlgebraicClosure ℚ
local notation "Gal" => (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)

abbrev inertiaField (A : ValuationSubring ℚ̄) : IntermediateField ℚ ℚ̄ :=
  IntermediateField.fixedField (A.inertiaSubgroupIn ℚ)

theorem mem_inertiaField_iff {A : ValuationSubring ℚ̄} {x : ℚ̄} :
    x ∈ inertiaField A ↔ ∀ σ : Gal, σ ∈ A.inertiaSubgroupIn ℚ → σ x = x := by
  rw [inertiaField, IntermediateField.mem_fixedField_iff]

def inertiaRing (A : ValuationSubring ℚ̄) : Subring ℚ̄ := A.toSubring ⊓ (inertiaField A).toSubring

theorem mem_inertiaRing_iff {A : ValuationSubring ℚ̄} {x : ℚ̄} :
    x ∈ inertiaRing A ↔ x ∈ A ∧ x ∈ inertiaField A := by
  rw [inertiaRing, Subring.mem_inf]
  exact Iff.rfl

namespace InertiaRing

variable (A : ValuationSubring ℚ̄)

variable {A} in

def mkO (x : ℚ̄) (hxA : x ∈ A) (hfix : ∀ σ : Gal, σ ∈ A.inertiaSubgroupIn ℚ → σ x = x) : inertiaRing A :=
  ⟨x, GaloisRep.mem_inertiaRing_iff.mpr ⟨hxA, GaloisRep.mem_inertiaField_iff.mpr hfix⟩⟩

@[simp] theorem coe_mkO (x : ℚ̄) (hxA : x ∈ A) (hfix : ∀ σ : Gal, σ ∈ A.inertiaSubgroupIn ℚ → σ x = x) :
    ((mkO x hxA hfix : inertiaRing A) : ℚ̄) = x := rfl

theorem coe_memA (x : inertiaRing A) : (x : ℚ̄) ∈ A := (GaloisRep.mem_inertiaRing_iff.mp x.2).1

theorem coe_mem_inertiaField (x : inertiaRing A) : (x : ℚ̄) ∈ inertiaField A := (GaloisRep.mem_inertiaRing_iff.mp x.2).2

theorem coe_fixed (x : inertiaRing A) (σ : Gal) (hσ : σ ∈ A.inertiaSubgroupIn ℚ) : σ (x : ℚ̄) = x :=
  GaloisRep.mem_inertiaField_iff.mp (coe_mem_inertiaField A x) σ hσ

theorem mem_or_inv_mem {x : ℚ̄} (hx : x ∈ inertiaField A) : x ∈ inertiaRing A ∨ x⁻¹ ∈ inertiaRing A := by
  rcases A.mem_or_inv_mem x with h | h
  · exact Or.inl (GaloisRep.mem_inertiaRing_iff.mpr ⟨h, hx⟩)
  · exact Or.inr (GaloisRep.mem_inertiaRing_iff.mpr ⟨h, IntermediateField.inv_mem _ hx⟩)

theorem not_isUnit_of_valuation_lt_one (x : inertiaRing A) (hx : A.valuation (x : ℚ̄) < 1) : ¬ IsUnit x := by
  rintro ⟨u, rfl⟩
  have h1 : ((u : inertiaRing A) : ℚ̄) * ((↑u⁻¹ : inertiaRing A) : ℚ̄) = 1 := by
    rw [← Subring.coe_mul, Units.mul_inv]; rfl
  have hle : A.valuation ((↑u⁻¹ : inertiaRing A) : ℚ̄) ≤ 1 := (A.valuation_le_one_iff _).mpr (coe_memA A _)
  have hlt : A.valuation (((u : inertiaRing A) : ℚ̄) * ((↑u⁻¹ : inertiaRing A) : ℚ̄)) < 1 := by
    rw [map_mul]; exact mul_lt_one_of_lt_of_le hx hle
  rw [h1, map_one] at hlt
  exact lt_irrefl _ hlt

instance instAlgebraField : Algebra (inertiaRing A) (inertiaField A) :=
  (({ toFun := fun x => ⟨(x : ℚ̄), coe_mem_inertiaField A x⟩
      map_one' := rfl
      map_mul' := fun _ _ => rfl
      map_zero' := rfl
      map_add' := fun _ _ => rfl } : inertiaRing A →+* inertiaField A)).toAlgebra

theorem algebraMap_field_coe (x : inertiaRing A) : ((algebraMap (inertiaRing A) (inertiaField A) x : inertiaField A) : ℚ̄) = x := rfl

instance instTowerField : IsScalarTower (inertiaRing A) (inertiaField A) ℚ̄ :=
  IsScalarTower.of_algebraMap_eq fun _ => rfl

instance instIsFractionRing : IsFractionRing (inertiaRing A) (inertiaField A) where
  map_units y := by
    apply IsUnit.mk0
    intro h0
    have : ((y.1 : inertiaRing A) : ℚ̄) = 0 := by
      have := congrArg (fun z : inertiaField A => (z : ℚ̄)) h0
      exact this
    exact nonZeroDivisors.ne_zero y.2 (Subtype.ext this)
  surj k := by
    by_cases hk0 : (k : ℚ̄) = 0
    · refine ⟨(0, 1), ?_⟩
      have : k = 0 := Subtype.ext hk0
      rw [this]; simp
    rcases mem_or_inv_mem A k.2 with h | h
    · refine ⟨(⟨k, h⟩, 1), ?_⟩
      show k * algebraMap (inertiaRing A) (inertiaField A) 1 = algebraMap (inertiaRing A) (inertiaField A) ⟨k, h⟩
      rw [map_one, mul_one]
      exact Subtype.ext rfl
    · have hne : (⟨(k : ℚ̄)⁻¹, h⟩ : inertiaRing A) ∈ nonZeroDivisors (inertiaRing A) :=
        mem_nonZeroDivisors_of_ne_zero (fun h0 => hk0 (inv_eq_zero.mp (congrArg (fun z : inertiaRing A => (z : ℚ̄)) h0)))
      refine ⟨(1, ⟨⟨(k : ℚ̄)⁻¹, h⟩, hne⟩), ?_⟩
      show k * algebraMap (inertiaRing A) (inertiaField A) ⟨(k : ℚ̄)⁻¹, h⟩ = algebraMap (inertiaRing A) (inertiaField A) 1
      rw [map_one]
      apply Subtype.ext
      show (k : ℚ̄) * (k : ℚ̄)⁻¹ = 1
      exact mul_inv_cancel₀ hk0
  exists_of_eq {a b} h := ⟨1, by
    have : ((a : ℚ̄)) = b := by
      have := congrArg (fun z : inertiaField A => (z : ℚ̄)) h
      exact this
    rw [Subtype.ext this]⟩

end InertiaRing

end GaloisRep

end

section PointTransportSection

set_option maxHeartbeats 1600000
set_option synthInstance.maxHeartbeats 400000

open scoped TensorProduct
open WithConv

namespace GaloisRep.PointTransport

section LiftPt

variable {R S L H : Type*} [CommRing R] [CommRing S] [CommRing L] [CommRing H]
  [Algebra R S] [Algebra S L] [Algebra R L] [IsScalarTower R S L] [Algebra R H]

noncomputable def liftPt (φ : WithConv (H →ₐ[R] L)) : WithConv (S ⊗[R] H →ₐ[S] L) :=
  toConv (Algebra.TensorProduct.lift (Algebra.ofId S L) φ.ofConv fun _ _ => .all _ _)

theorem liftPt_tmul (φ : WithConv (H →ₐ[R] L)) (s : S) (h : H) :
    liftPt (S := S) φ (s ⊗ₜ[R] h) = algebraMap S L s * φ h := by
  show Algebra.TensorProduct.lift (Algebra.ofId S L) φ.ofConv (fun _ _ => .all _ _) (s ⊗ₜ[R] h) = _
  rw [Algebra.TensorProduct.lift_tmul, Algebra.ofId_apply]

theorem liftPt_one_tmul (φ : WithConv (H →ₐ[R] L)) (h : H) : liftPt (S := S) φ ((1 : S) ⊗ₜ[R] h) = φ h := by
  rw [liftPt_tmul, map_one, one_mul]

theorem liftPt_injective : Function.Injective (liftPt (R := R) (S := S) (L := L) (H := H)) := by
  intro φ ψ h
  apply WithConv.ext
  apply AlgHom.ext
  intro x
  have := congrArg (fun χ : WithConv (S ⊗[R] H →ₐ[S] L) => χ ((1 : S) ⊗ₜ[R] x)) h
  simpa only [liftPt_one_tmul] using this

theorem comp_liftPt (σ : L →ₐ[S] L) (φ : WithConv (H →ₐ[R] L)) :
    σ.comp (liftPt (S := S) φ).ofConv = (liftPt (S := S) (toConv ((σ.restrictScalars R).comp φ.ofConv))).ofConv := by
  apply AlgHom.ext
  intro x
  induction x using TensorProduct.induction_on with
  | zero => rw [map_zero, map_zero]
  | tmul s h =>
    rw [AlgHom.comp_apply]
    show σ (liftPt (S := S) φ (s ⊗ₜ[R] h)) = liftPt (S := S) (toConv ((σ.restrictScalars R).comp φ.ofConv)) (s ⊗ₜ[R] h)
    rw [liftPt_tmul, liftPt_tmul, map_mul, AlgHom.commutes]
    rfl
  | add x y hx hy => rw [map_add, map_add, hx, hy]

end LiftPt

section LiftPtConv

variable {R S L H : Type*} [CommRing R] [CommRing S] [CommRing L] [CommRing H]
  [Algebra R S] [Algebra S L] [Algebra R L] [IsScalarTower R S L] [Bialgebra R H]

theorem liftPt_mul (φ ψ : WithConv (H →ₐ[R] L)) :
    liftPt (S := S) (φ * ψ) = liftPt (S := S) φ * liftPt (S := S) ψ := by
  apply WithConv.ext
  apply AlgHom.ext
  intro x
  show liftPt (S := S) (φ * ψ) x = (liftPt (S := S) φ * liftPt (S := S) ψ) x
  induction x using TensorProduct.induction_on with
  | zero => rw [map_zero, map_zero]
  | tmul s h =>
    let rr := Coalgebra.Repr.arbitrary R h
    have hco : Coalgebra.comul (R := S) (s ⊗ₜ[R] h)
        = ∑ i ∈ rr.index, ((1 : S) ⊗ₜ[R] rr.left i) ⊗ₜ[S] (s ⊗ₜ[R] rr.right i) := by
      rw [TensorProduct.comul_tmul, CommSemiring.comul_apply, ← rr.eq, TensorProduct.tmul_sum, map_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [TensorProduct.AlgebraTensorModule.tensorTensorTensorComm_tmul]
    rw [liftPt_tmul, AlgHom.convMul_apply, AlgHom.convMul_apply, ← rr.eq, map_sum, Finset.mul_sum, hco, map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Algebra.TensorProduct.lift_tmul, Algebra.TensorProduct.lift_tmul]
    show algebraMap S L s * (φ.ofConv (rr.left i) * ψ.ofConv (rr.right i))
      = liftPt (S := S) φ ((1 : S) ⊗ₜ[R] rr.left i) * liftPt (S := S) ψ (s ⊗ₜ[R] rr.right i)
    rw [liftPt_one_tmul, liftPt_tmul]
    show _ = φ.ofConv (rr.left i) * (algebraMap S L s * ψ.ofConv (rr.right i))
    ring
  | add x y hx hy => rw [map_add, map_add, hx, hy]

theorem liftPt_one : liftPt (S := S) (1 : WithConv (H →ₐ[R] L)) = 1 := by
  apply WithConv.ext
  apply AlgHom.ext
  intro x
  show liftPt (S := S) (1 : WithConv (H →ₐ[R] L)) x = (1 : WithConv (S ⊗[R] H →ₐ[S] L)) x
  induction x using TensorProduct.induction_on with
  | zero => rw [map_zero, map_zero]
  | tmul s h =>
    rw [liftPt_tmul, AlgHom.convOne_apply, AlgHom.convOne_apply, TensorProduct.counit_tmul, CommSemiring.counit_apply,
      Algebra.smul_def, map_mul, ← IsScalarTower.algebraMap_apply, mul_comm]
  | add x y hx hy => rw [map_add, map_add, hx, hy]

theorem liftPt_pow (φ : WithConv (H →ₐ[R] L)) (n : ℕ) : liftPt (S := S) (φ ^ n) = liftPt (S := S) φ ^ n := by
  induction n with
  | zero => rw [pow_zero, pow_zero, liftPt_one]
  | succ n ih => rw [pow_succ, pow_succ, liftPt_mul, ih]

end LiftPtConv

section EvGen

variable (K : Type*) (L : Type*) (B : Type*) [CommRing K] [CommRing L] [CommRing B] [Algebra K L] [Algebra K B]

noncomputable def evGen : L ⊗[K] B →ₐ[L] (WithConv (B →ₐ[K] L) → L) :=
  Algebra.TensorProduct.lift (Algebra.ofId L _)
    (Pi.algHom K _ fun ν : WithConv (B →ₐ[K] L) => (WithConv.ofConv ν : B →ₐ[K] L)) (fun _ _ => Commute.all _ _)

theorem evGen_tmul (t : L) (b : B) (ν : WithConv (B →ₐ[K] L)) : evGen K L B (t ⊗ₜ[K] b) ν = t * (WithConv.ofConv ν) b := by
  simp only [evGen, Algebra.TensorProduct.lift_tmul, Pi.mul_apply, Pi.algHom_apply]
  rw [Algebra.ofId_apply, Pi.algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply]

variable {K L B}
variable {S : Type*} [CommRing S] [Algebra K S] [Algebra S L] [IsScalarTower K S L]

theorem liftPt_surjective : Function.Surjective (liftPt (R := K) (S := S) (L := L) (H := B)) := by
  intro ψ
  refine ⟨toConv (((ψ.ofConv).restrictScalars K).comp Algebra.TensorProduct.includeRight), ?_⟩
  apply WithConv.ext
  apply AlgHom.ext
  intro x
  show liftPt (S := S) (toConv (((ψ.ofConv).restrictScalars K).comp Algebra.TensorProduct.includeRight)) x = ψ.ofConv x
  induction x using TensorProduct.induction_on with
  | zero => rw [map_zero, map_zero]
  | tmul s b =>
    rw [liftPt_tmul]
    show algebraMap S L s * ψ.ofConv ((1 : S) ⊗ₜ[K] b) = ψ.ofConv (s ⊗ₜ[K] b)
    rw [← ψ.ofConv.commutes s, ← map_mul, Algebra.TensorProduct.algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply,
      Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
  | add x y hx hy => rw [map_add, map_add, hx, hy]

noncomputable def liftPtEquiv : WithConv (B →ₐ[K] L) ≃ WithConv (S ⊗[K] B →ₐ[S] L) :=
  Equiv.ofBijective (liftPt (S := S)) ⟨liftPt_injective, liftPt_surjective⟩

@[simp] theorem liftPtEquiv_apply (φ : WithConv (B →ₐ[K] L)) : liftPtEquiv (S := S) φ = liftPt (S := S) φ := rfl

theorem finite_pts_baseChange [Finite (WithConv (B →ₐ[K] L))] : Finite (WithConv (S ⊗[K] B →ₐ[S] L)) :=
  Finite.of_surjective _ liftPt_surjective

theorem evGen_baseChange_apply (x : L ⊗[S] (S ⊗[K] B)) (φ : WithConv (B →ₐ[K] L)) :
    evGen S L (S ⊗[K] B) x (liftPt (S := S) φ)
      = evGen K L B (Algebra.TensorProduct.cancelBaseChange K S L L B x) φ := by
  induction x using TensorProduct.induction_on with
  | zero => simp only [map_zero, Pi.zero_apply]
  | tmul t y =>
    induction y using TensorProduct.induction_on with
    | zero => simp only [TensorProduct.tmul_zero, map_zero, Pi.zero_apply]
    | tmul s b =>
      rw [evGen_tmul, Algebra.TensorProduct.cancelBaseChange_tmul, evGen_tmul, Algebra.smul_def]
      show t * liftPt (S := S) φ (s ⊗ₜ[K] b) = _
      rw [liftPt_tmul]
      ring
    | add y₁ y₂ h₁ h₂ => simp only [TensorProduct.tmul_add, map_add, Pi.add_apply, h₁, h₂]
  | add x y hx hy => simp only [map_add, Pi.add_apply, hx, hy]

theorem evGen_baseChange_bijective (hev : Function.Bijective (evGen K L B)) :
    Function.Bijective (evGen S L (S ⊗[K] B)) := by

  let pre : (WithConv (B →ₐ[K] L) → L) ≃ (WithConv (S ⊗[K] B →ₐ[S] L) → L) :=
    (liftPtEquiv (K := K) (L := L) (B := B) (S := S)).arrowCongr (Equiv.refl L)
  have hfac : ⇑(evGen S L (S ⊗[K] B))
      = pre ∘ evGen K L B ∘ Algebra.TensorProduct.cancelBaseChange K S L L B := by
    funext x
    funext ψ
    obtain ⟨φ, rfl⟩ := liftPt_surjective (K := K) (L := L) (S := S) ψ
    rw [evGen_baseChange_apply]
    show _ = evGen K L B _ ((liftPtEquiv (S := S)).symm (liftPtEquiv (S := S) φ))
    rw [Equiv.symm_apply_apply]
  rw [hfac]
  exact pre.bijective.comp (hev.comp (Algebra.TensorProduct.cancelBaseChange K S L L B).bijective)

end EvGen

section LiftPtMulEquiv

variable {R S L H : Type*} [CommRing R] [CommRing S] [CommRing L] [CommRing H]
  [Algebra R S] [Algebra S L] [Algebra R L] [IsScalarTower R S L] [Bialgebra R H]

noncomputable def liftPtMulEquiv : WithConv (H →ₐ[R] L) ≃* WithConv (S ⊗[R] H →ₐ[S] L) :=
  { liftPtEquiv (K := R) (L := L) (B := H) (S := S) with map_mul' := liftPt_mul }

@[simp] theorem liftPtMulEquiv_apply (φ : WithConv (H →ₐ[R] L)) :
    liftPtMulEquiv (S := S) φ = liftPt (S := S) φ := rfl

theorem liftPtMulEquiv_symm_apply (ψ : WithConv (S ⊗[R] H →ₐ[S] L)) :
    (liftPtMulEquiv (S := S)).symm ψ = (liftPtEquiv (S := S)).symm ψ := rfl

end LiftPtMulEquiv

section Valuative

variable {R S L H : Type*} [CommRing R] [CommRing S] [Field L] [CommRing H]
  [Algebra R S] [Algebra S L] [Algebra R L] [IsScalarTower R S L] [Bialgebra R H]
  {Γ₀ : Type*} [LinearOrderedCommGroupWithZero Γ₀] (v : Valuation L Γ₀)

theorem valuation_liftPt_sub_lt_one (hS : ∀ s : S, v (algebraMap S L s) ≤ 1)
    (φ : WithConv (H →ₐ[R] L)) (hφ : ∀ h : H, v (φ h - algebraMap R L (Coalgebra.counit (R := R) h)) < 1)
    (x : S ⊗[R] H) :
    v (liftPt (S := S) φ x - algebraMap S L (Coalgebra.counit (R := S) x)) < 1 := by
  induction x using TensorProduct.induction_on with
  | zero => rw [map_zero, map_zero, map_zero, sub_zero, map_zero]; exact zero_lt_one
  | tmul s h =>
    rw [liftPt_tmul, TensorProduct.counit_tmul, CommSemiring.counit_apply, Algebra.smul_def, map_mul,
      ← IsScalarTower.algebraMap_apply, mul_comm (algebraMap R L _), ← mul_sub, map_mul]
    exact mul_lt_one_of_nonneg_of_lt_one_right (hS s) zero_le' (hφ h)
  | add x y hx hy =>
    rw [map_add, map_add, map_add]
    have : liftPt (S := S) φ x + liftPt (S := S) φ y - (algebraMap S L (Coalgebra.counit (R := S) x)
        + algebraMap S L (Coalgebra.counit (R := S) y))
        = (liftPt (S := S) φ x - algebraMap S L (Coalgebra.counit (R := S) x))
          + (liftPt (S := S) φ y - algebraMap S L (Coalgebra.counit (R := S) y)) := by ring
    rw [this]
    exact lt_of_le_of_lt (v.map_add _ _) (max_lt hx hy)

end Valuative

end GaloisRep.PointTransport

noncomputable section

namespace GaloisRep.InertiaRing

section Dec

local notation "ℚ̄" => AlgebraicClosure ℚ
local notation "Gal" => (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)

variable (A : ValuationSubring ℚ̄)

theorem algebraMap_O_apply (z : GaloisRep.inertiaRing A) : algebraMap (GaloisRep.inertiaRing A) ℚ̄ z = (z : ℚ̄) := rfl

theorem algebraMap_O_injective : Function.Injective (algebraMap (GaloisRep.inertiaRing A) ℚ̄) := Subtype.val_injective

theorem valuation_algebraMap_O_le_one (z : GaloisRep.inertiaRing A) : A.valuation (algebraMap (GaloisRep.inertiaRing A) ℚ̄ z) ≤ 1 :=
  (A.valuation_le_one_iff _).mpr (GaloisRep.InertiaRing.coe_memA A z)

noncomputable def galF {σ : Gal} (hσ : σ ∈ A.inertiaSubgroupIn ℚ) : ℚ̄ ≃ₐ[GaloisRep.inertiaField A] ℚ̄ :=
  { σ with commutes' := fun x => GaloisRep.mem_inertiaField_iff.mp x.2 σ hσ }

@[simp] theorem galF_apply {σ : Gal} (hσ : σ ∈ A.inertiaSubgroupIn ℚ) (x : ℚ̄) : galF A hσ x = σ x := rfl

noncomputable def rhoI (σ : A.inertiaSubgroupIn ℚ) : ℚ̄ ≃ₐ[GaloisRep.inertiaField A] ℚ̄ := galF A σ.2

@[simp] theorem rhoI_apply (σ : A.inertiaSubgroupIn ℚ) (x : ℚ̄) : rhoI A σ x = (σ : Gal) x := rfl

theorem hfix_I (c : ℚ̄) (hc : ∀ σ : A.inertiaSubgroupIn ℚ, rhoI A σ c = c) :
    c ∈ Set.range (algebraMap (GaloisRep.inertiaField A) ℚ̄) :=
  ⟨⟨c, GaloisRep.mem_inertiaField_iff.mpr fun σ hσ => hc ⟨σ, hσ⟩⟩, rfl⟩

noncomputable def galO {σ : Gal} (hσ : σ ∈ A.inertiaSubgroupIn ℚ) : ℚ̄ →ₐ[GaloisRep.inertiaRing A] ℚ̄ :=
  { (σ : ℚ̄ →+* ℚ̄) with commutes' := fun z => GaloisRep.InertiaRing.coe_fixed A z σ hσ }

@[simp] theorem galO_apply {σ : Gal} (hσ : σ ∈ A.inertiaSubgroupIn ℚ) (x : ℚ̄) : galO A hσ x = σ x := rfl

theorem galF_hn {σ : Gal} (hσ : σ ∈ A.inertiaSubgroupIn ℚ) {N n : ℕ}
    (hn : ∀ ζ : ℚ̄, ζ ^ N = 1 → σ ζ = ζ ^ n) : ∀ ζ : ℚ̄, ζ ^ N = 1 → galF A hσ ζ = ζ ^ n := hn

theorem galF_fix_iff {σ : Gal} (hσ : σ ∈ A.inertiaSubgroupIn ℚ) {X : Type*} (f : X → ℚ̄) :
    (∀ x, galF A hσ (f x) = f x) ↔ ∀ x, σ (f x) = f x := Iff.rfl

theorem galF_comp_iff {σ : Gal} (hσ : σ ∈ A.inertiaSubgroupIn ℚ) {X : Type*} (f g : X → ℚ̄) :
    (∀ x, g x = galF A hσ (f x)) ↔ ∀ x, g x = σ (f x) := Iff.rfl

theorem galF_restrictScalars {σ : Gal} (hσ : σ ∈ A.inertiaSubgroupIn ℚ) :
    ((galF A hσ : ℚ̄ →ₐ[GaloisRep.inertiaField A] ℚ̄).restrictScalars (GaloisRep.inertiaRing A)) = galO A hσ :=
  AlgHom.ext fun _ => rfl

variable (q : ℕ) [Fact q.Prime]

theorem ratCast_mem_of_coprime (hA : ((q : ℕ) : ℚ̄) ∈ A.nonunits) {r : ℚ} (hr : r.den.Coprime q) : (r : ℚ̄) ∈ A := by
  have hq : q.Prime := Fact.out
  have hden : A.valuation ((r.den : ℚ̄)) = 1 := by
    have hle : A.valuation ((r.den : ℚ̄)) ≤ 1 := (A.valuation_le_one_iff _).mpr (natCast_mem A r.den)
    refine le_antisymm hle (not_lt.mp fun hlt => ?_)
    have hq1 : A.valuation ((q : ℚ̄)) < 1 := (A.mem_nonunits_iff).mp hA
    have hg := Nat.gcd_eq_gcd_ab r.den q
    rw [Nat.Coprime.gcd_eq_one hr, Nat.cast_one] at hg
    have h1 : (1 : ℚ̄) = (r.den : ℚ̄) * (Nat.gcdA r.den q : ℚ̄) + (q : ℚ̄) * (Nat.gcdB r.den q : ℚ̄) := by
      exact_mod_cast congrArg (fun z : ℤ => (z : ℚ̄)) hg
    have hlt' : A.valuation 1 < 1 := by
      rw [h1]
      refine lt_of_le_of_lt (A.valuation.map_add _ _) (max_lt ?_ ?_)
      · rw [map_mul]
        exact mul_lt_one_of_nonneg_of_lt_one_left zero_le' hlt ((A.valuation_le_one_iff _).mpr (intCast_mem A _))
      · rw [map_mul]
        exact mul_lt_one_of_nonneg_of_lt_one_left zero_le' hq1 ((A.valuation_le_one_iff _).mpr (intCast_mem A _))
    rw [map_one] at hlt'
    exact lt_irrefl _ hlt'
  have hden0 : (r.den : ℚ̄) ≠ 0 := by exact_mod_cast r.den_nz
  rw [← A.valuation_le_one_iff, Rat.cast_def, map_div₀, hden, div_one]
  exact (A.valuation_le_one_iff _).mpr (intCast_mem A r.num)

@[reducible] noncomputable def algebraRO (hA : ((q : ℕ) : ℚ̄) ∈ A.nonunits) :
    Algebra (GaloisRep.ratLocalizedAt q) (GaloisRep.inertiaRing A) :=
  RingHom.toAlgebra
    { toFun := fun r => GaloisRep.InertiaRing.mkO (((r : ℚ) : ℚ̄)) (ratCast_mem_of_coprime A q hA r.2)
        (fun σ _ => by rw [← eq_ratCast (algebraMap ℚ ℚ̄), AlgEquiv.commutes])
      map_one' := Subtype.ext (by simp only [GaloisRep.InertiaRing.coe_mkO, Subring.coe_one]; push_cast; try rfl)
      map_mul' := fun a b => Subtype.ext (by simp only [GaloisRep.InertiaRing.coe_mkO, Subring.coe_mul]; push_cast; try rfl)
      map_zero' := Subtype.ext (by simp only [GaloisRep.InertiaRing.coe_mkO, Subring.coe_zero]; push_cast; try rfl)
      map_add' := fun a b => Subtype.ext (by simp only [GaloisRep.InertiaRing.coe_mkO, Subring.coe_add]; push_cast; try rfl) }

theorem algebraMap_RO_coe (hA : ((q : ℕ) : ℚ̄) ∈ A.nonunits) (r : GaloisRep.ratLocalizedAt q) :
    letI := algebraRO A q hA
    ((algebraMap (GaloisRep.ratLocalizedAt q) (GaloisRep.inertiaRing A) r : GaloisRep.inertiaRing A) : ℚ̄) = ((r : ℚ) : ℚ̄) := rfl

theorem towerROQbar (hA : ((q : ℕ) : ℚ̄) ∈ A.nonunits) :
    letI := algebraRO A q hA
    IsScalarTower (GaloisRep.ratLocalizedAt q) (GaloisRep.inertiaRing A) ℚ̄ := by
  letI := algebraRO A q hA
  refine IsScalarTower.of_algebraMap_eq fun r => ?_
  rw [algebraMap_O_apply, algebraMap_RO_coe]
  show algebraMap (GaloisRep.ratLocalizedAt q) ℚ̄ r = ((r : ℚ) : ℚ̄)
  rw [IsScalarTower.algebraMap_apply (GaloisRep.ratLocalizedAt q) ℚ ℚ̄, eq_ratCast]
  rfl

end Dec

section T1

local notation "ℚ̄" => AlgebraicClosure ℚ
local notation "Gal" => (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)

variable (A : ValuationSubring ℚ̄)
variable {S : Type*} [CommRing S] [Bialgebra (GaloisRep.inertiaRing A) S] [Module.Finite (GaloisRep.inertiaRing A) S]

theorem apply_mem_A (ψ : S →ₐ[GaloisRep.inertiaRing A] ℚ̄) (s : S) : ψ s ∈ A := by
  have h1 : IsIntegral (GaloisRep.inertiaRing A) (ψ s) := (Algebra.IsIntegral.isIntegral s).map ψ
  obtain ⟨p, hpm, hpe⟩ := h1
  let j : GaloisRep.inertiaRing A →+* A :=
    { toFun := fun z => ⟨(z : ℚ̄), GaloisRep.InertiaRing.coe_memA A z⟩
      map_one' := Subtype.ext rfl
      map_mul' := fun a b => Subtype.ext rfl
      map_zero' := Subtype.ext rfl
      map_add' := fun a b => Subtype.ext rfl }
  have hj : (algebraMap A ℚ̄).comp j = algebraMap (GaloisRep.inertiaRing A) ℚ̄ := RingHom.ext fun _ => rfl
  have h2 : IsIntegral A (ψ s) := by
    refine ⟨p.map j, hpm.map j, ?_⟩
    rw [Polynomial.eval₂_map, hj]
    exact hpe
  obtain ⟨y, hy⟩ := IsIntegrallyClosed.isIntegral_iff.mp h2
  rw [← hy]; exact y.2

noncomputable def toQbarPt (x : WithConv (S →ₐ[GaloisRep.inertiaRing A] GaloisRep.inertiaRing A)) :
    WithConv (S →ₐ[GaloisRep.inertiaRing A] ℚ̄) :=
  toConv ((Algebra.ofId (GaloisRep.inertiaRing A) ℚ̄).comp x.ofConv)

omit [Module.Finite (GaloisRep.inertiaRing A) S] in
theorem toQbarPt_apply (x : WithConv (S →ₐ[GaloisRep.inertiaRing A] GaloisRep.inertiaRing A)) (s : S) :
    toQbarPt A x s = algebraMap (GaloisRep.inertiaRing A) ℚ̄ (x s) := rfl

omit [Module.Finite (GaloisRep.inertiaRing A) S] in
theorem toQbarPt_mul (x y : WithConv (S →ₐ[GaloisRep.inertiaRing A] GaloisRep.inertiaRing A)) :
    toQbarPt A (x * y) = toQbarPt A x * toQbarPt A y := by
  unfold toQbarPt
  rw [AlgHom.comp_convMul_distrib, WithConv.toConv_ofConv]

omit [Module.Finite (GaloisRep.inertiaRing A) S] in
theorem toQbarPt_one : toQbarPt A (1 : WithConv (S →ₐ[GaloisRep.inertiaRing A] GaloisRep.inertiaRing A)) = 1 := by
  apply WithConv.ext
  apply AlgHom.ext
  intro s
  show algebraMap (GaloisRep.inertiaRing A) ℚ̄ ((1 : WithConv (S →ₐ[GaloisRep.inertiaRing A] GaloisRep.inertiaRing A)) s)
    = (1 : WithConv (S →ₐ[GaloisRep.inertiaRing A] ℚ̄)) s
  rw [AlgHom.convOne_apply, AlgHom.convOne_apply]
  rfl

omit [Module.Finite (GaloisRep.inertiaRing A) S] in
theorem toQbarPt_pow (x : WithConv (S →ₐ[GaloisRep.inertiaRing A] GaloisRep.inertiaRing A)) (n : ℕ) :
    toQbarPt A (x ^ n) = toQbarPt A x ^ n := by
  induction n with
  | zero => rw [pow_zero, pow_zero, toQbarPt_one]
  | succ n ih => rw [pow_succ, pow_succ, toQbarPt_mul, ih]

omit [Module.Finite (GaloisRep.inertiaRing A) S] in
theorem toQbarPt_injective : Function.Injective (toQbarPt A (S := S)) := by
  intro x y h
  apply WithConv.ext
  apply AlgHom.ext
  intro s
  apply algebraMap_O_injective A
  rw [← toQbarPt_apply, ← toQbarPt_apply, h]

theorem exists_OPt_of_fixed [IsLocalRing (GaloisRep.inertiaRing A)] (ψ : WithConv (S →ₐ[GaloisRep.inertiaRing A] ℚ̄))
    (hfix : ∀ σ : Gal, σ ∈ A.inertiaSubgroupIn ℚ → ∀ s : S, σ (ψ s) = ψ s) :
    ∃ x : WithConv (S →ₐ[GaloisRep.inertiaRing A] GaloisRep.inertiaRing A),
      toQbarPt A x = ψ ∧
      (∀ s, algebraMap (GaloisRep.inertiaRing A) ℚ̄ (x s) = ψ s) ∧
      (∀ k : ℕ, ψ ^ k = 1 ↔ x ^ k = 1) ∧
      ((∀ s, A.valuation (ψ s - algebraMap (GaloisRep.inertiaRing A) ℚ̄ (Coalgebra.counit (R := GaloisRep.inertiaRing A) s)) < 1) →
        ∀ s, x s - algebraMap (GaloisRep.inertiaRing A) (GaloisRep.inertiaRing A) (Coalgebra.counit (R := GaloisRep.inertiaRing A) s)
          ∈ IsLocalRing.maximalIdeal (GaloisRep.inertiaRing A)) := by
  let x₀ : S → GaloisRep.inertiaRing A := fun s => GaloisRep.InertiaRing.mkO (ψ s) (apply_mem_A A ψ.ofConv s) (fun σ hσ => hfix σ hσ s)
  have hx₀ : ∀ s, ((x₀ s : GaloisRep.inertiaRing A) : ℚ̄) = ψ s := fun s => rfl
  let xa : S →ₐ[GaloisRep.inertiaRing A] GaloisRep.inertiaRing A :=
    { toFun := x₀
      map_one' := Subtype.ext (by rw [hx₀]; exact map_one ψ.ofConv)
      map_mul' := fun a b => Subtype.ext (by rw [hx₀, Subring.coe_mul, hx₀, hx₀]; exact map_mul ψ.ofConv a b)
      map_zero' := Subtype.ext (by rw [hx₀]; exact map_zero ψ.ofConv)
      map_add' := fun a b => Subtype.ext (by rw [hx₀, Subring.coe_add, hx₀, hx₀]; exact map_add ψ.ofConv a b)
      commutes' := fun z => Subtype.ext (by rw [hx₀]; exact ψ.ofConv.commutes z) }
  refine ⟨toConv xa, ?_, fun s => rfl, fun k => ?_, fun hred s => ?_⟩
  · exact WithConv.ext (AlgHom.ext fun s => rfl)
  · have hψ : toQbarPt A (toConv xa) = ψ := WithConv.ext (AlgHom.ext fun s => rfl)
    constructor
    · intro h
      apply toQbarPt_injective A
      rw [toQbarPt_pow, hψ, h, toQbarPt_one]
    · intro h
      rw [← hψ, ← toQbarPt_pow, h, toQbarPt_one]
  · apply (IsLocalRing.mem_maximalIdeal _).mpr
    apply GaloisRep.InertiaRing.not_isUnit_of_valuation_lt_one
    have hid : ∀ y : GaloisRep.inertiaRing A, algebraMap (GaloisRep.inertiaRing A) (GaloisRep.inertiaRing A) y = y := fun _ => rfl
    rw [hid, AddSubgroupClass.coe_sub]
    exact hred s

end T1

end GaloisRep.InertiaRing

end

end PointTransportSection


