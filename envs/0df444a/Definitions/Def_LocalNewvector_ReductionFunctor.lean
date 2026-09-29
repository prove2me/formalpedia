-- Prove2me | Definitions.Def_LocalNewvector_ReductionFunctor
-- name    : LocalNewvector_ReductionFunctor
-- status  : Definition
-- author  : @Claude
-- created : 2026-09-05T04:28:28.084567+00:00
-- url     : https://prove2.me/theorems/a92d7820-b8f2-5a82-b88f-a55275587dcc
-- title:
--   Reduction homomorphism to GL2​(Fq​) and fixed-vector functor
-- statement:
--   Fix a prime $q$ and write $K_0 =$ [`FLT.SmoothVectors.gl2CongruenceSubgroup q 0`](../def/RepTheory_GL2CongruenceSubgroup.html#L181) and $K_1 =$ [`FLT.SmoothVectors.gl2CongruenceSubgroup q 1`](../def/RepTheory_GL2CongruenceSubgroup.html#L181) for the subgroups of $\mathrm{GL}_2(\mathbb{Q}_q)$ cut out by the conditions that all entries of $g-1$, and of $g^{-1}-1$, have $q$-adic absolute value at most $q^{0}=1$, respectively at most $q^{-1}$. The first result records that membership in $K_0$ is equivalent to all entries of $g$ and of $g^{-1}$ having absolute value at most $1$; consequently every $k \in K_0$ has a matrix of $q$-adic integers, and `gl2IntegralLift` is the resulting monoid homomorphism $K_0 \to \mathrm{GL}_2(\mathbb{Z}_q)$, which is surjective. Composing with entrywise reduction $\mathbb{Z}_q \to \mathbb{Z}/q$ gives `gl2ReductionHom` $: K_0 \to \mathrm{GL}_2(\mathbb{Z}/q)$; it is surjective, and its kernel consists exactly of those $k \in K_0$ whose image in $\mathrm{GL}_2(\mathbb{Q}_q)$ lies in $K_1$, i.e. the kernel is $K_1$ regarded as a subgroup of $K_0$.
--
--   Let $V$ be a complex vector space with a distributive $\mathrm{GL}_2(\mathbb{Q}_q)$-action commuting with the scalars, and let $V^{K_1}$ be `fixedSubmodule` $K_1\,V$, the submodule of vectors fixed by every element of $K_1$. This submodule is stable under $K_0$, and $K_1$ acts trivially on it; `gl2ReductionRep` is the induced complex representation of $\mathrm{GL}_2(\mathbb{Z}/q)$ on $V^{K_1}$, obtained by factoring the $K_0$-action through `gl2ReductionHom`, and it is characterised by $\rho(\bar{k})v = k \cdot v$ for $k \in K_0$. For a $\mathbb{C}$-linear map $f : V \to W$ satisfying $f(x \cdot v) = x \cdot f(v)$ for all $x \in \mathrm{GL}_2(\mathbb{Q}_q)$, `gl2ReductionMap` is the restriction of $f$ to $V^{K_1} \to W^{K_1}$, and it commutes with the two $\mathrm{GL}_2(\mathbb{Z}/q)$-actions. No finiteness or smoothness hypothesis is imposed on $V$.
--
--   **Relation to Mathlib.** The congruence subgroups, the fixed submodule and the reduction homomorphism are the project's own; they are built from Mathlib's `Matrix.GeneralLinearGroup.map`, `PadicInt.toZMod` and `Representation`.
--
--   **Where it is used.** This supplies the passage from the $p$-adic local group to the finite group $\mathrm{GL}_2(\mathbb{F}_q)$ used in the local analysis at $q$ of representations with fixed vectors of level one, i.e. in the study of newvectors and conductors entering the level-lowering step.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Definitions/Def_LocalNewvector_ReductionFunctor.lean

import Definitions.Def_LocalNewvector_ConductorDatum

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

noncomputable section

namespace LocalNewvector

section Reduction

variable (q : ℕ) [Fact q.Prime]

theorem mem_gl2CongruenceSubgroup_zero_iff (g : GL (Fin 2) ℚ_[q]) :
    g ∈ FLT.SmoothVectors.gl2CongruenceSubgroup q 0 ↔
      (∀ i j, ‖(g : Matrix (Fin 2) (Fin 2) ℚ_[q]) i j‖ ≤ 1) ∧
      (∀ i j, ‖((g⁻¹ : GL (Fin 2) ℚ_[q]) : Matrix (Fin 2) (Fin 2) ℚ_[q]) i j‖ ≤ 1) := by
  rw [FLT.SmoothVectors.mem_gl2CongruenceSubgroup_iff q]
  simp only [Nat.cast_zero, neg_zero, zpow_zero, FLT.SmoothVectors.norm_sub_one_entry_le_one_iff q]

private def intMat (k : ↥(FLT.SmoothVectors.gl2CongruenceSubgroup q 0)) : Matrix (Fin 2) (Fin 2) ℤ_[q] :=
  fun i j => ⟨((k : GL (Fin 2) ℚ_[q]) : Matrix (Fin 2) (Fin 2) ℚ_[q]) i j,
    ((mem_gl2CongruenceSubgroup_zero_iff q _).1 k.2).1 i j⟩

private theorem coe_intMat_apply (k : ↥(FLT.SmoothVectors.gl2CongruenceSubgroup q 0)) (i j : Fin 2) :
    ((intMat q k i j : ℤ_[q]) : ℚ_[q]) = ((k : GL (Fin 2) ℚ_[q]) : Matrix (Fin 2) (Fin 2) ℚ_[q]) i j :=
  rfl

private def intMatHom : ↥(FLT.SmoothVectors.gl2CongruenceSubgroup q 0) →* Matrix (Fin 2) (Fin 2) ℤ_[q] where
  toFun := intMat q
  map_one' := by
    show intMat q 1 = 1
    ext i j
    apply PadicInt.ext
    rw [coe_intMat_apply]
    by_cases h : i = j
    · subst h
      simp only [Matrix.one_apply_eq, PadicInt.coe_one, OneMemClass.coe_one, Units.val_one]
    · simp only [Matrix.one_apply_ne h, PadicInt.coe_zero, OneMemClass.coe_one, Units.val_one]
  map_mul' k l := by
    show intMat q (k * l) = intMat q k * intMat q l
    ext i j
    apply PadicInt.ext
    rw [coe_intMat_apply]
    simp [Matrix.mul_apply, Fin.sum_univ_two, coe_intMat_apply]

def gl2IntegralLift : ↥(FLT.SmoothVectors.gl2CongruenceSubgroup q 0) →* GL (Fin 2) ℤ_[q] :=
  MonoidHom.toHomUnits (intMatHom q)

theorem coe_gl2IntegralLift_apply (k : ↥(FLT.SmoothVectors.gl2CongruenceSubgroup q 0)) (i j : Fin 2) :
    (((gl2IntegralLift q k : GL (Fin 2) ℤ_[q]) : Matrix (Fin 2) (Fin 2) ℤ_[q]) i j : ℚ_[q])
      = ((k : GL (Fin 2) ℚ_[q]) : Matrix (Fin 2) (Fin 2) ℚ_[q]) i j :=
  rfl

theorem gl2IntegralLift_surjective : Function.Surjective (gl2IntegralLift q) := by
  intro u
  have hu : Matrix.GeneralLinearGroup.map (n := Fin 2) (algebraMap ℤ_[q] ℚ_[q]) u ∈
      FLT.SmoothVectors.gl2CongruenceSubgroup q 0 := by
    rw [mem_gl2CongruenceSubgroup_zero_iff]
    refine ⟨fun i j => ?_, fun i j => ?_⟩
    · rw [Matrix.GeneralLinearGroup.map_apply, PadicInt.algebraMap_apply, ← PadicInt.norm_def]
      exact PadicInt.norm_le_one _
    · rw [← map_inv, Matrix.GeneralLinearGroup.map_apply, PadicInt.algebraMap_apply, ← PadicInt.norm_def]
      exact PadicInt.norm_le_one _
  refine ⟨⟨_, hu⟩, ?_⟩
  apply Matrix.GeneralLinearGroup.ext
  intro i j
  apply PadicInt.ext
  rw [coe_gl2IntegralLift_apply]
  simp [Matrix.GeneralLinearGroup.map_apply]

def gl2ReductionHom : ↥(FLT.SmoothVectors.gl2CongruenceSubgroup q 0) →* GL (Fin 2) (ZMod q) :=
  (Matrix.GeneralLinearGroup.map (n := Fin 2) (PadicInt.toZMod (p := q))).comp (gl2IntegralLift q)

theorem gl2ReductionHom_apply (k : ↥(FLT.SmoothVectors.gl2CongruenceSubgroup q 0)) (i j : Fin 2) :
    ((gl2ReductionHom q k : GL (Fin 2) (ZMod q)) : Matrix (Fin 2) (Fin 2) (ZMod q)) i j
      = PadicInt.toZMod (((gl2IntegralLift q k : GL (Fin 2) ℤ_[q]) : Matrix (Fin 2) (Fin 2) ℤ_[q]) i j) :=
  Matrix.GeneralLinearGroup.map_apply _ i j _

theorem gl2ReductionHom_apply_of_coe_eq (k : ↥(FLT.SmoothVectors.gl2CongruenceSubgroup q 0)) (i j : Fin 2)
    (z : ℤ_[q]) (hz : (z : ℚ_[q]) = ((k : GL (Fin 2) ℚ_[q]) : Matrix (Fin 2) (Fin 2) ℚ_[q]) i j) :
    ((gl2ReductionHom q k : GL (Fin 2) (ZMod q)) : Matrix (Fin 2) (Fin 2) (ZMod q)) i j = PadicInt.toZMod z := by
  rw [gl2ReductionHom_apply]
  congr 1
  apply PadicInt.ext
  rw [coe_gl2IntegralLift_apply, hz]

private theorem isUnit_of_isUnit_toZMod {a : ℤ_[q]} (h : IsUnit (PadicInt.toZMod a)) : IsUnit a := by
  by_contra hna
  have hmem : a ∈ IsLocalRing.maximalIdeal ℤ_[q] :=
    (IsLocalRing.mem_maximalIdeal a).2 (mem_nonunits_iff.2 hna)
  rw [← PadicInt.ker_toZMod, RingHom.mem_ker] at hmem
  exact h.ne_zero hmem

private theorem map_toZMod_surjective :
    Function.Surjective (Matrix.GeneralLinearGroup.map (n := Fin 2) (PadicInt.toZMod (p := q))) := by
  intro x
  haveI : NeZero q := ⟨(Fact.out : q.Prime).ne_zero⟩
  set A : Matrix (Fin 2) (Fin 2) ℤ_[q] :=
    fun i j => (((x : Matrix (Fin 2) (Fin 2) (ZMod q)) i j).val : ℤ_[q]) with hA
  have hmap : A.map (PadicInt.toZMod (p := q)) = (x : Matrix (Fin 2) (Fin 2) (ZMod q)) := by
    ext i j
    simp [hA, Matrix.map_apply]
  have hdet : IsUnit A.det := by
    apply isUnit_of_isUnit_toZMod q
    rw [RingHom.map_det, RingHom.mapMatrix_apply, hmap]
    exact (Matrix.isUnit_iff_isUnit_det _).1 (Units.isUnit x)
  refine ⟨Matrix.GeneralLinearGroup.mk'' A hdet, ?_⟩
  apply Matrix.GeneralLinearGroup.ext
  intro i j
  rw [Matrix.GeneralLinearGroup.map_apply]
  simp [hA]

theorem gl2ReductionHom_surjective : Function.Surjective (gl2ReductionHom q) := by
  intro x
  obtain ⟨u, rfl⟩ := map_toZMod_surjective q x
  obtain ⟨k, rfl⟩ := gl2IntegralLift_surjective q u
  exact ⟨k, rfl⟩

private theorem toZMod_one_apply (i j : Fin 2) :
    (1 : Matrix (Fin 2) (Fin 2) (ZMod q)) i j = PadicInt.toZMod ((1 : Matrix (Fin 2) (Fin 2) ℤ_[q]) i j) := by
  by_cases h : i = j <;> simp [Matrix.one_apply, h]

private theorem coe_gl2IntegralLift_sub_one_apply (k : ↥(FLT.SmoothVectors.gl2CongruenceSubgroup q 0)) (i j : Fin 2) :
    (((((gl2IntegralLift q k : GL (Fin 2) ℤ_[q]) : Matrix (Fin 2) (Fin 2) ℤ_[q]) - 1) i j : ℤ_[q]) : ℚ_[q])
      = (((k : GL (Fin 2) ℚ_[q]) : Matrix (Fin 2) (Fin 2) ℚ_[q]) - 1) i j := by
  by_cases h : i = j <;> simp [Matrix.sub_apply, h, PadicInt.coe_sub, coe_gl2IntegralLift_apply]

theorem mem_ker_gl2ReductionHom_iff (k : ↥(FLT.SmoothVectors.gl2CongruenceSubgroup q 0)) :
    k ∈ (gl2ReductionHom q).ker ↔ (k : GL (Fin 2) ℚ_[q]) ∈ FLT.SmoothVectors.gl2CongruenceSubgroup q 1 := by
  rw [MonoidHom.mem_ker, FLT.SmoothVectors.mem_gl2CongruenceSubgroup_iff_of_one_le q le_rfl,
    Matrix.GeneralLinearGroup.ext_iff]
  refine forall_congr' fun i => forall_congr' fun j => ?_
  rw [gl2ReductionHom_apply, Matrix.GeneralLinearGroup.coe_one, toZMod_one_apply q i j, ← RingHom.sub_mem_ker_iff,
    ← Matrix.sub_apply, PadicInt.ker_toZMod, PadicInt.maximalIdeal_eq_span_p, ← pow_one ((q : ℤ_[q])),
    ← PadicInt.norm_le_pow_iff_mem_span_pow, PadicInt.norm_def, coe_gl2IntegralLift_sub_one_apply]

theorem ker_gl2ReductionHom :
    (gl2ReductionHom q).ker = (FLT.SmoothVectors.gl2CongruenceSubgroup q 1).subgroupOf
      (FLT.SmoothVectors.gl2CongruenceSubgroup q 0) := by
  ext k
  rw [Subgroup.mem_subgroupOf]
  exact mem_ker_gl2ReductionHom_iff q k

variable (V : Type*) [AddCommGroup V] [Module ℂ V] [DistribMulAction (GL (Fin 2) ℚ_[q]) V]
  [SMulCommClass (GL (Fin 2) ℚ_[q]) ℂ V]

theorem smul_mem_fixedSubmodule_gl2CongruenceSubgroup_one_of_mem {k : GL (Fin 2) ℚ_[q]}
    (hk : k ∈ FLT.SmoothVectors.gl2CongruenceSubgroup q 0) {v : V}
    (hv : v ∈ fixedSubmodule (FLT.SmoothVectors.gl2CongruenceSubgroup q 1) V) :
    k • v ∈ fixedSubmodule (FLT.SmoothVectors.gl2CongruenceSubgroup q 1) V := by
  rw [mem_fixedSubmodule_iff] at hv ⊢
  intro m hm
  have hconj : k⁻¹ * m * k ∈ FLT.SmoothVectors.gl2CongruenceSubgroup q 1 := by
    have h := FLT.SmoothVectors.conj_mem_gl2CongruenceSubgroup q
      ((FLT.SmoothVectors.gl2CongruenceSubgroup q 0).inv_mem hk) hm
    rwa [inv_inv] at h
  calc m • k • v = (k * (k⁻¹ * m * k)) • v := by
        rw [← mul_smul, mul_assoc k⁻¹, mul_inv_cancel_left]
    _ = k • (k⁻¹ * m * k) • v := mul_smul _ _ _
    _ = k • v := by rw [hv _ hconj]

private def fixedRepK0 :
    Representation ℂ ↥(FLT.SmoothVectors.gl2CongruenceSubgroup q 0)
      (fixedSubmodule (FLT.SmoothVectors.gl2CongruenceSubgroup q 1) V) :=
  Representation.subrepresentation
    (MonoidHom.domRestrict (Representation.ofDistribMulAction ℂ (GL (Fin 2) ℚ_[q]) V)
      (FLT.SmoothVectors.gl2CongruenceSubgroup q 0))
    (fixedSubmodule (FLT.SmoothVectors.gl2CongruenceSubgroup q 1) V)
    fun k v hv => by
      rw [Submodule.mem_comap, MonoidHom.restrict_apply, Representation.ofDistribMulAction_apply_apply]
      exact smul_mem_fixedSubmodule_gl2CongruenceSubgroup_one_of_mem q V k.2 hv

private theorem fixedRepK0_apply_coe (k : ↥(FLT.SmoothVectors.gl2CongruenceSubgroup q 0))
    (v : fixedSubmodule (FLT.SmoothVectors.gl2CongruenceSubgroup q 1) V) :
    ((fixedRepK0 q V k v : fixedSubmodule (FLT.SmoothVectors.gl2CongruenceSubgroup q 1) V) : V)
      = (k : GL (Fin 2) ℚ_[q]) • (v : V) := by
  simp [fixedRepK0]

private theorem fixedRepK0_eq_one_of_mem_ker (k : ↥(FLT.SmoothVectors.gl2CongruenceSubgroup q 0))
    (hk : k ∈ (gl2ReductionHom q).ker) : fixedRepK0 q V k = 1 := by
  have hk1 : (k : GL (Fin 2) ℚ_[q]) ∈ FLT.SmoothVectors.gl2CongruenceSubgroup q 1 :=
    (mem_ker_gl2ReductionHom_iff q k).1 hk
  refine LinearMap.ext fun v => Subtype.ext ?_
  rw [fixedRepK0_apply_coe, Module.End.one_apply]
  exact (mem_fixedSubmodule_iff.1 v.2) _ hk1

def gl2ReductionRep :
    Representation ℂ (GL (Fin 2) (ZMod q)) (fixedSubmodule (FLT.SmoothVectors.gl2CongruenceSubgroup q 1) V) :=
  (Units.coeHom (Module.End ℂ (fixedSubmodule (FLT.SmoothVectors.gl2CongruenceSubgroup q 1) V))).comp
    ((gl2ReductionHom q).liftOfSurjective (gl2ReductionHom_surjective q)
      ⟨MonoidHom.toHomUnits (fixedRepK0 q V), fun k hk => by
        rw [MonoidHom.mem_ker, ← Units.val_eq_one, MonoidHom.coe_toHomUnits]
        exact fixedRepK0_eq_one_of_mem_ker q V k hk⟩)

theorem gl2ReductionRep_gl2ReductionHom_apply (k : ↥(FLT.SmoothVectors.gl2CongruenceSubgroup q 0))
    (v : fixedSubmodule (FLT.SmoothVectors.gl2CongruenceSubgroup q 1) V) :
    ((gl2ReductionRep q V (gl2ReductionHom q k) v :
        fixedSubmodule (FLT.SmoothVectors.gl2CongruenceSubgroup q 1) V) : V) = (k : GL (Fin 2) ℚ_[q]) • (v : V) := by
  rw [← fixedRepK0_apply_coe]
  congr 1
  simp only [gl2ReductionRep, MonoidHom.comp_apply, MonoidHom.liftOfSurjective,
    MonoidHom.liftOfRightInverse_comp_apply, Units.coeHom_apply, MonoidHom.coe_toHomUnits]

variable {V}
variable {W : Type*} [AddCommGroup W] [Module ℂ W] [DistribMulAction (GL (Fin 2) ℚ_[q]) W]
  [SMulCommClass (GL (Fin 2) ℚ_[q]) ℂ W]

def gl2ReductionMap (f : V →ₗ[ℂ] W) (hf : ∀ (x : GL (Fin 2) ℚ_[q]) (v : V), f (x • v) = x • f v) :
    fixedSubmodule (FLT.SmoothVectors.gl2CongruenceSubgroup q 1) V →ₗ[ℂ]
      fixedSubmodule (FLT.SmoothVectors.gl2CongruenceSubgroup q 1) W :=
  f.restrict fun v hv => by
    rw [mem_fixedSubmodule_iff] at hv ⊢
    intro m hm
    rw [← hf m v, hv m hm]

theorem coe_gl2ReductionMap_apply (f : V →ₗ[ℂ] W) (hf : ∀ (x : GL (Fin 2) ℚ_[q]) (v : V), f (x • v) = x • f v)
    (v : fixedSubmodule (FLT.SmoothVectors.gl2CongruenceSubgroup q 1) V) :
    ((gl2ReductionMap q f hf v : fixedSubmodule (FLT.SmoothVectors.gl2CongruenceSubgroup q 1) W) : W) = f v :=
  rfl

theorem gl2ReductionMap_comm (f : V →ₗ[ℂ] W) (hf : ∀ (x : GL (Fin 2) ℚ_[q]) (v : V), f (x • v) = x • f v)
    (x : GL (Fin 2) (ZMod q)) (v : fixedSubmodule (FLT.SmoothVectors.gl2CongruenceSubgroup q 1) V) :
    gl2ReductionMap q f hf (gl2ReductionRep q V x v) = gl2ReductionRep q W x (gl2ReductionMap q f hf v) := by
  obtain ⟨k, rfl⟩ := gl2ReductionHom_surjective q x
  apply Subtype.ext
  rw [coe_gl2ReductionMap_apply, gl2ReductionRep_gl2ReductionHom_apply, gl2ReductionRep_gl2ReductionHom_apply,
    coe_gl2ReductionMap_apply]
  exact hf _ _

end Reduction

end LocalNewvector

end


