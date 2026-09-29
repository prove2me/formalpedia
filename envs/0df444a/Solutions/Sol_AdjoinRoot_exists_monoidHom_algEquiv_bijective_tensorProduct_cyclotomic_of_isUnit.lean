-- Prove2me | solution 1 for AdjoinRoot.exists_monoidHom_algEquiv_bijective_tensorProduct_cyclotomic_of_isUnit
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:01.734404+00:00
-- url     : https://prove2.me/submissions/53afec4d-98d3-549b-bf37-d825058a3817

import Mathlib
import Theorems.Thm_AdjoinRoot_isUnit_one_sub_root_pow_of_isUnit_of_not_dvd
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AdjoinRoot_exists_monoidHom_algEquiv_bijective_tensorProduct_cyclotomic_of_isUnit

set_option autoImplicit false

open Polynomial TensorProduct

universe u

namespace CycSplit29

abbrev S0 (m : ℕ) : Type := AdjoinRoot (cyclotomic m ℤ)

theorem isDomain_S0 (m : ℕ) (hm : 0 < m) : IsDomain (S0 m) :=
  AdjoinRoot.isDomain_of_prime (cyclotomic.irreducible hm).prime

theorem natCast_ne_zero_S0 (m : ℕ) (hm : 0 < m) (n : ℕ) (hn : n ≠ 0) : ((n : ℕ) : S0 m) ≠ 0 := by
  intro h
  have h' : AdjoinRoot.mk (cyclotomic m ℤ) (C (n : ℤ)) = 0 := by
    rw [← map_natCast (AdjoinRoot.of (cyclotomic m ℤ)) n] at h
    rw [← h, AdjoinRoot.mk_C]
  rw [AdjoinRoot.mk_eq_zero] at h'
  have hdeg := Polynomial.natDegree_le_of_dvd h' (by simp [hn])
  rw [natDegree_C, natDegree_cyclotomic] at hdeg
  exact absurd hdeg (not_le.mpr (Nat.totient_pos.mpr hm))

theorem isPrimitiveRoot_S0 (m : ℕ) (hm : 0 < m) : IsPrimitiveRoot (AdjoinRoot.root (cyclotomic m ℤ)) m := by
  haveI := isDomain_S0 m hm
  haveI : NeZero ((m : ℕ) : S0 m) := ⟨natCast_ne_zero_S0 m hm m hm.ne'⟩
  refine (isRoot_cyclotomic_iff (R := S0 m)).mp ?_
  have := AdjoinRoot.isRoot_root (cyclotomic m ℤ)
  rwa [map_cyclotomic] at this

theorem cyclotomic_eq_prod_S0 (m : ℕ) [NeZero m] :
    cyclotomic m (S0 m) = ∏ a : (ZMod m)ˣ, (X - C (AdjoinRoot.root (cyclotomic m ℤ) ^ (a : ZMod m).val)) := by
  classical
  have hm : 0 < m := Nat.pos_of_ne_zero (NeZero.ne m)
  haveI := isDomain_S0 m hm
  have hζ := isPrimitiveRoot_S0 m hm
  set ζ := AdjoinRoot.root (cyclotomic m ℤ) with hζdef
  rw [cyclotomic_eq_prod_X_sub_primitiveRoots hζ]

  have himage : primitiveRoots m (S0 m) =
      Finset.image (fun a : (ZMod m)ˣ => ζ ^ (a : ZMod m).val) Finset.univ := by
    ext μ
    rw [mem_primitiveRoots hm, Finset.mem_image]
    constructor
    · intro hμ
      obtain ⟨i, hi, rfl⟩ := hζ.eq_pow_of_pow_eq_one hμ.pow_eq_one
      have hcop : i.Coprime m := (hζ.pow_iff_coprime hm i).mp hμ
      refine ⟨ZMod.unitOfCoprime i hcop, Finset.mem_univ _, ?_⟩
      rw [ZMod.coe_unitOfCoprime, ZMod.val_natCast, Nat.mod_eq_of_lt hi]
    · rintro ⟨a, -, rfl⟩
      exact hζ.pow_of_coprime _ (ZMod.val_coe_unit_coprime a)
  have hinj : Set.InjOn (fun a : (ZMod m)ˣ => ζ ^ (a : ZMod m).val) (Finset.univ : Finset (ZMod m)ˣ) := by
    intro a _ b _ hab
    have := hζ.pow_inj (ZMod.val_lt _) (ZMod.val_lt _) hab
    exact Units.ext (ZMod.val_injective m this)
  rw [himage, Finset.prod_image hinj]

variable {𝒪 : Type u} [CommRing 𝒪]

local notation "𝒪'" => AdjoinRoot (cyclotomic _ 𝒪)

noncomputable def φ (m : ℕ) : S0 m →+* AdjoinRoot (cyclotomic m 𝒪) :=
  AdjoinRoot.lift (Int.castRingHom _) (AdjoinRoot.root (cyclotomic m 𝒪)) (by
    rw [eval₂_eq_eval_map, map_cyclotomic, ← map_cyclotomic m (algebraMap 𝒪 (AdjoinRoot (cyclotomic m 𝒪))), eval_map,
      ← aeval_def, AdjoinRoot.aeval_eq, AdjoinRoot.mk_self])

theorem φ_root (m : ℕ) : φ (𝒪 := 𝒪) m (AdjoinRoot.root (cyclotomic m ℤ)) = AdjoinRoot.root (cyclotomic m 𝒪) :=
  AdjoinRoot.lift_root _

theorem root_pow_eq_one (m : ℕ) : AdjoinRoot.root (cyclotomic m 𝒪) ^ m = 1 := by
  have h : AdjoinRoot.mk (cyclotomic m 𝒪) (X ^ m - 1) = 0 :=
    AdjoinRoot.mk_eq_zero.mpr (cyclotomic.dvd_X_pow_sub_one m 𝒪)
  rwa [map_sub, map_pow, AdjoinRoot.mk_X, map_one, sub_eq_zero] at h

theorem cyclotomic_eq_prod (m : ℕ) [NeZero m] :
    cyclotomic m (AdjoinRoot (cyclotomic m 𝒪)) =
      ∏ a : (ZMod m)ˣ, (X - C (AdjoinRoot.root (cyclotomic m 𝒪) ^ (a : ZMod m).val)) := by
  have h := congrArg (Polynomial.map (φ (𝒪 := 𝒪) m)) (cyclotomic_eq_prod_S0 m)
  rw [map_cyclotomic, Polynomial.map_prod] at h
  rw [h]
  refine Finset.prod_congr rfl fun a _ => ?_
  rw [Polynomial.map_sub, Polynomial.map_X, Polynomial.map_C, map_pow, φ_root]

theorem aeval_root_pow (m : ℕ) [NeZero m] (a : (ZMod m)ˣ) :
    aeval (AdjoinRoot.root (cyclotomic m 𝒪) ^ (a : ZMod m).val) (cyclotomic m 𝒪) = 0 := by
  classical
  rw [aeval_def, ← eval_map, map_cyclotomic, cyclotomic_eq_prod (𝒪 := 𝒪) m, eval_prod]
  exact Finset.prod_eq_zero (Finset.mem_univ a) (by rw [eval_sub, eval_X, eval_C, sub_self])

end CycSplit29

namespace CycSplit29

variable {𝒪 : Type u} [CommRing 𝒪]

theorem root_pow_mod (m n : ℕ) :
    AdjoinRoot.root (cyclotomic m 𝒪) ^ (n % m) = AdjoinRoot.root (cyclotomic m 𝒪) ^ n := by
  conv_rhs => rw [← Nat.mod_add_div n m, pow_add, pow_mul, root_pow_eq_one, one_pow, mul_one]

noncomputable def σ (m : ℕ) [NeZero m] (a : (ZMod m)ˣ) :
    AdjoinRoot (cyclotomic m 𝒪) →ₐ[𝒪] AdjoinRoot (cyclotomic m 𝒪) :=
  AdjoinRoot.liftAlgHom (cyclotomic m 𝒪) (Algebra.ofId 𝒪 _) (AdjoinRoot.root (cyclotomic m 𝒪) ^ (a : ZMod m).val) (by
    have := aeval_root_pow (𝒪 := 𝒪) m a
    rwa [aeval_def, ← eval_map, eval_map] at this)

theorem σ_root (m : ℕ) [NeZero m] (a : (ZMod m)ˣ) :
    σ (𝒪 := 𝒪) m a (AdjoinRoot.root (cyclotomic m 𝒪)) = AdjoinRoot.root (cyclotomic m 𝒪) ^ (a : ZMod m).val :=
  AdjoinRoot.liftAlgHom_root _ _ _ _

theorem σ_mul (m : ℕ) [NeZero m] (a b : (ZMod m)ˣ) :
    σ (𝒪 := 𝒪) m (a * b) = (σ m a).comp (σ m b) := by
  apply AdjoinRoot.algHom_ext
  rw [σ_root, AlgHom.comp_apply, σ_root, map_pow, σ_root, ← pow_mul, Units.val_mul, ZMod.val_mul,
    root_pow_mod]

theorem σ_one (m : ℕ) [NeZero m] : σ (𝒪 := 𝒪) m 1 = AlgHom.id 𝒪 _ := by
  apply AdjoinRoot.algHom_ext
  rw [σ_root, AlgHom.id_apply, Units.val_one, ZMod.val_one_eq_one_mod, root_pow_mod, pow_one]

noncomputable def τ (m : ℕ) [NeZero m] (a : (ZMod m)ˣ) :
    AdjoinRoot (cyclotomic m 𝒪) ≃ₐ[𝒪] AdjoinRoot (cyclotomic m 𝒪) :=
  AlgEquiv.ofAlgHom (σ m a) (σ m a⁻¹) (by rw [← σ_mul, mul_inv_cancel, σ_one]) (by rw [← σ_mul, inv_mul_cancel, σ_one])

theorem τ_apply (m : ℕ) [NeZero m] (a : (ZMod m)ˣ) (y : AdjoinRoot (cyclotomic m 𝒪)) : τ m a y = σ m a y := rfl

noncomputable def τHom (m : ℕ) [NeZero m] :
    (ZMod m)ˣ →* (AdjoinRoot (cyclotomic m 𝒪) ≃ₐ[𝒪] AdjoinRoot (cyclotomic m 𝒪)) where
  toFun := τ m
  map_one' := by
    apply AlgEquiv.ext; intro y
    rw [τ_apply, σ_one]; rfl
  map_mul' a b := by
    apply AlgEquiv.ext; intro y
    show τ m (a * b) y = τ m a (τ m b y)
    rw [τ_apply, τ_apply, τ_apply, σ_mul]; rfl

theorem τHom_apply (m : ℕ) [NeZero m] (a : (ZMod m)ˣ) (y : AdjoinRoot (cyclotomic m 𝒪)) :
    τHom (𝒪 := 𝒪) m a y = σ m a y := rfl

theorem isUnit_root_pow_sub (m : ℕ) [NeZero m] (hm : IsUnit ((m : ℕ) : 𝒪)) (a b : (ZMod m)ˣ) (hab : a ≠ b) :
    IsUnit (AdjoinRoot.root (cyclotomic m 𝒪) ^ (b : ZMod m).val - AdjoinRoot.root (cyclotomic m 𝒪) ^ (a : ZMod m).val) := by
  set x := AdjoinRoot.root (cyclotomic m 𝒪) with hx
  have hxu : IsUnit x := IsUnit.of_pow_eq_one (root_pow_eq_one m) (NeZero.ne m)
  have hne : (a : ZMod m).val ≠ (b : ZMod m).val := fun h =>
    hab (Units.ext (ZMod.val_injective m h))
  have hlt_a := ZMod.val_lt (a : ZMod m)
  have hlt_b := ZMod.val_lt (b : ZMod m)
  rcases Nat.lt_or_gt_of_ne hne with h | h
  ·
    have hnd : ¬ m ∣ ((b : ZMod m).val - (a : ZMod m).val) := fun hd =>
      absurd (Nat.le_of_dvd (by omega) hd) (by omega)
    have hu := AdjoinRoot.isUnit_one_sub_root_pow_of_isUnit_of_not_dvd 𝒪 m hm _ hnd
    have : x ^ (b : ZMod m).val - x ^ (a : ZMod m).val = -(x ^ (a : ZMod m).val * (1 - x ^ ((b : ZMod m).val - (a : ZMod m).val))) := by
      rw [mul_sub, mul_one, ← pow_add, Nat.add_sub_cancel' h.le]; ring
    rw [this]
    exact ((hxu.pow _).mul hu).neg
  · have hnd : ¬ m ∣ ((a : ZMod m).val - (b : ZMod m).val) := fun hd =>
      absurd (Nat.le_of_dvd (by omega) hd) (by omega)
    have hu := AdjoinRoot.isUnit_one_sub_root_pow_of_isUnit_of_not_dvd 𝒪 m hm _ hnd
    have : x ^ (b : ZMod m).val - x ^ (a : ZMod m).val = x ^ (b : ZMod m).val * (1 - x ^ ((a : ZMod m).val - (b : ZMod m).val)) := by
      rw [mul_sub, mul_one, ← pow_add, Nat.add_sub_cancel' h.le]
    rw [this]
    exact (hxu.pow _).mul hu

noncomputable def Ψ (m : ℕ) [NeZero m] :
    AdjoinRoot (cyclotomic m 𝒪) ⊗[𝒪] AdjoinRoot (cyclotomic m 𝒪) →ₗ[AdjoinRoot (cyclotomic m 𝒪)]
      ((ZMod m)ˣ → AdjoinRoot (cyclotomic m 𝒪)) :=
  TensorProduct.AlgebraTensorModule.lift
    { toFun := fun s =>
        { toFun := fun t => fun a => s * σ m a t
          map_add' := fun t t' => by ext a; simp [mul_add]
          map_smul' := fun c t => by
            funext a
            show s * σ m a (c • t) = (c • fun a => s * σ m a t) a
            rw [Pi.smul_apply, map_smul, Algebra.smul_def, Algebra.smul_def, mul_left_comm] }
      map_add' := fun s s' => by ext t a; simp [add_mul]
      map_smul' := fun c s => by ext t a; simp [mul_assoc] }

theorem Ψ_tmul (m : ℕ) [NeZero m] (s t : AdjoinRoot (cyclotomic m 𝒪)) (a : (ZMod m)ˣ) :
    Ψ (𝒪 := 𝒪) m (s ⊗ₜ t) a = s * σ m a t := rfl

theorem Ψ_eq (m : ℕ) [NeZero m] (z : AdjoinRoot (cyclotomic m 𝒪) ⊗[𝒪] AdjoinRoot (cyclotomic m 𝒪)) (a : (ZMod m)ˣ) :
    Ψ (𝒪 := 𝒪) m z a =
      Algebra.TensorProduct.lmul' (S := AdjoinRoot (cyclotomic m 𝒪)) 𝒪
        (Algebra.TensorProduct.map (AlgHom.id 𝒪 _) ((τHom (𝒪 := 𝒪) m a : _ ≃ₐ[𝒪] _) : _ →ₐ[𝒪] _) z) := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul s t =>
    rw [Ψ_tmul, Algebra.TensorProduct.map_tmul, Algebra.TensorProduct.lmul'_apply_tmul, AlgHom.id_apply]
    rfl
  | add z w hz hw => rw [map_add, Pi.add_apply, hz, hw, map_add, map_add]

theorem Ψ_bijective (m : ℕ) [NeZero m] (hm : IsUnit ((m : ℕ) : 𝒪)) : Function.Bijective (Ψ (𝒪 := 𝒪) m) := by
  classical
  set 𝒪' := AdjoinRoot (cyclotomic m 𝒪) with h𝒪'
  rcases subsingleton_or_nontrivial 𝒪 with h𝒪 | h𝒪
  · haveI : Subsingleton 𝒪' := (algebraMap 𝒪 𝒪').codomain_trivial
    haveI : Subsingleton (𝒪' ⊗[𝒪] 𝒪') := by
      refine ⟨fun z w => ?_⟩
      rw [← one_smul 𝒪' z, ← one_smul 𝒪' w, Subsingleton.elim (1 : 𝒪') 0, zero_smul, zero_smul]
    exact ⟨fun _ _ _ => Subsingleton.elim _ _, fun y => ⟨0, Subsingleton.elim _ _⟩⟩
  haveI : Nontrivial 𝒪' := by
    have hmon := cyclotomic.monic m 𝒪
    let B := AdjoinRoot.powerBasis' (R := 𝒪) hmon
    have hpos : 0 < B.dim := by
      rw [AdjoinRoot.powerBasis'_dim, natDegree_cyclotomic]; exact Nat.totient_pos.mpr (Nat.pos_of_ne_zero (NeZero.ne m))
    exact nontrivial_of_ne (B.basis ⟨0, hpos⟩) 0 (B.basis.ne_zero _)

  have hmon := cyclotomic.monic m 𝒪
  let B := AdjoinRoot.powerBasis' (R := 𝒪) hmon
  have hdim : B.dim = Fintype.card (ZMod m)ˣ := by
    rw [AdjoinRoot.powerBasis'_dim, natDegree_cyclotomic, ZMod.card_units_eq_totient]
  let e : (ZMod m)ˣ ≃ Fin B.dim := (Fintype.equivFin _).trans (finCongr hdim.symm)
  let bS : Module.Basis (Fin B.dim) 𝒪' (𝒪' ⊗[𝒪] 𝒪') := Algebra.TensorProduct.basis 𝒪' B.basis
  let bT : Module.Basis (Fin B.dim) 𝒪' ((ZMod m)ˣ → 𝒪') := (Pi.basisFun 𝒪' (ZMod m)ˣ).reindex e
  let v : Fin B.dim → 𝒪' := fun i => AdjoinRoot.root (cyclotomic m 𝒪) ^ ((e.symm i : (ZMod m)ˣ) : ZMod m).val
  have hmat : LinearMap.toMatrix bS bT (Ψ m) = Matrix.vandermonde v := by
    ext i j
    rw [LinearMap.toMatrix_apply, Matrix.vandermonde_apply]
    have hbS : bS j = (1 : 𝒪') ⊗ₜ (AdjoinRoot.root (cyclotomic m 𝒪) ^ (j : ℕ)) := by
      rw [show bS j = Algebra.TensorProduct.basis 𝒪' B.basis j from rfl, Algebra.TensorProduct.basis_apply,
        B.basis_eq_pow, AdjoinRoot.powerBasis'_gen]
    rw [hbS]
    rw [show bT = (Pi.basisFun 𝒪' (ZMod m)ˣ).reindex e from rfl, Module.Basis.repr_reindex, Finsupp.mapDomain_equiv_apply,
      Pi.basisFun_repr, Ψ_tmul, one_mul, map_pow, σ_root, ← pow_mul, mul_comm, pow_mul]
  have hdet : IsUnit (LinearMap.toMatrix bS bT (Ψ m)).det := by
    rw [hmat, Matrix.det_vandermonde]
    refine IsUnit.prod_iff.mpr fun i _ => IsUnit.prod_iff.mpr fun j hj => ?_
    have hij : e.symm i ≠ e.symm j := fun h => by
      have := e.symm.injective h
      rw [Finset.mem_Ioi] at hj
      exact absurd hj (this ▸ lt_irrefl _)
    exact isUnit_root_pow_sub m hm (e.symm i) (e.symm j) hij
  exact (LinearEquiv.ofIsUnitDet hdet).bijective

end CycSplit29

open CycSplit29 in
theorem solution
    (𝒪 : Type u) [CommRing 𝒪] (m : ℕ) (hm : IsUnit ((m : ℕ) : 𝒪)) :
    ∃ τ : (ZMod m)ˣ →* (AdjoinRoot (cyclotomic m 𝒪) ≃ₐ[𝒪] AdjoinRoot (cyclotomic m 𝒪)),
      (∀ a : (ZMod m)ˣ, τ a (AdjoinRoot.root (cyclotomic m 𝒪)) = AdjoinRoot.root (cyclotomic m 𝒪) ^ (a : ZMod m).val) ∧
      Function.Bijective fun x : AdjoinRoot (cyclotomic m 𝒪) ⊗[𝒪] AdjoinRoot (cyclotomic m 𝒪) => fun σ : (ZMod m)ˣ =>
        Algebra.TensorProduct.lmul' (S := AdjoinRoot (cyclotomic m 𝒪)) 𝒪
          (Algebra.TensorProduct.map (AlgHom.id 𝒪 (AdjoinRoot (cyclotomic m 𝒪)))
            ((τ σ : AdjoinRoot (cyclotomic m 𝒪) ≃ₐ[𝒪] AdjoinRoot (cyclotomic m 𝒪)) :
              AdjoinRoot (cyclotomic m 𝒪) →ₐ[𝒪] AdjoinRoot (cyclotomic m 𝒪)) x) := by
  classical
  by_cases hm0 : m = 0
  ·
    subst hm0
    haveI : Subsingleton 𝒪 := by
      rw [Nat.cast_zero] at hm
      exact subsingleton_of_zero_eq_one (isUnit_zero_iff.mp hm)
    haveI : Subsingleton (AdjoinRoot (cyclotomic 0 𝒪)) := (algebraMap 𝒪 (AdjoinRoot (cyclotomic 0 𝒪))).codomain_trivial
    haveI : Subsingleton (AdjoinRoot (cyclotomic 0 𝒪) ⊗[𝒪] AdjoinRoot (cyclotomic 0 𝒪)) := by
      refine ⟨fun z w => ?_⟩
      rw [← one_smul (AdjoinRoot (cyclotomic 0 𝒪)) z, ← one_smul (AdjoinRoot (cyclotomic 0 𝒪)) w,
        Subsingleton.elim (1 : AdjoinRoot (cyclotomic 0 𝒪)) 0, zero_smul, zero_smul]
    exact ⟨1, fun a => Subsingleton.elim _ _, fun _ _ _ => Subsingleton.elim _ _, fun y => ⟨0, Subsingleton.elim _ _⟩⟩
  haveI : NeZero m := ⟨hm0⟩
  refine ⟨τHom m, fun a => by rw [τHom_apply, σ_root], ?_⟩
  have hfun : (fun x : AdjoinRoot (cyclotomic m 𝒪) ⊗[𝒪] AdjoinRoot (cyclotomic m 𝒪) => fun σ : (ZMod m)ˣ =>
        Algebra.TensorProduct.lmul' (S := AdjoinRoot (cyclotomic m 𝒪)) 𝒪
          (Algebra.TensorProduct.map (AlgHom.id 𝒪 (AdjoinRoot (cyclotomic m 𝒪)))
            ((τHom (𝒪 := 𝒪) m σ : AdjoinRoot (cyclotomic m 𝒪) ≃ₐ[𝒪] AdjoinRoot (cyclotomic m 𝒪)) :
              AdjoinRoot (cyclotomic m 𝒪) →ₐ[𝒪] AdjoinRoot (cyclotomic m 𝒪)) x)) = ⇑(Ψ (𝒪 := 𝒪) m) := by
    funext z a
    exact (Ψ_eq m z a).symm
  rw [hfun]
  exact Ψ_bijective m hm

end S_AdjoinRoot_exists_monoidHom_algEquiv_bijective_tensorProduct_cyclotomic_of_isUnit
end P2MW
export P2MW.S_AdjoinRoot_exists_monoidHom_algEquiv_bijective_tensorProduct_cyclotomic_of_isUnit (solution)
