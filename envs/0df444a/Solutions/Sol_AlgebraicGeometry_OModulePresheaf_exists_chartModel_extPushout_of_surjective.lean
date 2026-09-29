-- Prove2me | solution 1 for AlgebraicGeometry.OModulePresheaf.exists_chartModel_extPushout_of_surjective
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:02.935278+00:00
-- url     : https://prove2.me/submissions/358ff19c-fef8-5355-8ccf-04c262167d80

import Mathlib
import Definitions.Def_AlgebraicGeometry_OModulePresheafHom
import Definitions.Def_LinearMap_ExtPushout
import Theorems.Thm_AlgebraicGeometry_OModulePresheaf_IsQuasicoherent_exists_linearEquiv_tensorProduct_apply_one_tmul_eq_res
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_chartModel_extPushout_of_surjective

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry TopologicalSpace

universe u

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace X1bSol

namespace EP

open LinearMap

variable {B : Type u} [CommRing B] {B₂ : Type u} [CommRing B₂] {σ : B →+* B₂}
  {M : Type u} {N : Type u} [AddCommGroup M] [Module B M] [AddCommGroup N] [Module B N] {r : ℕ}
  (p : (Fin r → B) →ₗ[B] M) (δ : ↥(ker p) →ₗ[B] N)
  {Q : Type u} [AddCommGroup Q] [Module B₂ Q]

noncomputable def slift (f : N →ₛₗ[σ] Q) (g : (Fin r → B) →ₛₗ[σ] Q) (h : ∀ s : ↥(ker p), f (δ s) = g s) :
    ExtPushout p δ →ₛₗ[σ] Q :=
  (extPushoutRel p δ).liftQ (f.comp (LinearMap.fst B N (Fin r → B)) + g.comp (LinearMap.snd B N (Fin r → B))) (by
    rintro x ⟨s, rfl⟩
    rw [LinearMap.mem_ker, LinearMap.add_apply, LinearMap.comp_apply, LinearMap.comp_apply]
    show f (δ s) + g (-(s : Fin r → B)) = 0
    rw [map_neg, h, add_neg_cancel])

theorem slift_mk (f : N →ₛₗ[σ] Q) (g : (Fin r → B) →ₛₗ[σ] Q) (h : ∀ s : ↥(ker p), f (δ s) = g s) (n : N) (v : Fin r → B) :
    slift p δ f g h (ExtPushout.mk p δ (n, v)) = f n + g v := rfl

theorem slift_inl (f : N →ₛₗ[σ] Q) (g : (Fin r → B) →ₛₗ[σ] Q) (h : ∀ s : ↥(ker p), f (δ s) = g s) (n : N) :
    slift p δ f g h (ExtPushout.inl p δ n) = f n := by
  rw [ExtPushout.inl_apply, slift_mk, map_zero, add_zero]

theorem slift_inr (f : N →ₛₗ[σ] Q) (g : (Fin r → B) →ₛₗ[σ] Q) (h : ∀ s : ↥(ker p), f (δ s) = g s) (v : Fin r → B) :
    slift p δ f g h (ExtPushout.inr p δ v) = g v := by
  rw [ExtPushout.inr_apply, slift_mk, map_zero, zero_add]

theorem ind {C : ExtPushout p δ → Prop} (x : ExtPushout p δ) (h : ∀ (n : N) (v : Fin r → B), C (ExtPushout.inl p δ n + ExtPushout.inr p δ v)) :
    C x := by
  obtain ⟨⟨n, v⟩, rfl⟩ := ExtPushout.mk_surjective p δ x
  rw [ExtPushout.mk_eq_inl_add_inr]
  exact h n v

theorem fun_ext {Q' : Type u} [AddCommGroup Q'] {φ ψ : ExtPushout p δ →+ Q'}
    (h₁ : ∀ n : N, φ (ExtPushout.inl p δ n) = ψ (ExtPushout.inl p δ n))
    (h₂ : ∀ v : Fin r → B, φ (ExtPushout.inr p δ v) = ψ (ExtPushout.inr p δ v)) (x : ExtPushout p δ) : φ x = ψ x := by
  refine ind p δ (C := fun y => φ y = ψ y) x fun n v => ?_
  show φ (_ + _) = ψ (_ + _)
  rw [map_add, map_add, h₁, h₂]

end EP

namespace BC

variable {R : Type u} [CommRing R] {S : Type u} [CommRing S] [Algebra R S]

noncomputable abbrev φ (R S : Type u) [CommRing R] [CommRing S] [Algebra R S] (n : ℕ) :
    (Fin n → R) →ₗ[R] (Fin n → S) :=
  (Algebra.linearMap R S).compLeft (Fin n)

theorem φ_apply (n : ℕ) (v : Fin n → R) (i : Fin n) : φ R S n v i = algebraMap R S (v i) := rfl

theorem isBaseChange_φ (n : ℕ) : IsBaseChange S (φ R S n) :=
  IsBaseChange.finitePow (Fin n) (IsBaseChange.linearMap R S)

theorem mem_span_of_isBaseChange {M N : Type*} [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    [Module S N] [IsScalarTower R S N] {f : M →ₗ[R] N} (hf : IsBaseChange S f) (y : N) :
    y ∈ Submodule.span S (Set.range f) := by
  induction y using hf.inductionOn with
  | zero => exact Submodule.zero_mem _
  | tmul m => exact Submodule.subset_span ⟨m, rfl⟩
  | smul s n hn => exact Submodule.smul_mem _ s hn
  | add n₁ n₂ h₁ h₂ => exact Submodule.add_mem _ h₁ h₂

variable {M : Type u} [AddCommGroup M] [Module R M] {M' : Type u} [AddCommGroup M'] [Module R M'] [Module S M'] [IsScalarTower R S M']
  (μ : M →ₗ[R] M') {r : ℕ} (p : (Fin r → R) →ₗ[R] M)

variable (S) in

@[irreducible] noncomputable def bc : (Fin r → S) →ₗ[S] M' :=
  ∑ i : Fin r, (LinearMap.proj i : (Fin r → S) →ₗ[S] S).smulRight (μ (p (Pi.single i 1)))

theorem bc_apply (v : Fin r → S) : bc S μ p v = ∑ i, v i • μ (p (Pi.single i 1)) := by
  simp only [bc, LinearMap.sum_apply, LinearMap.smulRight_apply, LinearMap.proj_apply]

theorem bc_φ (v : Fin r → R) : bc S μ p (φ R S r v) = μ (p v) := by
  rw [bc_apply]
  conv_rhs => rw [show v = ∑ i, v i • (Pi.single i 1 : Fin r → R) from by
    ext j; simp [Finset.sum_apply, Pi.single_apply]]
  rw [map_sum, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_smul, map_smul, φ_apply, algebraMap_smul]

theorem bc_algebraMap (v : Fin r → R) : bc S μ p (fun i => algebraMap R S (v i)) = μ (p v) := bc_φ μ p v

variable (p' : (Fin r → S) →ₗ[S] M') (hp' : ∀ v : Fin r → R, p' (φ R S r v) = μ (p v))

include hp' in
theorem surjective_of_isBaseChange (hμ : IsBaseChange S μ) (hp : Function.Surjective p) : Function.Surjective p' := by
  rw [← LinearMap.range_eq_top, eq_top_iff]
  intro y _
  have hy := mem_span_of_isBaseChange hμ y
  refine Submodule.span_le.mpr ?_ hy
  rintro _ ⟨n, rfl⟩
  obtain ⟨m, rfl⟩ := hp n
  exact ⟨φ R S r m, hp' m⟩

noncomputable def g : ↥(LinearMap.ker p) →ₗ[R] ↥(LinearMap.ker p') :=
  LinearMap.codRestrict ((LinearMap.ker p').restrictScalars R) ((φ R S r) ∘ₗ (LinearMap.ker p).subtype)
    (fun s => by
      show p' (φ R S r s) = 0
      rw [hp', (LinearMap.mem_ker).mp s.2, map_zero])

theorem g_coe (s : ↥(LinearMap.ker p)) : ((g μ p p' hp' s : ↥(LinearMap.ker p')) : Fin r → S) = φ R S r s := rfl

theorem g_coe_apply (s : ↥(LinearMap.ker p)) (i : Fin r) :
    ((g μ p p' hp' s : ↥(LinearMap.ker p')) : Fin r → S) i = algebraMap R S ((s : Fin r → R) i) := rfl

theorem isBaseChange_g [Module.Flat R S] (hμ : IsBaseChange S μ) : IsBaseChange S (g μ p p' hp') := by
  refine IsBaseChange.of_left_exact S (g μ p p' hp') (φ R S r) μ (f := (LinearMap.ker p).subtype) (g := p)
    (f' := (LinearMap.ker p').subtype) (g' := p') ?_ ?_ (isBaseChange_φ r) hμ ?_ ?_ ?_ ?_
  · exact LinearMap.ext fun s => rfl
  · exact LinearMap.ext fun v => (hp' v).symm
  · exact LinearMap.exact_subtype_ker_map p
  · exact Subtype.val_injective
  · exact LinearMap.exact_subtype_ker_map p'
  · exact Subtype.val_injective

theorem span_range_g_eq_top [Module.Flat R S] (hμ : IsBaseChange S μ) :
    Submodule.span S (Set.range (g μ p p' hp')) = ⊤ := by
  rw [eq_top_iff]
  intro y _
  exact mem_span_of_isBaseChange (isBaseChange_g μ p p' hp' hμ) y

theorem span_range_g [Module.Flat R S] (hμ : IsBaseChange S μ) :
    Submodule.span S (Set.range fun s : ↥(LinearMap.ker p) => ((g μ p p' hp' s : ↥(LinearMap.ker p')) : Fin r → S)) =
      LinearMap.ker p' := by
  have h := congrArg (Submodule.map (LinearMap.ker p').subtype) (span_range_g_eq_top μ p p' hp' hμ)
  rw [Submodule.map_span, Submodule.map_top, Submodule.range_subtype, ← Set.range_comp] at h
  exact h

theorem ext_on_g [Module.Flat R S] (hμ : IsBaseChange S μ) {T : Type u} [CommRing T] {τ : S →+* T} {Q : Type u} [AddCommGroup Q] [Module T Q]
    (f₁ f₂ : ↥(LinearMap.ker p') →ₛₗ[τ] Q) (h : ∀ s : ↥(LinearMap.ker p), f₁ (g μ p p' hp' s) = f₂ (g μ p p' hp' s)) : f₁ = f₂ :=
  LinearMap.ext_on_range (span_range_g_eq_top μ p p' hp' hμ) h

omit μ p p' hp' in

theorem ext_of_span_eq {F : Type u} [AddCommGroup F] [Module S F] (K : Submodule S F) {ι : Type u} (gen : ι → ↥K)
    (hspan : Submodule.span S (Set.range fun i => (gen i : F)) = K) {T : Type u} [CommRing T] {τ : S →+* T}
    {Q : Type u} [AddCommGroup Q] [Module T Q] (f₁ f₂ : ↥K →ₛₗ[τ] Q) (h : ∀ i, f₁ (gen i) = f₂ (gen i)) : f₁ = f₂ := by
  refine LinearMap.ext_on_range (v := gen) ?_ h
  apply Submodule.map_injective_of_injective K.injective_subtype
  rw [Submodule.map_span, Submodule.map_top, Submodule.range_subtype, ← Set.range_comp]
  exact hspan

variable {N : Type u} [AddCommGroup N] [Module R N] {N' : Type u} [AddCommGroup N'] [Module R N'] [Module S N'] [IsScalarTower R S N']
  (ν : N →ₗ[R] N')

noncomputable def δ' [Module.Flat R S] (hμ : IsBaseChange S μ) (δ : ↥(LinearMap.ker p) →ₗ[R] N) : ↥(LinearMap.ker p') →ₗ[S] N' :=
  IsBaseChange.linearMapLeftRightHom (isBaseChange_g μ p p' hp' hμ) ν δ

theorem δ'_g [Module.Flat R S] (hμ : IsBaseChange S μ) (δ : ↥(LinearMap.ker p) →ₗ[R] N) (s : ↥(LinearMap.ker p)) :
    δ' μ p p' hp' ν hμ δ (g μ p p' hp' s) = ν (δ s) :=
  IsBaseChange.linearMapLeftRightHom_comp_apply _ ν δ s

end BC

namespace EP

open LinearMap

section resMap

variable {B' : Type u} [CommRing B'] {B'' : Type u} [CommRing B''] (σ : B' →+* B'')

def coordMap (r : ℕ) : (Fin r → B') →ₛₗ[σ] (Fin r → B'') where
  toFun v m := σ (v m)
  map_add' v w := by ext m; exact map_add σ (v m) (w m)
  map_smul' a v := by ext m; exact map_mul σ a (v m)

theorem coordMap_apply (r : ℕ) (v : Fin r → B') (m : Fin r) : coordMap σ r v m = σ (v m) := rfl

variable {N' : Type u} [AddCommGroup N'] [Module B' N'] {N'' : Type u} [AddCommGroup N''] [Module B'' N'']
  (νσ : N' →ₛₗ[σ] N'')
  {M' : Type u} [AddCommGroup M'] [Module B' M'] {M'' : Type u} [AddCommGroup M''] [Module B'' M'']
  (μσ : M' →ₛₗ[σ] M'')
  {r : ℕ} (p' : (Fin r → B') →ₗ[B'] M') (δ' : ↥(ker p') →ₗ[B'] N')
  (p'' : (Fin r → B'') →ₗ[B''] M'') (δ'' : ↥(ker p'') →ₗ[B''] N'')
  (hp : ∀ v : Fin r → B', p'' (fun m => σ (v m)) = μσ (p' v))
  (hδ : ∀ (s : ↥(ker p')) (s'' : ↥(ker p'')), (∀ m, (s'' : Fin r → B'') m = σ ((s : Fin r → B') m)) → δ'' s'' = νσ (δ' s))

include hp in
theorem coordMap_mem_ker (s : ↥(ker p')) : coordMap σ r (s : Fin r → B') ∈ ker p'' := by
  rw [mem_ker]
  show p'' (fun m => σ ((s : Fin r → B') m)) = 0
  rw [hp, (mem_ker.mp s.2), map_zero]

noncomputable def resMap : ExtPushout p' δ' →ₛₗ[σ] ExtPushout p'' δ'' :=
  slift p' δ' ((ExtPushout.inl p'' δ'').comp νσ) ((ExtPushout.inr p'' δ'').comp (coordMap σ r)) (fun s => by
    rw [LinearMap.comp_apply, LinearMap.comp_apply]
    have hmem := coordMap_mem_ker σ μσ p' p'' hp s
    rw [show coordMap σ r (s : Fin r → B') = ((⟨_, hmem⟩ : ↥(ker p'')) : Fin r → B'') from rfl, ExtPushout.inr_coe,
      hδ s ⟨_, hmem⟩ (fun m => rfl)])

theorem resMap_inl (n : N') : resMap σ νσ μσ p' δ' p'' δ'' hp hδ (ExtPushout.inl p' δ' n) = ExtPushout.inl p'' δ'' (νσ n) :=
  slift_inl _ _ _ _ _ n

theorem resMap_inr (v : Fin r → B') :
    resMap σ νσ μσ p' δ' p'' δ'' hp hδ (ExtPushout.inr p' δ' v) = ExtPushout.inr p'' δ'' (fun m => σ (v m)) :=
  slift_inr _ _ _ _ _ v

theorem resMap_mk (n : N') (v : Fin r → B') :
    resMap σ νσ μσ p' δ' p'' δ'' hp hδ (ExtPushout.mk p' δ' (n, v)) = ExtPushout.mk p'' δ'' (νσ n, fun m => σ (v m)) := by
  rw [ExtPushout.mk_eq_inl_add_inr, map_add, resMap_inl, resMap_inr, ← ExtPushout.mk_eq_inl_add_inr]

theorem exists_vec_lift (g₀ : B') (locS : ∀ z : B'', ∃ (n : ℕ) (a : B'), z * σ g₀ ^ n = σ a) (v : Fin r → B'') :
    ∃ (b : ℕ) (w : Fin r → B'), (fun m => σ (w m)) = σ (g₀ ^ b) • v := by
  classical
  choose n a hna using fun m => locS (v m)
  refine ⟨∑ m, n m, fun m => a m * g₀ ^ ((∑ m, n m) - n m), ?_⟩
  ext m
  have hle : n m ≤ ∑ m, n m := Finset.single_le_sum (fun i _ => Nat.zero_le (n i)) (Finset.mem_univ m)
  rw [Pi.smul_apply, smul_eq_mul, map_mul, map_pow, ← hna, map_pow, mul_assoc, ← pow_add, Nat.add_sub_cancel' hle, mul_comm]

include hp hδ in

theorem resMap_surj_upto (g₀ : B') (locS : ∀ z : B'', ∃ (n : ℕ) (a : B'), z * σ g₀ ^ n = σ a)
    (NS : ∀ x : N'', ∃ (n : ℕ) (y : N'), νσ y = σ (g₀ ^ n) • x) (y : ExtPushout p'' δ'') :
    ∃ (n : ℕ) (x : ExtPushout p' δ'), resMap σ νσ μσ p' δ' p'' δ'' hp hδ x = σ (g₀ ^ n) • y := by
  refine ind p'' δ'' (C := fun y => ∃ (n : ℕ) (x : ExtPushout p' δ'), resMap σ νσ μσ p' δ' p'' δ'' hp hδ x = σ (g₀ ^ n) • y) y
    fun n'' v'' => ?_
  obtain ⟨a, y₁, hy₁⟩ := NS n''
  obtain ⟨b, w, hw⟩ := exists_vec_lift σ g₀ locS v''
  refine ⟨a + b, ExtPushout.inl p' δ' (g₀ ^ b • y₁) + ExtPushout.inr p' δ' (g₀ ^ a • w), ?_⟩
  rw [map_add, resMap_inl, resMap_inr, LinearMap.map_smulₛₗ, hy₁]
  have hw' : (fun m => σ ((g₀ ^ a • w) m)) = σ (g₀ ^ a) • (σ (g₀ ^ b) • v'') := by
    rw [← hw]; ext m; rw [Pi.smul_apply, Pi.smul_apply, smul_eq_mul, smul_eq_mul, map_mul]
  rw [hw', smul_smul, smul_smul, ← map_mul, ← map_mul, ← pow_add, ← pow_add, add_comm b a, smul_add, map_smul, map_smul]

include hp hδ in

theorem resMap_ker_torsion (g₀ : B')
    (NK : ∀ y : N', νσ y = 0 → ∃ n : ℕ, g₀ ^ n • y = 0) (MK : ∀ y : M', μσ y = 0 → ∃ n : ℕ, g₀ ^ n • y = 0)
    (x : ExtPushout p' δ') (hx : resMap σ νσ μσ p' δ' p'' δ'' hp hδ x = 0) : ∃ n : ℕ, g₀ ^ n • x = 0 := by
  obtain ⟨⟨n, v⟩, rfl⟩ := ExtPushout.mk_surjective p' δ' x
  rw [resMap_mk] at hx
  obtain ⟨s'', hs1, hs2⟩ := (ExtPushout.mk_eq_zero_iff p'' δ'' _).mp hx
  dsimp only at hs1 hs2

  have hpv : μσ (p' v) = 0 := by
    rw [← hp, ← hs2, map_neg, mem_ker.mp s''.2, neg_zero]
  obtain ⟨a, ha⟩ := MK (p' v) hpv
  have hker : g₀ ^ a • v ∈ ker p' := by rw [mem_ker, map_smul, ha]
  have hcoords : ∀ m, ((-(σ (g₀ ^ a) • s'') : ↥(ker p'')) : Fin r → B'') m = σ (((⟨g₀ ^ a • v, hker⟩ : ↥(ker p')) : Fin r → B') m) := by
    intro m
    have h2 := congrFun hs2 m
    simp only [Pi.neg_apply] at h2
    show (-(σ (g₀ ^ a) • (s'' : Fin r → B''))) m = σ ((g₀ ^ a • v) m)
    rw [Pi.neg_apply, Pi.smul_apply, Pi.smul_apply, smul_eq_mul, smul_eq_mul, map_mul, ← h2, mul_neg]
  have hδt : νσ (δ' ⟨g₀ ^ a • v, hker⟩) = -(σ (g₀ ^ a) • νσ n) := by
    rw [← hδ ⟨g₀ ^ a • v, hker⟩ (-(σ (g₀ ^ a) • s'')) hcoords, map_neg, map_smul, hs1]
  have hsum : νσ (δ' ⟨g₀ ^ a • v, hker⟩ + g₀ ^ a • n) = 0 := by
    rw [map_add, LinearMap.map_smulₛₗ, hδt, map_pow, neg_add_cancel]
  obtain ⟨b, hb⟩ := NK _ hsum
  refine ⟨b + a, ?_⟩
  rw [← map_smul, Prod.smul_mk, ExtPushout.mk_eq_inl_add_inr, pow_add, mul_smul, mul_smul,
    show g₀ ^ a • v = ((⟨g₀ ^ a • v, hker⟩ : ↥(ker p')) : Fin r → B') from rfl, map_smul (ExtPushout.inr p' δ'),
    ExtPushout.inr_coe, ← map_smul, ← map_add, ← smul_add, add_comm, hb, map_zero]

end resMap

end EP

namespace SG

open AlgebraicGeometry

variable {A : Type u} [CommRing A] {P : Scheme.{u}} (q : P ⟶ Spec (CommRingCat.of A))

abbrev ρ (P : Scheme.{u}) {U V : P.Opens} (h : V ≤ U) : Γ(P, U) →+* Γ(P, V) := (P.presheaf.map (homOfLE h).op).hom

omit q in
theorem ρ_refl_apply (U : P.Opens) (x : Γ(P, U)) : ρ P (le_refl U) x = x := by
  show (P.presheaf.map (homOfLE (le_refl U)).op).hom x = x
  rw [Subsingleton.elim (homOfLE (le_refl U)).op (𝟙 (Opposite.op U)), P.presheaf.map_id]; rfl

omit q in
theorem ρ_ρ {U V W : P.Opens} (h : V ≤ U) (h' : W ≤ V) (x : Γ(P, U)) : ρ P h' (ρ P h x) = ρ P (h'.trans h) x := by
  show (P.presheaf.map (homOfLE h').op).hom ((P.presheaf.map (homOfLE h).op).hom x) = (P.presheaf.map (homOfLE (h'.trans h)).op).hom x
  rw [← CommRingCat.comp_apply, ← P.presheaf.map_comp]; rfl

theorem ρ_algebraMap {U V : P.Opens} (h : V ≤ U) (a : A) :
    ρ P h ((Scheme.TwoAffineOpenCover.algebraOfHom q U).algebraMap a) = (Scheme.TwoAffineOpenCover.algebraOfHom q V).algebraMap a := by
  letI := Scheme.TwoAffineOpenCover.algebraOfHom q U; letI := Scheme.TwoAffineOpenCover.algebraOfHom q V
  exact (Scheme.TwoAffineOpenCover.restrictAlgHom q h).commutes a

omit q in

theorem flat_ρ {U : P.Opens} (hU : IsAffineOpen U) (V : P.affineOpens) (h : V.1 ≤ U) : (ρ P h).Flat := by
  have H := AlgebraicGeometry.HasRingHomProperty.appLE @AlgebraicGeometry.Flat (𝟙 P) inferInstance ⟨U, hU⟩ V h
  simp only [Scheme.Hom.appLE, Scheme.Hom.id_app, Category.id_comp] at H
  exact H

def resₛ (F : OModulePresheaf q) {U V : P.Opens} (h : V ≤ U) : F.obj U →ₛₗ[ρ P h] F.obj V where
  toFun := F.res h
  map_add' x y := map_add _ x y
  map_smul' a x := F.res_smul h a x

theorem resₛ_apply (F : OModulePresheaf q) {U V : P.Opens} (h : V ≤ U) (x : F.obj U) : resₛ q F h x = F.res h x := rfl

theorem qc_of_eq (F : OModulePresheaf q) (hF : F.IsQuasicoherent) (U : P.affineOpens) (f : Γ(P, U.1)) (V : P.Opens)
    (hV : V = P.basicOpen f) :
    (∀ x : F.obj V, ∃ (n : ℕ) (y : F.obj U.1),
        F.res (hV.trans_le (P.basicOpen_le f)) y = ρ P (hV.trans_le (P.basicOpen_le f)) (f ^ n) • x) ∧
    (∀ y : F.obj U.1, F.res (hV.trans_le (P.basicOpen_le f)) y = 0 → ∃ n : ℕ, f ^ n • y = 0) := by
  subst hV; exact hF U f

omit q in
theorem loc_of_eq (U : P.affineOpens) (f : Γ(P, U.1)) (V : P.Opens) (hV : V = P.basicOpen f) (z : Γ(P, V)) :
    ∃ (n : ℕ) (a : Γ(P, U.1)), z * ρ P (hV.trans_le (P.basicOpen_le f)) f ^ n = ρ P (hV.trans_le (P.basicOpen_le f)) a := by
  subst hV
  haveI := U.2.isLocalization_basicOpen f
  exact IsLocalization.Away.surj f z

theorem isBaseChange_res (F : OModulePresheaf q) (hF : F.IsQuasicoherent) {U : P.Opens} (hU : IsAffineOpen U) (V : P.affineOpens)
    (h : V.1 ≤ U) :
    letI := (ρ P h).toAlgebra
    letI : Module Γ(P, U) (F.obj V.1) := Module.compHom _ (ρ P h)
    ∃ (_ : IsScalarTower Γ(P, U) Γ(P, V.1) (F.obj V.1)) (μ : F.obj U →ₗ[Γ(P, U)] F.obj V.1),
      (∀ x, μ x = F.res h x) ∧ IsBaseChange Γ(P, V.1) μ := by
  letI := (ρ P h).toAlgebra
  letI : Module Γ(P, U) (F.obj V.1) := Module.compHom _ (ρ P h)
  haveI hst : IsScalarTower Γ(P, U) Γ(P, V.1) (F.obj V.1) := IsScalarTower.of_algebraMap_smul fun a x => rfl
  let μ : F.obj U →ₗ[Γ(P, U)] F.obj V.1 :=
    { toFun := F.res h, map_add' := fun x y => map_add _ x y, map_smul' := fun a x => F.res_smul h a x }
  obtain ⟨β, hβ⟩ :=
    AlgebraicGeometry.OModulePresheaf.IsQuasicoherent.exists_linearEquiv_tensorProduct_apply_one_tmul_eq_res F hF ⟨U, hU⟩ V h
  exact ⟨hst, μ, fun x => rfl, IsBaseChange.of_equiv β hβ⟩

end SG

namespace EP

def linA {A B' B'' : Type u} [CommRing A] [CommRing B'] [CommRing B''] (α' : A →+* B') (α'' : A →+* B'') (σ : B' →+* B'')
    (hσ : ∀ a, σ (α' a) = α'' a) {M' M'' : Type u} [AddCommGroup M'] [Module B' M'] [AddCommGroup M''] [Module B'' M'']
    (f : M' →ₛₗ[σ] M'') :
    letI := Module.compHom M' α'; letI := Module.compHom M'' α''; M' →ₗ[A] M'' :=
  letI := Module.compHom M' α'; letI := Module.compHom M'' α''
  { toFun := f, map_add' := f.map_add, map_smul' := fun a x => by
      show f (α' a • x) = α'' a • f x
      rw [f.map_smulₛₗ, hσ] }

def inlA {A B : Type u} [CommRing A] [CommRing B] (inst : Algebra A B) {M N : Type u} [AddCommGroup M] [Module B M]
    [AddCommGroup N] [Module B N] [Module A N] (hN : letI := inst; IsScalarTower A B N)
    {r : ℕ} (p : (Fin r → B) →ₗ[B] M) (δ : ↥(LinearMap.ker p) →ₗ[B] N) :
    letI := Module.compHom (LinearMap.ExtPushout p δ) inst.algebraMap; N →ₗ[A] LinearMap.ExtPushout p δ :=
  letI := Module.compHom (LinearMap.ExtPushout p δ) inst.algebraMap
  letI := inst; haveI := hN
  { toFun := LinearMap.ExtPushout.inl p δ
    map_add' := fun x y => map_add _ x y
    map_smul' := fun a x => by
      show LinearMap.ExtPushout.inl p δ (a • x) = algebraMap A B a • LinearMap.ExtPushout.inl p δ x
      rw [← map_smul, algebraMap_smul] }

def projA {A B : Type u} [CommRing A] [CommRing B] (inst : Algebra A B) {M N : Type u} [AddCommGroup M] [Module B M]
    [AddCommGroup N] [Module B N] [Module A M] (hM : letI := inst; IsScalarTower A B M)
    {r : ℕ} (p : (Fin r → B) →ₗ[B] M) (δ : ↥(LinearMap.ker p) →ₗ[B] N) :
    letI := Module.compHom (LinearMap.ExtPushout p δ) inst.algebraMap; LinearMap.ExtPushout p δ →ₗ[A] M :=
  letI := Module.compHom (LinearMap.ExtPushout p δ) inst.algebraMap
  letI := inst; haveI := hM
  { toFun := LinearMap.ExtPushout.proj p δ
    map_add' := fun x y => map_add _ x y
    map_smul' := fun a x => by
      show LinearMap.ExtPushout.proj p δ (algebraMap A B a • x) = a • LinearMap.ExtPushout.proj p δ x
      rw [map_smul, algebraMap_smul] }

theorem linA_apply {A B' B'' : Type u} [CommRing A] [CommRing B'] [CommRing B''] (α' : A →+* B') (α'' : A →+* B'') (σ : B' →+* B'')
    (hσ : ∀ a, σ (α' a) = α'' a) {M' M'' : Type u} [AddCommGroup M'] [Module B' M'] [AddCommGroup M''] [Module B'' M'']
    (f : M' →ₛₗ[σ] M'') (x : M') :
    letI := Module.compHom M' α'; letI := Module.compHom M'' α''; linA α' α'' σ hσ f x = f x := rfl

end EP

namespace EP

open LinearMap

section more

variable {B' : Type u} [CommRing B'] {B'' : Type u} [CommRing B''] (σ : B' →+* B'')
  {N' : Type u} [AddCommGroup N'] [Module B' N'] {N'' : Type u} [AddCommGroup N''] [Module B'' N'']
  (νσ : N' →ₛₗ[σ] N'')
  {M' : Type u} [AddCommGroup M'] [Module B' M'] {M'' : Type u} [AddCommGroup M''] [Module B'' M'']
  (μσ : M' →ₛₗ[σ] M'')
  {r : ℕ} (p' : (Fin r → B') →ₗ[B'] M') (δ' : ↥(ker p') →ₗ[B'] N')
  (p'' : (Fin r → B'') →ₗ[B''] M'') (δ'' : ↥(ker p'') →ₗ[B''] N'')
  (hp : ∀ v : Fin r → B', p'' (fun m => σ (v m)) = μσ (p' v))
  (hδ : ∀ (s : ↥(ker p')) (s'' : ↥(ker p'')), (∀ m, (s'' : Fin r → B'') m = σ ((s : Fin r → B') m)) → δ'' s'' = νσ (δ' s))

theorem proj_resMap (x : ExtPushout p' δ') :
    ExtPushout.proj p'' δ'' (resMap σ νσ μσ p' δ' p'' δ'' hp hδ x) = μσ (ExtPushout.proj p' δ' x) := by
  refine ind p' δ' (C := fun x => ExtPushout.proj p'' δ'' (resMap σ νσ μσ p' δ' p'' δ'' hp hδ x) = μσ (ExtPushout.proj p' δ' x)) x
    fun n v => ?_
  show ExtPushout.proj p'' δ'' (resMap σ νσ μσ p' δ' p'' δ'' hp hδ (_ + _)) = μσ (ExtPushout.proj p' δ' (_ + _))
  rw [map_add, resMap_inl, resMap_inr, map_add, map_add, ExtPushout.proj_inl, ExtPushout.proj_inr, ExtPushout.proj_inl,
    ExtPushout.proj_inr, zero_add, map_add, map_zero, zero_add, hp]

end more

theorem resMap_self {B' : Type u} [CommRing B'] (σ : B' →+* B') (hσ : ∀ b, σ b = b)
    {N' : Type u} [AddCommGroup N'] [Module B' N'] (νσ : N' →ₛₗ[σ] N') (hν : ∀ n, νσ n = n)
    {M' : Type u} [AddCommGroup M'] [Module B' M'] (μσ : M' →ₛₗ[σ] M')
    {r : ℕ} (p' : (Fin r → B') →ₗ[B'] M') (δ' : ↥(ker p') →ₗ[B'] N') (hp) (hδ) (x : ExtPushout p' δ') :
    resMap σ νσ μσ p' δ' p' δ' hp hδ x = x := by
  refine ind p' δ' (C := fun x => resMap σ νσ μσ p' δ' p' δ' hp hδ x = x) x fun n v => ?_
  show resMap σ νσ μσ p' δ' p' δ' hp hδ (_ + _) = _
  rw [map_add, resMap_inl, resMap_inr, hν]
  congr 2
  funext m; exact hσ (v m)

theorem resMap_trans {B₁ B₂ B₃ : Type u} [CommRing B₁] [CommRing B₂] [CommRing B₃]
    (σ₁₂ : B₁ →+* B₂) (σ₂₃ : B₂ →+* B₃) (σ₁₃ : B₁ →+* B₃) (hσ : ∀ b, σ₂₃ (σ₁₂ b) = σ₁₃ b)
    {N₁ N₂ N₃ : Type u} [AddCommGroup N₁] [Module B₁ N₁] [AddCommGroup N₂] [Module B₂ N₂] [AddCommGroup N₃] [Module B₃ N₃]
    (ν₁₂ : N₁ →ₛₗ[σ₁₂] N₂) (ν₂₃ : N₂ →ₛₗ[σ₂₃] N₃) (ν₁₃ : N₁ →ₛₗ[σ₁₃] N₃) (hν : ∀ n, ν₂₃ (ν₁₂ n) = ν₁₃ n)
    {M₁ M₂ M₃ : Type u} [AddCommGroup M₁] [Module B₁ M₁] [AddCommGroup M₂] [Module B₂ M₂] [AddCommGroup M₃] [Module B₃ M₃]
    (μ₁₂ : M₁ →ₛₗ[σ₁₂] M₂) (μ₂₃ : M₂ →ₛₗ[σ₂₃] M₃) (μ₁₃ : M₁ →ₛₗ[σ₁₃] M₃)
    {r : ℕ} (p₁ : (Fin r → B₁) →ₗ[B₁] M₁) (δ₁ : ↥(ker p₁) →ₗ[B₁] N₁) (p₂ : (Fin r → B₂) →ₗ[B₂] M₂) (δ₂ : ↥(ker p₂) →ₗ[B₂] N₂)
    (p₃ : (Fin r → B₃) →ₗ[B₃] M₃) (δ₃ : ↥(ker p₃) →ₗ[B₃] N₃) (hp₁₂) (hδ₁₂) (hp₂₃) (hδ₂₃) (hp₁₃) (hδ₁₃) (x : ExtPushout p₁ δ₁) :
    resMap σ₁₃ ν₁₃ μ₁₃ p₁ δ₁ p₃ δ₃ hp₁₃ hδ₁₃ x =
      resMap σ₂₃ ν₂₃ μ₂₃ p₂ δ₂ p₃ δ₃ hp₂₃ hδ₂₃ (resMap σ₁₂ ν₁₂ μ₁₂ p₁ δ₁ p₂ δ₂ hp₁₂ hδ₁₂ x) := by
  refine ind p₁ δ₁ (C := fun x => resMap σ₁₃ ν₁₃ μ₁₃ p₁ δ₁ p₃ δ₃ hp₁₃ hδ₁₃ x =
      resMap σ₂₃ ν₂₃ μ₂₃ p₂ δ₂ p₃ δ₃ hp₂₃ hδ₂₃ (resMap σ₁₂ ν₁₂ μ₁₂ p₁ δ₁ p₂ δ₂ hp₁₂ hδ₁₂ x)) x fun n v => ?_
  show resMap σ₁₃ ν₁₃ μ₁₃ p₁ δ₁ p₃ δ₃ hp₁₃ hδ₁₃ (_ + _) =
      resMap σ₂₃ ν₂₃ μ₂₃ p₂ δ₂ p₃ δ₃ hp₂₃ hδ₂₃ (resMap σ₁₂ ν₁₂ μ₁₂ p₁ δ₁ p₂ δ₂ hp₁₂ hδ₁₂ (_ + _))
  rw [map_add, map_add, resMap_inl, resMap_inr, resMap_inl, resMap_inr, map_add, resMap_inl, resMap_inr, hν]
  congr 2
  funext m; exact (hσ (v m)).symm

theorem isScalarTower_compHom {A B : Type u} [CommRing A] [CommRing B] (inst : Algebra A B) (M : Type u) [AddCommGroup M] [Module B M] :
    letI := inst; letI := Module.compHom M inst.algebraMap; IsScalarTower A B M := by
  letI := inst; letI := Module.compHom M inst.algebraMap
  exact ⟨fun a b x => by rw [Algebra.smul_def, mul_smul]; rfl⟩

theorem range_inlA_eq_ker_projA {A B : Type u} [CommRing A] [CommRing B] (inst : Algebra A B) {M N : Type u}
    [AddCommGroup M] [Module B M] [AddCommGroup N] [Module B N] [Module A N] [Module A M]
    (hN : letI := inst; IsScalarTower A B N) (hM : letI := inst; IsScalarTower A B M)
    {r : ℕ} (p : (Fin r → B) →ₗ[B] M) (δ : ↥(LinearMap.ker p) →ₗ[B] N) :
    letI := Module.compHom (LinearMap.ExtPushout p δ) inst.algebraMap
    LinearMap.range (inlA inst hN p δ) = LinearMap.ker (projA inst hM p δ) := by
  letI := Module.compHom (LinearMap.ExtPushout p δ) inst.algebraMap
  refine Submodule.ext fun x => ?_
  rw [LinearMap.mem_range, LinearMap.mem_ker]
  have h := SetLike.ext_iff.mp (ExtPushout.range_inl_eq_ker_proj p δ) x
  rw [LinearMap.mem_range, LinearMap.mem_ker] at h
  exact h

theorem finite_extPushout {B : Type u} [CommRing B] {M N : Type u} [AddCommGroup M] [Module B M] [AddCommGroup N] [Module B N]
    [Module.Finite B N] {r : ℕ} (p : (Fin r → B) →ₗ[B] M) (δ : ↥(LinearMap.ker p) →ₗ[B] N) :
    Module.Finite B (ExtPushout p δ) := by
  unfold ExtPushout
  infer_instance

end EP

end X1bSol

namespace X1bSol

open AlgebraicGeometry

section chart

variable {A : Type u} [CommRing A] {P : Scheme.{u}} (q : P ⟶ Spec (CommRingCat.of A))
  (GE GK : OModulePresheaf q) {U₀ : P.Opens} {r : ℕ}

theorem chart_kit (hGEq : GE.IsQuasicoherent) (hGKq : GK.IsQuasicoherent) (hU₀ : IsAffineOpen U₀)
    (pr : (Fin r → Γ(P, U₀)) →ₗ[Γ(P, U₀)] GE.obj U₀) (hpr : Function.Surjective pr)
    (δ : ↥(LinearMap.ker pr) →ₗ[Γ(P, U₀)] GK.obj U₀) (U : {U : P.affineOpens // U.1 ≤ U₀}) :
    ∃ (p' : (Fin r → Γ(P, U.1.1)) →ₗ[Γ(P, U.1.1)] GE.obj U.1.1) (g : ↥(LinearMap.ker pr) → ↥(LinearMap.ker p'))
      (δ' : ↥(LinearMap.ker p') →ₗ[Γ(P, U.1.1)] GK.obj U.1.1),
      (∀ v : Fin r → Γ(P, U.1.1), p' v = ∑ m, v m • GE.res U.2 (pr (Pi.single m 1))) ∧
      (∀ v : Fin r → Γ(P, U₀), p' (fun m => SG.ρ P U.2 (v m)) = GE.res U.2 (pr v)) ∧
      Function.Surjective p' ∧
      (∀ (s : ↥(LinearMap.ker pr)) (m : Fin r),
        ((g s : ↥(LinearMap.ker p')) : Fin r → Γ(P, U.1.1)) m = SG.ρ P U.2 ((s : Fin r → Γ(P, U₀)) m)) ∧
      (∀ s : ↥(LinearMap.ker pr), δ' (g s) = GK.res U.2 (δ s)) ∧
      Submodule.span Γ(P, U.1.1) (Set.range fun s : ↥(LinearMap.ker pr) => ((g s : ↥(LinearMap.ker p')) : Fin r → Γ(P, U.1.1))) =
        LinearMap.ker p' := by
  letI alg := (SG.ρ P U.2).toAlgebra
  letI mE : Module Γ(P, U₀) (GE.obj U.1.1) := Module.compHom _ (SG.ρ P U.2)
  letI mK : Module Γ(P, U₀) (GK.obj U.1.1) := Module.compHom _ (SG.ρ P U.2)
  obtain ⟨istE, μE, hμE, hbcE⟩ := SG.isBaseChange_res q GE hGEq hU₀ U.1 U.2
  obtain ⟨istK, μK, hμK, hbcK⟩ := SG.isBaseChange_res q GK hGKq hU₀ U.1 U.2
  haveI := istE; haveI := istK
  haveI : Module.Flat Γ(P, U₀) Γ(P, U.1.1) := SG.flat_ρ hU₀ U.1 U.2
  have hp' : ∀ v, BC.bc Γ(P, U.1.1) μE pr (BC.φ Γ(P, U₀) Γ(P, U.1.1) r v) = μE (pr v) := BC.bc_φ μE pr
  refine ⟨BC.bc Γ(P, U.1.1) μE pr, fun s => BC.g μE pr _ hp' s, BC.δ' μE pr _ hp' μK hbcE δ, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro v; rw [BC.bc_apply]; exact Finset.sum_congr rfl fun m _ => by rw [hμE]
  · intro v; rw [← hμE]; exact hp' v
  · exact BC.surjective_of_isBaseChange μE pr _ hp' hbcE hpr
  · intro s m; rfl
  · intro s; rw [BC.δ'_g, hμK]
  · exact BC.span_range_g μE pr _ hp' hbcE

variable (prU : ∀ U : {U : P.affineOpens // U.1 ≤ U₀}, (Fin r → Γ(P, U.1.1)) →ₗ[Γ(P, U.1.1)] GE.obj U.1.1)

theorem chart_prUn (pr : (Fin r → Γ(P, U₀)) →ₗ[Γ(P, U₀)] GE.obj U₀)
    (hform : ∀ (U : {U : P.affineOpens // U.1 ≤ U₀}) (v : Fin r → Γ(P, U.1.1)), prU U v = ∑ m, v m • GE.res U.2 (pr (Pi.single m 1)))
    (U U' : {U : P.affineOpens // U.1 ≤ U₀}) (h : U'.1.1 ≤ U.1.1) (v : Fin r → Γ(P, U.1.1)) :
    prU U' (fun m => SG.ρ P h (v m)) = GE.res h (prU U v) := by
  rw [hform U', hform U, map_sum]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [GE.res_smul, GE.res_res]

variable (δU : ∀ U : {U : P.affineOpens // U.1 ≤ U₀}, ↥(LinearMap.ker (prU U)) →ₗ[Γ(P, U.1.1)] GK.obj U.1.1)
  (hprUn : ∀ (U U' : {U : P.affineOpens // U.1 ≤ U₀}) (h : U'.1.1 ≤ U.1.1) (v : Fin r → Γ(P, U.1.1)), prU U' (fun m => SG.ρ P h (v m)) = GE.res h (prU U v))

include hprUn in
theorem chart_memn (U U' : {U : P.affineOpens // U.1 ≤ U₀}) (h : U'.1.1 ≤ U.1.1) (s : ↥(LinearMap.ker (prU U))) :
    (fun m => SG.ρ P h ((s : Fin r → Γ(P, U.1.1)) m)) ∈ LinearMap.ker (prU U') := by
  rw [LinearMap.mem_ker, hprUn, LinearMap.mem_ker.mp s.2, map_zero]

include hprUn in

theorem chart_δUn (pr : (Fin r → Γ(P, U₀)) →ₗ[Γ(P, U₀)] GE.obj U₀) (δ : ↥(LinearMap.ker pr) →ₗ[Γ(P, U₀)] GK.obj U₀)
    (gU : ∀ U : {U : P.affineOpens // U.1 ≤ U₀}, ↥(LinearMap.ker pr) → ↥(LinearMap.ker (prU U)))
    (hgU : ∀ (U : {U : P.affineOpens // U.1 ≤ U₀}) (s : ↥(LinearMap.ker pr)) (m : Fin r),
      ((gU U s : ↥(LinearMap.ker (prU U))) : Fin r → Γ(P, U.1.1)) m = SG.ρ P U.2 ((s : Fin r → Γ(P, U₀)) m))
    (hδU : ∀ (U : {U : P.affineOpens // U.1 ≤ U₀}) (s : ↥(LinearMap.ker pr)), δU U (gU U s) = GK.res U.2 (δ s))
    (hspan : ∀ U : {U : P.affineOpens // U.1 ≤ U₀}, Submodule.span Γ(P, U.1.1)
      (Set.range fun s : ↥(LinearMap.ker pr) => ((gU U s : ↥(LinearMap.ker (prU U))) : Fin r → Γ(P, U.1.1))) = LinearMap.ker (prU U))
    (U U' : {U : P.affineOpens // U.1 ≤ U₀}) (h : U'.1.1 ≤ U.1.1) (s : ↥(LinearMap.ker (prU U))) (s' : ↥(LinearMap.ker (prU U')))
    (hs' : ∀ m : Fin r, (s' : Fin r → Γ(P, U'.1.1)) m = SG.ρ P h ((s : Fin r → Γ(P, U.1.1)) m)) :
    δU U' s' = GK.res h (δU U s) := by
  let f₁ : ↥(LinearMap.ker (prU U)) →ₛₗ[SG.ρ P h] GK.obj U'.1.1 :=
    { toFun := fun s => δU U' ⟨_, chart_memn q GE prU hprUn U U' h s⟩
      map_add' := fun s t => by
        rw [← map_add]; congr 1; apply Subtype.ext; funext m
        show SG.ρ P h (((s + t : ↥(LinearMap.ker (prU U))) : Fin r → Γ(P, U.1.1)) m) = _
        rw [Submodule.coe_add, Pi.add_apply, map_add]; rfl
      map_smul' := fun a s => by
        rw [← map_smul]; congr 1; apply Subtype.ext; funext m
        show SG.ρ P h (((a • s : ↥(LinearMap.ker (prU U))) : Fin r → Γ(P, U.1.1)) m) = _
        rw [Submodule.coe_smul, Pi.smul_apply, smul_eq_mul, map_mul]; rfl }
  let f₂ : ↥(LinearMap.ker (prU U)) →ₛₗ[SG.ρ P h] GK.obj U'.1.1 :=
    { toFun := fun s => GK.res h (δU U s)
      map_add' := fun s t => by rw [map_add, map_add]
      map_smul' := fun a s => by rw [map_smul, GK.res_smul] }
  have heq : f₁ = f₂ := by
    refine BC.ext_of_span_eq (LinearMap.ker (prU U)) (gU U) (hspan U) f₁ f₂ fun s₀ => ?_
    have h1 : (⟨_, chart_memn q GE prU hprUn U U' h (gU U s₀)⟩ : ↥(LinearMap.ker (prU U'))) = gU U' s₀ := by
      apply Subtype.ext; funext m
      show SG.ρ P h (((gU U s₀ : ↥(LinearMap.ker (prU U))) : Fin r → Γ(P, U.1.1)) m) = _
      rw [hgU, hgU, SG.ρ_ρ]
    show δU U' ⟨_, chart_memn q GE prU hprUn U U' h (gU U s₀)⟩ = GK.res h (δU U (gU U s₀))
    rw [h1, hδU, hδU, GK.res_res]
  have hs : s' = ⟨_, chart_memn q GE prU hprUn U U' h s⟩ := Subtype.ext (funext hs')
  rw [hs]
  exact DFunLike.congr_fun heq s

variable (hδUn : ∀ (U U' : {U : P.affineOpens // U.1 ≤ U₀}) (h : U'.1.1 ≤ U.1.1) (s : ↥(LinearMap.ker (prU U))) (s' : ↥(LinearMap.ker (prU U'))),
    (∀ m : Fin r, (s' : Fin r → Γ(P, U'.1.1)) m = SG.ρ P h ((s : Fin r → Γ(P, U.1.1)) m)) → δU U' s' = GK.res h (δU U s))

noncomputable abbrev Rmap (U U' : {U : P.affineOpens // U.1 ≤ U₀}) (h : U'.1.1 ≤ U.1.1) :
    LinearMap.ExtPushout (prU U) (δU U) →ₛₗ[SG.ρ P h] LinearMap.ExtPushout (prU U') (δU U') :=
  EP.resMap (SG.ρ P h) (SG.resₛ q GK h) (SG.resₛ q GE h) (prU U) (δU U) (prU U') (δU U') (hprUn U U' h) (hδUn U U' h)

end chart

end X1bSol

open X1bSol in
theorem solution
    {A : Type u} [CommRing A] {P : Scheme.{u}} (q : P ⟶ Spec (CommRingCat.of A)) [IsLocallyNoetherian P]
    (GE : OModulePresheaf q) (hGEc : GE.IsCoherent) (hGEq : GE.IsQuasicoherent)
    (GK : OModulePresheaf q) (hGKc : GK.IsCoherent) (hGKq : GK.IsQuasicoherent)
    (U₀ : P.Opens) (hU₀ : IsAffineOpen U₀) (r : ℕ)
    (pr : (Fin r → Γ(P, U₀)) →ₗ[Γ(P, U₀)] GE.obj U₀) (hpr : Function.Surjective pr)
    (δ : ↥(LinearMap.ker pr) →ₗ[Γ(P, U₀)] GK.obj U₀) :
    ∃ (prU : ∀ (U : {U : P.affineOpens // U.1 ≤ U₀}),
        (Fin r → Γ(P, U.1.1)) →ₗ[Γ(P, U.1.1)] GE.obj U.1.1)
      (_hprU : ∀ (U : {U : P.affineOpens // U.1 ≤ U₀}) (v : Fin r → Γ(P, U₀)),
        prU U (fun m => (P.presheaf.map (homOfLE U.2).op).hom (v m)) = GE.res U.2 (pr v))
      (_hprUs : ∀ (U : {U : P.affineOpens // U.1 ≤ U₀}), Function.Surjective (prU U))
      (_hprUn : ∀ (U U' : {U : P.affineOpens // U.1 ≤ U₀}) (h : U'.1.1 ≤ U.1.1) (v : Fin r → Γ(P, U.1.1)),
        prU U' (fun m => (P.presheaf.map (homOfLE h).op).hom (v m)) = GE.res h (prU U v))
      (gU : ∀ (U : {U : P.affineOpens // U.1 ≤ U₀}), ↥(LinearMap.ker pr) → ↥(LinearMap.ker (prU U)))
      (_hgU : ∀ (U : {U : P.affineOpens // U.1 ≤ U₀}) (s : ↥(LinearMap.ker pr)) (m : Fin r),
        ((gU U s : ↥(LinearMap.ker (prU U))) : Fin r → Γ(P, U.1.1)) m =
          (P.presheaf.map (homOfLE U.2).op).hom ((s : Fin r → Γ(P, U₀)) m))
      (δU : ∀ (U : {U : P.affineOpens // U.1 ≤ U₀}), ↥(LinearMap.ker (prU U)) →ₗ[Γ(P, U.1.1)] GK.obj U.1.1)
      (_hδU : ∀ (U : {U : P.affineOpens // U.1 ≤ U₀}) (s : ↥(LinearMap.ker pr)),
        δU U (gU U s) = GK.res U.2 (δ s))
      (_hgUspan : ∀ (U : {U : P.affineOpens // U.1 ≤ U₀}),
        Submodule.span Γ(P, U.1.1)
            (Set.range fun s : ↥(LinearMap.ker pr) =>
              ((gU U s : ↥(LinearMap.ker (prU U))) : Fin r → Γ(P, U.1.1))) =
          LinearMap.ker (prU U))
      (_hδUn : ∀ (U U' : {U : P.affineOpens // U.1 ≤ U₀}) (h : U'.1.1 ≤ U.1.1)
        (s : ↥(LinearMap.ker (prU U))) (s' : ↥(LinearMap.ker (prU U'))),
        (∀ m : Fin r, (s' : Fin r → Γ(P, U'.1.1)) m = (P.presheaf.map (homOfLE h).op).hom ((s : Fin r → Γ(P, U.1.1)) m)) →
        δU U' s' = GK.res h (δU U s)),
    letI : ∀ (U : {U : P.affineOpens // U.1 ≤ U₀}), Module A (LinearMap.ExtPushout (prU U) (δU U)) :=
      fun U => Module.compHom _ (Scheme.TwoAffineOpenCover.algebraOfHom q U.1.1).algebraMap
    ∃ (_ : ∀ (U : {U : P.affineOpens // U.1 ≤ U₀}),
          letI := Scheme.TwoAffineOpenCover.algebraOfHom q U.1.1
          IsScalarTower A Γ(P, U.1.1) (LinearMap.ExtPushout (prU U) (δU U)))
      (res : ∀ {U U' : {U : P.affineOpens // U.1 ≤ U₀}}, U'.1.1 ≤ U.1.1 → (LinearMap.ExtPushout (prU U) (δU U) →ₗ[A] LinearMap.ExtPushout (prU U') (δU U')))
      (res_smul : ∀ {U U' : {U : P.affineOpens // U.1 ≤ U₀}} (h : U'.1.1 ≤ U.1.1) (a : Γ(P, U.1.1)) (x : LinearMap.ExtPushout (prU U) (δU U)),
          res h (a • x) = (P.presheaf.map (homOfLE h).op).hom a • res h x)
      (res_refl : ∀ (U : {U : P.affineOpens // U.1 ≤ U₀}) (x : LinearMap.ExtPushout (prU U) (δU U)), res (le_refl U.1.1) x = x)
      (res_comp : ∀ {U U' U'' : {U : P.affineOpens // U.1 ≤ U₀}} (h : U''.1.1 ≤ U'.1.1) (h' : U'.1.1 ≤ U.1.1)
          (x : LinearMap.ExtPushout (prU U) (δU U)), res (h.trans h') x = res h (res h' x))
      (hqc : ∀ (U Ug : {U : P.affineOpens // U.1 ≤ U₀}) (g : Γ(P, U.1.1)) (hUg : Ug.1.1 = P.basicOpen g),
          (∀ y : LinearMap.ExtPushout (prU Ug) (δU Ug), ∃ (n : ℕ) (x : LinearMap.ExtPushout (prU U) (δU U)),
              res (hUg.trans_le (P.basicOpen_le g)) x =
                (P.presheaf.map (homOfLE (hUg.trans_le (P.basicOpen_le g))).op).hom (g ^ n) • y) ∧
          (∀ x : LinearMap.ExtPushout (prU U) (δU U), res (hUg.trans_le (P.basicOpen_le g)) x = 0 → ∃ n : ℕ, (g ^ n) • x = 0))
      (hfg : ∀ (U : {U : P.affineOpens // U.1 ≤ U₀}), Module.Finite (Γ(P, U.1.1) : Type u) (LinearMap.ExtPushout (prU U) (δU U)))
      (ϑ : ∀ (U : {U : P.affineOpens // U.1 ≤ U₀}), GK.obj U.1.1 →ₗ[A] LinearMap.ExtPushout (prU U) (δU U))
      (θE : ∀ (U : {U : P.affineOpens // U.1 ≤ U₀}), LinearMap.ExtPushout (prU U) (δU U) →ₗ[A] GE.obj U.1.1)
            (hϑs : ∀ (U : {U : P.affineOpens // U.1 ≤ U₀}) (a : Γ(P, U.1.1)) (x : GK.obj U.1.1), ϑ U (a • x) = a • ϑ U x)
      (hθEs : ∀ (U : {U : P.affineOpens // U.1 ≤ U₀}) (a : Γ(P, U.1.1)) (x : LinearMap.ExtPushout (prU U) (δU U)), θE U (a • x) = a • θE U x)
            (hϑn : ∀ (U U' : {U : P.affineOpens // U.1 ≤ U₀}) (h : U'.1.1 ≤ U.1.1) (x : GK.obj U.1.1),
          ϑ U' (GK.res h x) = res h (ϑ U x))
      (hθEn : ∀ (U U' : {U : P.affineOpens // U.1 ≤ U₀}) (h : U'.1.1 ≤ U.1.1) (x : LinearMap.ExtPushout (prU U) (δU U)),
          θE U' (res h x) = GE.res h (θE U x))
            (hexact : ∀ (U : {U : P.affineOpens // U.1 ≤ U₀}), LinearMap.range (ϑ U) = LinearMap.ker (θE U))
      (hsurj : ∀ (U : {U : P.affineOpens // U.1 ≤ U₀}), Function.Surjective (θE U))
      (hϑi : ∀ (U : {U : P.affineOpens // U.1 ≤ U₀}), Function.Injective (ϑ U)),

      (∀ (U : {U : P.affineOpens // U.1 ≤ U₀}) (x : GK.obj U.1.1),
        ϑ U x = LinearMap.ExtPushout.inl (prU U) (δU U) x) ∧
      (∀ (U : {U : P.affineOpens // U.1 ≤ U₀}) (x : LinearMap.ExtPushout (prU U) (δU U)),
        θE U x = LinearMap.ExtPushout.proj (prU U) (δU U) x) ∧
      (∀ (U U' : {U : P.affineOpens // U.1 ≤ U₀}) (h : U'.1.1 ≤ U.1.1) (n : GK.obj U.1.1),
        res h (LinearMap.ExtPushout.inl (prU U) (δU U) n) = LinearMap.ExtPushout.inl (prU U') (δU U') (GK.res h n)) ∧
      (∀ (U U' : {U : P.affineOpens // U.1 ≤ U₀}) (h : U'.1.1 ≤ U.1.1) (v : Fin r → Γ(P, U.1.1)),
        res h (LinearMap.ExtPushout.inr (prU U) (δU U) v) =
          LinearMap.ExtPushout.inr (prU U') (δU U') (fun m => (P.presheaf.map (homOfLE h).op).hom (v m))) := by
  classical
  have kit := chart_kit q GE GK hGEq hGKq hU₀ pr hpr δ
  choose prU gU δU hform hprU hprUs hgU hδU hspan using kit
  have hprUn := chart_prUn q GE prU pr hform
  have hδUn : ∀ (U U' : {U : P.affineOpens // U.1 ≤ U₀}) (h : U'.1.1 ≤ U.1.1) (s : ↥(LinearMap.ker (prU U))) (s' : ↥(LinearMap.ker (prU U'))),
      (∀ m : Fin r, (s' : Fin r → Γ(P, U'.1.1)) m = SG.ρ P h ((s : Fin r → Γ(P, U.1.1)) m)) → δU U' s' = GK.res h (δU U s) :=
    chart_δUn q GE GK prU δU hprUn pr δ gU hgU hδU hspan
  refine ⟨prU, hprU, hprUs, hprUn, gU, hgU, δU, hδU, hspan, hδUn,
    fun U => inferInstance,
    fun {U U'} h => EP.linA (Scheme.TwoAffineOpenCover.algebraOfHom q U.1.1).algebraMap
      (Scheme.TwoAffineOpenCover.algebraOfHom q U'.1.1).algebraMap (SG.ρ P h) (SG.ρ_algebraMap q h)
      (Rmap q GE GK prU δU hprUn hδUn U U' h),
    fun {U U'} h a x => (Rmap q GE GK prU δU hprUn hδUn U U' h).map_smulₛₗ a x,
    fun U x => EP.resMap_self (SG.ρ P (le_refl U.1.1)) (fun b => SG.ρ_refl_apply U.1.1 b) (SG.resₛ q GK (le_refl U.1.1))
      (fun n => GK.res_refl_apply U.1.1 n) (SG.resₛ q GE (le_refl U.1.1)) (prU U) (δU U)
      (hprUn U U (le_refl U.1.1)) (hδUn U U (le_refl U.1.1)) x,
    fun {U U' U''} h h' x => EP.resMap_trans (SG.ρ P h') (SG.ρ P h) (SG.ρ P (h.trans h')) (fun b => SG.ρ_ρ h' h b)
      (SG.resₛ q GK h') (SG.resₛ q GK h) (SG.resₛ q GK (h.trans h')) (fun n => GK.res_res h h' n)
      (SG.resₛ q GE h') (SG.resₛ q GE h) (SG.resₛ q GE (h.trans h'))
      (prU U) (δU U) (prU U') (δU U') (prU U'') (δU U'')
      (hprUn U U' h') (hδUn U U' h') (hprUn U' U'' h) (hδUn U' U'' h) (hprUn U U'' (h.trans h')) (hδUn U U'' (h.trans h')) x,
    ?_, fun U => @EP.finite_extPushout _ _ _ _ _ _ _ _ (hGKc U.1) _ (prU U) (δU U),
    fun U => EP.inlA (Scheme.TwoAffineOpenCover.algebraOfHom q U.1.1) (GK.isScalarTower U.1.1) (prU U) (δU U),
    fun U => EP.projA (Scheme.TwoAffineOpenCover.algebraOfHom q U.1.1) (GE.isScalarTower U.1.1) (prU U) (δU U),
    fun U a x => map_smul (LinearMap.ExtPushout.inl (prU U) (δU U)) a x,
    fun U a x => map_smul (LinearMap.ExtPushout.proj (prU U) (δU U)) a x,
    fun U U' h x => (EP.resMap_inl (SG.ρ P h) (SG.resₛ q GK h) (SG.resₛ q GE h) (prU U) (δU U) (prU U') (δU U')
      (hprUn U U' h) (hδUn U U' h) x).symm,
    fun U U' h x => EP.proj_resMap (SG.ρ P h) (SG.resₛ q GK h) (SG.resₛ q GE h) (prU U) (δU U) (prU U') (δU U')
      (hprUn U U' h) (hδUn U U' h) x,
    fun U => EP.range_inlA_eq_ker_projA (Scheme.TwoAffineOpenCover.algebraOfHom q U.1.1) (GK.isScalarTower U.1.1)
      (GE.isScalarTower U.1.1) (prU U) (δU U),
    fun U => LinearMap.ExtPushout.proj_surjective (prU U) (δU U) (hprUs U),
    fun U => LinearMap.ExtPushout.inl_injective (prU U) (δU U),
    fun U x => rfl, fun U x => rfl, fun U U' h n => EP.resMap_inl (SG.ρ P h) (SG.resₛ q GK h) (SG.resₛ q GE h) (prU U) (δU U) (prU U') (δU U') (hprUn U U' h) (hδUn U U' h) n,
    fun U U' h v => EP.resMap_inr (SG.ρ P h) (SG.resₛ q GK h) (SG.resₛ q GE h) (prU U) (δU U) (prU U') (δU U') (hprUn U U' h) (hδUn U U' h) v⟩

  intro U Ug g hUg
  have hK := SG.qc_of_eq q GK hGKq U.1 g Ug.1.1 hUg
  have hEk := (SG.qc_of_eq q GE hGEq U.1 g Ug.1.1 hUg).2
  have locS := SG.loc_of_eq U.1 g Ug.1.1 hUg
  refine ⟨fun y => ?_, fun x hx => ?_⟩
  · obtain ⟨n, x, hx⟩ := EP.resMap_surj_upto (SG.ρ P (hUg.trans_le (P.basicOpen_le g))) (SG.resₛ q GK _) (SG.resₛ q GE _)
      (prU U) (δU U) (prU Ug) (δU Ug) (hprUn U Ug _) (hδUn U Ug _) g locS hK.1 y
    exact ⟨n, x, hx⟩
  · exact EP.resMap_ker_torsion (SG.ρ P (hUg.trans_le (P.basicOpen_le g))) (SG.resₛ q GK _) (SG.resₛ q GE _)
      (prU U) (δU U) (prU Ug) (δU Ug) (hprUn U Ug _) (hδUn U Ug _) g hK.2 hEk x hx

end S_AlgebraicGeometry_OModulePresheaf_exists_chartModel_extPushout_of_surjective
end P2MW
export P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_chartModel_extPushout_of_surjective (solution)
