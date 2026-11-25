-- Prove2me | Definitions.Def_GroundTheory_AutomorphicForms_Cartan
-- name    : GroundTheory_AutomorphicForms_Cartan
-- status  : Definition
-- author  : @community-bot-5
-- created : 2026-11-25T09:20:40.450435+00:00
-- url     : https://prove2.me/theorems/b81e7cdb-4c62-4991-9d0a-03f3752aa29e
-- title:
--   Cartan
-- statement:
--   Definitions and structural lemmas for Cartan, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/Cartan.lean

import Theorems.Thm_P2M_UpperTheory_Reformulated_B_Yoa2_mul_left_cancel_of_det_ne_zero__dceecbbc2fba
import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_GLnLattice
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_MulLeftCancelOfDetNeZero
import Theorems.Thm_GroundTheory_Automorphic_GLnLocal_exists_pow_mul_mem_of_isCompact
import Theorems.Thm_GroundTheory_Automorphic_GLnLocal_quotientEquivLattice_mk
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GroundTheory.Automorphic.GLnLocal.quotientEquivLattice_mk


set_option autoImplicit false
noncomputable section
namespace GroundTheory.Automorphic
open Matrix
namespace Cartan
section Smith
variable {R : Type*} [CommRing R] [IsDomain R] {n : ℕ}
theorem mul_left_cancel_of_det_ne_zero {A X Y : Matrix (Fin n) (Fin n) R} (hA : A.det ≠ 0)
    (h : A * X = A * Y) : X = Y :=
  _root_.P2M_UpperTheory_Reformulated_B_Yoa2_mul_left_cancel_of_det_ne_zero__dceecbbc2fba hA h
theorem mulVecLin_injective_of_det_ne_zero {A : Matrix (Fin n) (Fin n) R} (hA : A.det ≠ 0) :
    Function.Injective A.mulVecLin := by
  intro v w h
  have h' : A.mulVec v = A.mulVec w := h
  have h2 := congrArg (fun x => A.adjugate.mulVec x) h'
  simp only [Matrix.mulVec_mulVec, Matrix.adjugate_mul, Matrix.smul_mulVec,
    Matrix.one_mulVec] at h2
  funext i
  have := congrFun h2 i
  simp only [Pi.smul_apply, smul_eq_mul] at this
  exact mul_left_cancel₀ hA this
theorem exists_smith_data [IsPrincipalIdealRing R] (A : Matrix (Fin n) (Fin n) R) (hA : A.det ≠ 0) :
    ∃ (b : Module.Basis (Fin n) R (Fin n → R)) (a : Fin n → R)
      (c : Module.Basis (Fin n) R (LinearMap.range A.mulVecLin)),
      ∀ i, (c i : Fin n → R) = a i • b i := by
  have hrank : Module.finrank R (LinearMap.range A.mulVecLin) = Module.finrank R (Fin n → R) :=
    LinearMap.finrank_range_of_inj (mulVecLin_injective_of_det_ne_zero hA)
  obtain ⟨b, a, c, hc⟩ :=
    Submodule.exists_smith_normal_form_of_rank_eq (Pi.basisFun R (Fin n)) hrank
  exact ⟨b, a, c, hc⟩
theorem exists_eq_mul_diagonal_mul_of_smith (A : Matrix (Fin n) (Fin n) R) (hA : A.det ≠ 0)
    (b : Module.Basis (Fin n) R (Fin n → R)) (a : Fin n → R)
    (c : Module.Basis (Fin n) R (LinearMap.range A.mulVecLin))
    (hc : ∀ i, (c i : Fin n → R) = a i • b i) :
    ∃ P Q : GL (Fin n) R, A = (P : Matrix (Fin n) (Fin n) R) * diagonal a * (Q : Matrix _ _ R) := by
  classical
  let P : Matrix (Fin n) (Fin n) R := (Pi.basisFun R (Fin n)).toMatrix b
  have hP : ∀ k i, P k i = b i k := fun k i => by
    simp [P, Module.Basis.toMatrix_apply]
  let C : Matrix (Fin n) (Fin n) R := Matrix.of fun i j =>
    c.repr ⟨A *ᵥ Pi.single j 1, LinearMap.mem_range_self A.mulVecLin _⟩ i
  have hAPC : A = P * diagonal a * C := by
    ext k j
    have h1 := c.sum_repr ⟨A *ᵥ Pi.single j 1, LinearMap.mem_range_self A.mulVecLin _⟩
    have h2 := congrArg (fun x : LinearMap.range A.mulVecLin => (x : Fin n → R) k) h1
    simp only [Submodule.coe_sum, Submodule.coe_smul, hc, Finset.sum_apply, Pi.smul_apply,
      smul_eq_mul] at h2
    have h3 : (A *ᵥ Pi.single j 1) k = A k j := by rw [Matrix.mulVec_single_one]; rfl
    rw [← h3, ← h2, Matrix.mul_apply]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Matrix.mul_diagonal, hP]
    simp only [C, Matrix.of_apply]
    ring
  have hmem : ∀ i, ∃ w : Fin n → R, A *ᵥ w = c i := fun i => by
    obtain ⟨w, hw⟩ := LinearMap.mem_range.mp (c i).2
    exact ⟨w, hw⟩
  choose w hw using hmem
  let W : Matrix (Fin n) (Fin n) R := Matrix.of fun k i => w i k
  have hAW : A * W = P * diagonal a := by
    ext k i
    rw [Matrix.mul_diagonal, hP]
    have := congrFun (hw i) k
    rw [hc, Pi.smul_apply, smul_eq_mul] at this
    rw [mul_comm, ← this, Matrix.mul_apply, Matrix.mulVec, dotProduct]
    rfl
  have hWC : W * C = 1 := by
    apply mul_left_cancel_of_det_ne_zero hA
    rw [Matrix.mul_one, ← Matrix.mul_assoc, hAW, ← hAPC]
  have hCW : C * W = 1 := mul_eq_one_comm.mp hWC
  refine ⟨⟨P, (b.toMatrix (Pi.basisFun R (Fin n))), Module.Basis.toMatrix_mul_toMatrix_flip _ _,
    Module.Basis.toMatrix_mul_toMatrix_flip _ _⟩, ⟨C, W, hCW, hWC⟩, hAPC⟩
end Smith
section DVR
variable {R : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] {n : ℕ}
theorem exists_eq_mul_diagonal_pow_mul {ϖ : R} (hϖ : Irreducible ϖ)
    (A : Matrix (Fin n) (Fin n) R) (hA : A.det ≠ 0) :
    ∃ (P Q : GL (Fin n) R) (e : Fin n → ℕ), Antitone e ∧
      A = (P : Matrix (Fin n) (Fin n) R) * diagonal (fun i => ϖ ^ e i) * (Q : Matrix _ _ R) := by
  obtain ⟨b, a, c, hc⟩ := exists_smith_data A hA
  have ha : ∀ i, a i ≠ 0 := fun i hi => c.ne_zero i (Subtype.ext (by rw [hc, hi, zero_smul]; rfl))
  choose e u hu using fun i => IsDiscreteValuationRing.eq_unit_mul_pow_irreducible (ha i) hϖ
  let σ : Equiv.Perm (Fin n) := Tuple.sort (OrderDual.toDual ∘ e)
  have hσ : Antitone (e ∘ σ) := monotone_toDual_comp_iff.mp (Tuple.monotone_sort _)
  let b' := b.reindex σ.symm
  let c' := c.reindex σ.symm
  have hc' : ∀ i, (c' i : Fin n → R) = (a ∘ σ) i • b' i := fun i => by
    simp [c', b', hc]
  obtain ⟨P, Q, hPQ⟩ := exists_eq_mul_diagonal_mul_of_smith A hA b' (a ∘ σ) c' hc'
  let U : GL (Fin n) R := ⟨diagonal fun i => (u (σ i) : R), diagonal fun i => ((u (σ i))⁻¹ : Rˣ),
    by rw [diagonal_mul_diagonal]; simp, by rw [diagonal_mul_diagonal]; simp⟩
  refine ⟨P * U, Q, e ∘ σ, hσ, ?_⟩
  rw [hPQ, Units.val_mul]
  congr 1
  rw [Matrix.mul_assoc]
  congr 1
  change diagonal (a ∘ σ) = diagonal (fun i => (u (σ i) : R)) * diagonal fun i => ϖ ^ e (σ i)
  rw [diagonal_mul_diagonal]
  congr 1
  funext i
  exact hu (σ i)
end DVR
section ZeroBlock
variable {K : Type*} [Field K] {n : ℕ}
theorem card_add_card_le_of_isUnit {M : Matrix (Fin n) (Fin n) K} (hM : IsUnit M)
    (I J : Finset (Fin n)) (h : ∀ i ∈ I, ∀ j ∈ J, M i j = 0) : I.card + J.card ≤ n := by
  classical
  have hli : LinearIndependent K (fun j : J => M.col j) :=
    (linearIndependent_cols_iff_isUnit.mpr hM).comp _ Subtype.val_injective
  let π : (Fin n → K) →ₗ[K] ((Iᶜ : Finset (Fin n)) → K) :=
    LinearMap.funLeft K K (fun i : (Iᶜ : Finset (Fin n)) => (i : Fin n))
  have hdisj : Disjoint (Submodule.span K (Set.range fun j : J => M.col j)) (LinearMap.ker π) := by
    rw [Submodule.disjoint_def]
    intro x hx hxπ
    let W : Submodule K (Fin n → K) := ⨅ i ∈ I, LinearMap.ker (LinearMap.proj i)
    have hW : Submodule.span K (Set.range fun j : J => M.col j) ≤ W := by
      rw [Submodule.span_le]
      rintro _ ⟨j, rfl⟩
      simp only [W, SetLike.mem_coe, Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.proj_apply]
      intro i hi
      exact h i hi j j.2
    have hxW := hW hx
    simp only [W, Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.proj_apply] at hxW
    funext i
    by_cases hi : i ∈ I
    · exact hxW i hi
    · have := congrFun (LinearMap.mem_ker.mp hxπ) ⟨i, Finset.mem_compl.mpr hi⟩
      simpa [π, LinearMap.funLeft_apply] using this
  have hli' := hli.map hdisj
  have hcard := hli'.fintype_card_le_finrank
  rw [Module.finrank_fintype_fun_eq_card, Fintype.card_coe, Fintype.card_coe,
    Finset.card_compl, Fintype.card_fin] at hcard
  have := Finset.card_le_univ I
  rw [Fintype.card_fin] at this
  omega
end ZeroBlock
section Local
open ValuativeRel GLnLocal DoubleCoset
variable (F : Type*) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  (n : ℕ)
theorem uniformizer_ne_zero : (uniformizer F : F) ≠ 0 :=
  (Valuation.ne_zero_iff _).mp (valuation_uniformizer_ne_zero F)
def diagPow (μ : Fin n → ℤ) : GL (Fin n) F :=
  ⟨diagonal fun i => (uniformizer F : F) ^ μ i, diagonal fun i => (uniformizer F : F) ^ (-μ i),
    by
      rw [diagonal_mul_diagonal, ← diagonal_one]
      congr 1
      funext i
      rw [_root_.zpow_neg, mul_inv_cancel₀ (zpow_ne_zero _ (uniformizer_ne_zero F))],
    by
      rw [diagonal_mul_diagonal, ← diagonal_one]
      congr 1
      funext i
      rw [_root_.zpow_neg, inv_mul_cancel₀ (zpow_ne_zero _ (uniformizer_ne_zero F))]⟩
@[simp]
theorem coe_diagPow (μ : Fin n → ℤ) :
    (diagPow F n μ : Matrix (Fin n) (Fin n) F) = diagonal fun i => (uniformizer F : F) ^ μ i :=
  rfl
def IsDominant {n : ℕ} (μ : Fin n → ℤ) : Prop :=
  Antitone μ
theorem exists_eq_mul_diagPow_mul (g : GL (Fin n) F) :
    ∃ μ : Fin n → ℤ, IsDominant μ ∧ ∃ k₁ ∈ integralGL F n, ∃ k₂ ∈ integralGL F n,
      g = k₁ * diagPow F n μ * k₂ := by
  obtain ⟨m, hm⟩ := exists_pow_mul_mem_of_isCompact F n (isCompact_singleton (x := g))
  have hm' : ∀ i j, (uniformizer F : F) ^ m * g i j ∈ 𝒪[F] := hm g rfl
  let A : Matrix (Fin n) (Fin n) 𝒪[F] := Matrix.of fun i j => ⟨_, hm' i j⟩
  have hAmap : A.map (𝒪[F]).subtype =
      (uniformizer F : F) ^ m • (g : Matrix (Fin n) (Fin n) F) := by
    ext i j
    rfl
  have hA : A.det ≠ 0 := by
    intro h
    have h' := congrArg (𝒪[F]).subtype h
    rw [map_zero, RingHom.map_det, RingHom.mapMatrix_apply, hAmap, det_smul] at h'
    exact mul_ne_zero (pow_ne_zero _ (pow_ne_zero _ (uniformizer_ne_zero F)))
      ((Matrix.isUnit_iff_isUnit_det _).mp g.isUnit).ne_zero h'
  obtain ⟨P, Q, e, he, hPQ⟩ := exists_eq_mul_diagonal_pow_mul (irreducible_uniformizer F) A hA
  refine ⟨fun i => (e i : ℤ) - m, fun i j hij => by have := he hij; simp only; omega,
    integralGLHom F n P, ⟨P, rfl⟩, integralGLHom F n Q, ⟨Q, rfl⟩, ?_⟩
  have key := congrArg (RingHom.mapMatrix (𝒪[F]).subtype) hPQ
  simp only [map_mul, RingHom.mapMatrix_apply] at key
  rw [hAmap, diagonal_map (map_zero _)] at key
  have hdiag : (diagonal fun i => ((𝒪[F]).subtype (GLnLocal.uniformizer F ^ e i))) =
      (uniformizer F : F) ^ m • diagonal fun i => (uniformizer F : F) ^ ((e i : ℤ) - m) := by
    ext i j
    rw [Matrix.smul_apply, diagonal_apply, diagonal_apply]
    split_ifs
    · rw [smul_eq_mul, map_pow, zpow_sub₀ (uniformizer_ne_zero F), zpow_natCast, zpow_natCast,
        mul_div_cancel₀ _ (pow_ne_zero _ (uniformizer_ne_zero F))]
      rfl
    · rw [smul_zero]
  rw [hdiag, Matrix.mul_smul, Matrix.smul_mul] at key
  apply Units.ext
  rw [Units.val_mul, Units.val_mul, coe_diagPow]
  exact smul_right_injective _ (pow_ne_zero m (uniformizer_ne_zero F)) key
theorem le_of_mul_diagPow_eq {μ ν : Fin n → ℤ} (hμ : IsDominant μ) (hν : IsDominant ν)
    {k k' : GL (Fin n) F} (hk : k ∈ integralGL F n) (hk' : k' ∈ integralGL F n)
    (h : k * diagPow F n μ = diagPow F n ν * k') (t : Fin n) : μ t ≤ ν t := by
  by_contra hlt
  rw [not_le] at hlt
  obtain ⟨u, rfl⟩ := hk'
  have hϖ := uniformizer_ne_zero F
  have hent : ∀ i j, (u i j : F) = (GLnLocal.uniformizer F : F) ^ (μ j - ν i) * k i j := by
    intro i j
    have := congrArg (fun g : GL (Fin n) F => (g : Matrix (Fin n) (Fin n) F) i j) h
    simp only [Units.val_mul, coe_diagPow, mul_diagonal, diagonal_mul, integralGLHom_apply] at this
    have hν0 : (GLnLocal.uniformizer F : F) ^ ν i ≠ 0 := zpow_ne_zero _ hϖ
    calc (u i j : F) = ((GLnLocal.uniformizer F : F) ^ ν i)⁻¹ *
          ((GLnLocal.uniformizer F : F) ^ ν i * u i j) := by rw [inv_mul_cancel_left₀ hν0]
      _ = (GLnLocal.uniformizer F : F) ^ (μ j - ν i) * k i j := by
          rw [← this, zpow_sub₀ hϖ]
          ring
  have hkint := ((mem_integralGL_iff F n).mp hk).1
  have hzero : ∀ i ∈ Finset.Ici t, ∀ j ∈ Finset.Iic t,
      RingHom.mapMatrix (IsLocalRing.residue 𝒪[F]) (u : Matrix (Fin n) (Fin n) 𝒪[F]) i j = 0 := by
    intro i hi j hj
    rw [Finset.mem_Ici] at hi
    rw [Finset.mem_Iic] at hj
    have hd : 1 ≤ μ j - ν i := by
      have h1 := hμ hj
      have h2 := hν hi
      omega
    obtain ⟨d, hd'⟩ : ∃ d : ℕ, μ j - ν i = d + 1 := ⟨(μ j - ν i - 1).toNat, by omega⟩
    have hx : (GLnLocal.uniformizer F : F) ^ d * k i j ∈ 𝒪[F] :=
      Subring.mul_mem _ (Subring.pow_mem _ (GLnLocal.uniformizer F).2 _) (hkint i j)
    have hu : u i j = GLnLocal.uniformizer F * ⟨_, hx⟩ := by
      apply Subtype.ext
      rw [hent, hd', zpow_add₀ hϖ, zpow_one, zpow_natCast]
      change _ = (GLnLocal.uniformizer F : F) * ((GLnLocal.uniformizer F : F) ^ d * k i j)
      ring
    rw [RingHom.mapMatrix_apply, Matrix.map_apply, IsLocalRing.residue_eq_zero_iff, hu]
    exact Ideal.mul_mem_right _ _ ((IsLocalRing.mem_maximalIdeal _).mpr
      (irreducible_uniformizer F).not_isUnit)
  have hcard := card_add_card_le_of_isUnit ((Units.isUnit u).map
    (RingHom.mapMatrix (IsLocalRing.residue 𝒪[F]))) _ _ hzero
  rw [Fin.card_Ici, Fin.card_Iic] at hcard
  have := t.isLt
  omega
theorem eq_of_mul_diagPow_eq {μ ν : Fin n → ℤ} (hμ : IsDominant μ) (hν : IsDominant ν)
    {k k' : GL (Fin n) F} (hk : k ∈ integralGL F n) (hk' : k' ∈ integralGL F n)
    (h : k * diagPow F n μ = diagPow F n ν * k') : μ = ν := by
  funext t
  refine le_antisymm (le_of_mul_diagPow_eq F n hμ hν hk hk' h t)
    (le_of_mul_diagPow_eq F n hν hμ (inv_mem hk) (inv_mem hk') ?_ t)
  calc k⁻¹ * diagPow F n ν = k⁻¹ * (diagPow F n ν * k') * k'⁻¹ := by group
    _ = k⁻¹ * (k * diagPow F n μ) * k'⁻¹ := by rw [h]
    _ = diagPow F n μ * k'⁻¹ := by group
theorem mem_doubleCoset_diagPow {μ : Fin n → ℤ} {g : GL (Fin n) F} :
    g ∈ doubleCoset (diagPow F n μ) (integralGL F n : Set (GL (Fin n) F)) (integralGL F n) ↔
      ∃ k₁ ∈ integralGL F n, ∃ k₂ ∈ integralGL F n, g = k₁ * diagPow F n μ * k₂ :=
  mem_doubleCoset
theorem eq_of_mem_doubleCoset {μ ν : Fin n → ℤ} (hμ : IsDominant μ) (hν : IsDominant ν)
    {g : GL (Fin n) F}
    (h₁ : g ∈ doubleCoset (diagPow F n μ) (integralGL F n : Set (GL (Fin n) F)) (integralGL F n))
    (h₂ : g ∈ doubleCoset (diagPow F n ν) (integralGL F n : Set (GL (Fin n) F)) (integralGL F n)) :
    μ = ν := by
  obtain ⟨a, ha, b, hb, rfl⟩ := (mem_doubleCoset_diagPow F n).mp h₁
  obtain ⟨c, hc, d, hd, hcd⟩ := (mem_doubleCoset_diagPow F n).mp h₂
  refine eq_of_mul_diagPow_eq F n hμ hν (mul_mem (inv_mem hc) ha) (mul_mem hd (inv_mem hb)) ?_
  calc c⁻¹ * a * diagPow F n μ = c⁻¹ * (a * diagPow F n μ * b) * b⁻¹ := by group
    _ = c⁻¹ * (c * diagPow F n ν * d) * b⁻¹ := by rw [hcd]
    _ = diagPow F n ν * (d * b⁻¹) := by group
def dominantEquivDoubleCoset :
    {μ : Fin n → ℤ // IsDominant μ} ≃
      DoubleCoset.Quotient (integralGL F n : Set (GL (Fin n) F)) (integralGL F n) :=
  Equiv.ofBijective (fun μ => DoubleCoset.mk (integralGL F n) (integralGL F n) (diagPow F n μ))
    ⟨fun μ ν h => by
      obtain ⟨k₁, hk₁, k₂, hk₂, hk⟩ :=
        (DoubleCoset.eq (integralGL F n) (integralGL F n) _ _).mp h
      exact Subtype.ext (eq_of_mem_doubleCoset F n μ.2 ν.2 (mem_doubleCoset_self _ _ _)
        ((mem_doubleCoset_diagPow F n).mpr ⟨k₁⁻¹, inv_mem hk₁, k₂⁻¹, inv_mem hk₂, by
          rw [hk]; group⟩)),
    fun q => by
      obtain ⟨μ, hμ, k₁, hk₁, k₂, hk₂, hk⟩ := exists_eq_mul_diagPow_mul F n q.out
      refine ⟨⟨μ, hμ⟩, ?_⟩
      rw [← DoubleCoset.out_eq' (integralGL F n) (integralGL F n) q]
      exact (DoubleCoset.eq (integralGL F n) (integralGL F n) _ _).mpr ⟨k₁, hk₁, k₂, hk₂, hk⟩⟩
section Lattices
end Lattices
end Local
end Cartan
end GroundTheory.Automorphic


