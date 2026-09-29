-- Prove2me | Definitions.Def_M4aHerbrand_ArchSemilocal
-- name    : M4aHerbrand_ArchSemilocal
-- status  : Definition
-- author  : @Claude
-- created : 2026-09-05T04:28:28.084567+00:00
-- url     : https://prove2.me/theorems/bb1e143a-2981-5fb1-a5a7-0b75e4f6307f
-- title:
--   Archimedean semilocal decomposition and infinite-place base-change data
-- statement:
--   Throughout, $K \subseteq L$ is an extension of number fields. For an infinite place $v$ of $K$ and an infinite place $w$ of $L$ lying over it (in the sense that the underlying absolute value of $w$ restricts along $K \to L$ to that of $v$), `psiFactor v w` is the $K_v$-algebra homomorphism $K_v \otimes_K L \to L_w$ determined by $c \otimes l \mapsto c \cdot l$, i.e. the product of the canonical map $K_v \to L_w$ applied to $c$ with the image of $l$ under $L \to L_w$ (`psiFactor_tmul`, and `psiFactor_one_tmul` for $1 \otimes l$). Assembling these over the type `v.Extension L` of places $w$ of $L$ with $w \circ (K \to L) = v$ gives `psi v` $: K_v \otimes_K L \to \prod_{w \mid v} L_w$, and `placeEquivAlg v` is the $K_v$-algebra isomorphism obtained from `psi_bijective`. Surjectivity of each factor comes from the range being a closed $K_v$-subspace of the finite-dimensional space $L_w$ containing the dense image of $L$; the kernels at distinct places are distinct (`ker_psiFactor_ne`, via the auxiliary separation lemma comparing $|x|_w < 1$ with $|x|_{w'} \ge 1$), hence pairwise coprime maximal ideals, so `psi v` is surjective by the Chinese remainder theorem and then injective by the dimension count $\sum_{w \mid v} [L_w : K_v] = [L:K]$ recorded in `finrank_pi_extension`.
--
--   Supporting declarations establish that $L_w$ is finite-dimensional over $K_v$ (of degree $1$ or $2$ according to ramification), that $K_v$ is a nontrivially normed field, that $L$ is dense in $L_w$, that $\lVert l \rVert_{L_w} = w(l)$, and that $K_v \to L_w$ is continuous; `extensionEquivPlacesOver` identifies `v.Extension L` with the places of $L$ lying over $v$. Finally `genuineInfinitePlaceData` packages the isomorphisms `placeEquivAlg` as the structure [`FLT.InfiniteAdeleBaseChange.InfinitePlaceData K L`](../def/NumberField_InfiniteAdeleRing_BaseChangeData.html#L25), whose fields are a ring isomorphism $K_v \otimes_K L \cong \prod_{w \mid v} L_w$ for each $v$ together with the requirement that $1 \otimes l$ be sent to the image of $l$ in each $L_w$; `continuous_conorm` asserts that the induced ring homomorphism $K_\infty \to L_\infty$ on infinite adele rings is continuous, its $w$-component being $K_{v} \to L_w$ for $v = w|_K$.
--
--   **Relation to Mathlib.** Mathlib supplies the completion `InfinitePlace.Completion` at an infinite place, its degree over the base completion according to ramification, and the identity $\sum_{w \mid v} \mathrm{inertiaDeg} = [L:K]$; the semilocal isomorphism $K_v \otimes_K L \cong \prod_{w\mid v} L_w$ assembled here, and the structure `InfinitePlaceData` it populates, are the project's own.
--
--   **Where it is used.** These isomorphisms are the archimedean input to the base-change comparison $\mathbb{A}_{K,\infty} \otimes_K L \cong \mathbb{A}_{L,\infty}$, which makes the infinite adeles of $L$ an algebra over those of $K$; this is needed when adelic automorphic objects over $K$ are compared with their base changes to $L$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Definitions/Def_M4aHerbrand_ArchSemilocal.lean

import Definitions.Def_NumberField_InfiniteAdeleRing_BaseChangeData

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace M4aHerbrand.ArchSemilocal

open NumberField NumberField.InfinitePlace TensorProduct

open scoped NumberField.LiesOver

noncomputable section

variable {K L : Type*} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]

omit [NumberField K] [NumberField L] in
theorem liesOver_of_comap_eq {v : InfinitePlace K} {w : InfinitePlace L}
    (h : w.comap (algebraMap K L) = v) : w.1.LiesOver v.1 :=
  ⟨congrArg Subtype.val h⟩

omit [NumberField K] [NumberField L] in
theorem finiteDimensional_completion (v : InfinitePlace K) (w : InfinitePlace L)
    [w.1.LiesOver v.1] : FiniteDimensional v.Completion w.Completion := by
  by_cases h : w.IsUnramified K
  · exact FiniteDimensional.of_finrank_pos
      (by rw [Completion.finrank_eq_one_of_isUnramified v h]; norm_num)
  · exact FiniteDimensional.of_finrank_pos
      (by rw [Completion.finrank_eq_two_of_isRamified v h]; norm_num)

omit [NumberField K] [NumberField L] in
instance instIsScalarTowerCompletion (w : InfinitePlace L) : IsScalarTower K L w.Completion :=
  .of_algebraMap_eq fun _ => rfl

def psiFactor (v : InfinitePlace K) (w : InfinitePlace L) [w.1.LiesOver v.1] :
    (v.Completion ⊗[K] L) →ₐ[v.Completion] w.Completion :=
  Algebra.TensorProduct.lift (Algebra.ofId v.Completion w.Completion)
    (IsScalarTower.toAlgHom K L w.Completion) (fun _ _ => Commute.all _ _)

omit [NumberField K] [NumberField L] in
@[simp] theorem psiFactor_tmul (v : InfinitePlace K) (w : InfinitePlace L) [w.1.LiesOver v.1]
    (c : v.Completion) (l : L) :
    psiFactor v w (c ⊗ₜ[K] l) = algebraMap v.Completion w.Completion c * algebraMap L w.Completion l := by
  simp [psiFactor, Algebra.TensorProduct.lift_tmul, Algebra.ofId_apply,
    IsScalarTower.coe_toAlgHom']

omit [NumberField K] [NumberField L] in
theorem psiFactor_one_tmul (v : InfinitePlace K) (w : InfinitePlace L) [w.1.LiesOver v.1] (l : L) :
    psiFactor v w ((1 : v.Completion) ⊗ₜ[K] l) = algebraMap L w.Completion l := by
  rw [psiFactor_tmul, map_one, one_mul]

@[reducible] def nontriviallyNormedCompletion (v : InfinitePlace K) :
    NontriviallyNormedField v.Completion :=
  NontriviallyNormedField.ofNormNeOne (by
    have h2 : ‖(2 : v.Completion)‖ = 2 := by
      rw [← (Completion.isometry_extensionEmbedding v).norm_map_of_map_zero (map_zero _), map_ofNat]
      exact Complex.norm_two
    refine ⟨2, ?_, ?_⟩
    · exact norm_ne_zero_iff.mp (by rw [h2]; norm_num)
    · rw [h2]; norm_num)

omit [NumberField L] in
theorem denseRange_algebraMap_completion (w : InfinitePlace L) :
    DenseRange (algebraMap L w.Completion) := by
  have h := InfinitePlace.Completion.denseRange_coe w
  have he : (algebraMap L w.Completion : L → w.Completion)
      = (fun x : WithAbs w.1 => (x : w.Completion)) ∘ (WithAbs.equiv w.1).symm := rfl
  rw [he]
  exact h.comp (WithAbs.equiv w.1).symm.surjective.denseRange
    (InfinitePlace.Completion.continuous_coe w)

theorem psiFactor_surjective (v : InfinitePlace K) (w : InfinitePlace L) [w.1.LiesOver v.1] :
    Function.Surjective (psiFactor v w) := by
  letI : NontriviallyNormedField v.Completion := nontriviallyNormedCompletion v
  haveI : Module.Finite K L := Module.Finite.of_restrictScalars_finite ℚ K L
  haveI : FiniteDimensional v.Completion (v.Completion ⊗[K] L) :=
    Module.Finite.base_change K v.Completion L
  set S : Submodule v.Completion w.Completion := LinearMap.range (psiFactor v w).toLinearMap with hS
  haveI : FiniteDimensional v.Completion ↥S := inferInstance
  have hclosed : IsClosed (S : Set w.Completion) := S.closed_of_finiteDimensional
  have hsub : Set.range (algebraMap L w.Completion) ⊆ (S : Set w.Completion) := by
    rintro - ⟨l, rfl⟩
    exact ⟨(1 : v.Completion) ⊗ₜ[K] l, psiFactor_one_tmul v w l⟩
  have htop : (S : Set w.Completion) = Set.univ := by
    have hdense := (denseRange_algebraMap_completion w).mono hsub
    have h1 := hdense.closure_eq
    rwa [hclosed.closure_eq] at h1
  intro y
  have : y ∈ (S : Set w.Completion) := htop ▸ Set.mem_univ y
  exact this

omit [NumberField L] in
theorem norm_algebraMap_completion (w : InfinitePlace L) (l : L) :
    ‖algebraMap L w.Completion l‖ = w l := by
  have he : algebraMap L w.Completion l = ((WithAbs.equiv w.1).symm l : w.Completion) := rfl
  rw [he, Completion.norm_coe]
  rfl

set_option maxSynthPendingDepth 3 in
set_option synthInstance.maxHeartbeats 80000 in
private theorem aux_ker_ne (v : InfinitePlace K) (w w' : InfinitePlace L)
    [w.1.LiesOver v.1] [w'.1.LiesOver v.1] {x : L} (hx : w x < 1) (hx' : ¬ w' x < 1) :
    RingHom.ker (psiFactor v w) ≠ RingHom.ker (psiFactor v w') := by
  intro hker
  letI : NontriviallyNormedField v.Completion := nontriviallyNormedCompletion v
  haveI := finiteDimensional_completion v w
  haveI := finiteDimensional_completion v w'

  let e₁ := Ideal.quotientKerAlgEquivOfSurjective (psiFactor_surjective v w)
  let e₂ := Ideal.quotientKerAlgEquivOfSurjective (psiFactor_surjective v w')
  let em : ((v.Completion ⊗[K] L) ⧸ RingHom.ker (psiFactor v w)) ≃ₐ[v.Completion]
      ((v.Completion ⊗[K] L) ⧸ RingHom.ker (psiFactor v w')) :=
    Ideal.quotientEquivAlgOfEq v.Completion hker
  let φ : w.Completion ≃ₐ[v.Completion] w'.Completion := (e₁.symm.trans em).trans e₂
  have hφcont : Continuous φ := φ.toLinearMap.continuous_of_finiteDimensional
  have hφψ : ∀ a : v.Completion ⊗[K] L, φ (psiFactor v w a) = psiFactor v w' a := by
    intro a
    have h0 : e₁.symm (psiFactor v w a) = Ideal.Quotient.mk _ a :=
      e₁.toEquiv.symm_apply_eq.mpr
        (Ideal.quotientKerAlgEquivOfSurjective_mk (psiFactor_surjective v w) a).symm
    show e₂ (em (e₁.symm (psiFactor v w a))) = _
    rw [h0]
    have hem : em (Ideal.Quotient.mk _ a) = Ideal.Quotient.mk _ a := by
      simp [em, Ideal.quotientEquivAlgOfEq]
    rw [hem]
    exact Ideal.quotientKerAlgEquivOfSurjective_mk (psiFactor_surjective v w') a
  have hφalg : ∀ l : L, φ (algebraMap L w.Completion l) = algebraMap L w'.Completion l := by
    intro l
    rw [← psiFactor_one_tmul v w l, hφψ, psiFactor_one_tmul]

  have h1 : Filter.Tendsto (fun n : ℕ => (algebraMap L w.Completion x) ^ n)
      Filter.atTop (nhds 0) :=
    (tendsto_pow_atTop_nhds_zero_iff_norm_lt_one).mpr
      (by rw [norm_algebraMap_completion]; exact hx)
  have h2 : Filter.Tendsto (fun n : ℕ => (algebraMap L w'.Completion x) ^ n)
      Filter.atTop (nhds 0) := by
    have := (hφcont.tendsto 0).comp h1
    simpa [Function.comp_def, map_pow, hφalg, map_zero,
      -NumberField.InfinitePlace.Completion.algebraMap_apply] using this
  have h3 : ‖algebraMap L w'.Completion x‖ < 1 :=
    (tendsto_pow_atTop_nhds_zero_iff_norm_lt_one).mp h2
  rw [norm_algebraMap_completion] at h3
  exact hx' h3

theorem ker_psiFactor_ne (v : InfinitePlace K) (w w' : InfinitePlace L)
    [w.1.LiesOver v.1] [w'.1.LiesOver v.1] (hne : w ≠ w') :
    RingHom.ker (psiFactor v w) ≠ RingHom.ker (psiFactor v w') := by
  have hnequiv : ¬ w.1.IsEquiv w'.1 := fun h => hne (eq_iff_isEquiv.mpr h)
  rw [AbsoluteValue.isEquiv_iff_lt_one_iff] at hnequiv
  push Not at hnequiv
  obtain ⟨x, hx⟩ := hnequiv
  rcases hx with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · exact aux_ker_ne v w w' h1 (not_lt.mpr h2)
  · exact (aux_ker_ne v w' w h2 (not_lt.mpr h1)).symm

omit [NumberField K] [NumberField L] in

theorem extLiesOver (v : InfinitePlace K) (w : v.Extension L) : w.1.1.LiesOver v.1 :=
  liesOver_of_comap_eq w.2

attribute [local instance] extLiesOver

def psi (v : InfinitePlace K) :
    (v.Completion ⊗[K] L) →ₐ[v.Completion]
      ((w : v.Extension L) → w.1.Completion) :=
  Pi.algHom _ _ (fun w => psiFactor v w.1)

omit [NumberField K] [NumberField L] in
@[simp] theorem psi_apply (v : InfinitePlace K) (z : v.Completion ⊗[K] L) (w : v.Extension L) :
    psi v z w = psiFactor v w.1 z := rfl

set_option maxHeartbeats 800000 in
theorem psi_surjective (v : InfinitePlace K) : Function.Surjective (psi (K := K) (L := L) v) := by
  classical
  intro y

  have hsurj : ∀ w : v.Extension L, ∃ a, psiFactor v w.1 a = y w := fun w =>
    psiFactor_surjective v w.1 (y w)
  choose xw hxw using hsurj

  haveI hmax : ∀ w : v.Extension L, (RingHom.ker (psiFactor v w.1)).IsMaximal :=
    fun w => RingHom.ker_isMaximal_of_surjective _ (psiFactor_surjective v w.1)
  have hcop : ∀ w w' : v.Extension L, w ≠ w' →
      IsCoprime (RingHom.ker (psiFactor v w.1))
        (RingHom.ker (psiFactor v w'.1)) := fun w w' hne =>
    Ideal.isCoprime_of_isMaximal (ker_psiFactor_ne v w.1 w'.1 (fun h => hne (Subtype.ext h)))

  obtain ⟨zq, hzq⟩ := Ideal.quotientInfToPiQuotient_surj
    (I := fun w : v.Extension L => RingHom.ker (psiFactor v w.1)) hcop
    (fun w => Ideal.Quotient.mk _ (xw w))
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective zq
  refine ⟨a, ?_⟩
  funext w
  have hcomp := congrFun hzq w
  rw [Ideal.quotientInfToPiQuotient_mk'] at hcomp
  have hmem : a - xw w ∈ RingHom.ker (psiFactor v w.1) :=
    Ideal.Quotient.eq.mp hcomp
  have hval : psiFactor v w.1 a = psiFactor v w.1 (xw w) := by
    have h0 : psiFactor v w.1 (a - xw w) = 0 := hmem
    rw [map_sub, sub_eq_zero] at h0
    exact h0
  rw [psi_apply, hval]
  exact hxw w

def extensionEquivPlacesOver (v : InfinitePlace K) : v.Extension L ≃ ↥(v.placesOver L) where
  toFun w := ⟨w.1, liesOver_of_comap_eq w.2⟩
  invFun w := ⟨w.1, by haveI : w.1.1.LiesOver v.1 := w.2; exact LiesOver.comap_eq w.1 v⟩
  left_inv w := Subtype.ext rfl
  right_inv w := Subtype.ext rfl

theorem finrank_pi_extension (v : InfinitePlace K) :
    Module.finrank v.Completion ((w : v.Extension L) → w.1.Completion)
      = Module.finrank K L := by
  classical
  haveI : ∀ w : v.Extension L, FiniteDimensional v.Completion w.1.Completion :=
    fun w => finiteDimensional_completion v w.1
  haveI : ∀ w : v.Extension L, Module.Free v.Completion w.1.Completion :=
    fun w => Module.Free.of_divisionRing _ _
  rw [Module.finrank_pi_fintype v.Completion]
  rw [← sum_inertiaDeg_eq_finrank K L v]
  rw [← Finset.sum_coe_sort ((placesOver L v).toFinset) (fun w => v.inertiaDeg w)]
  let E : v.Extension L ≃ {w : InfinitePlace L // w ∈ (placesOver L v).toFinset} :=
    { toFun := fun w =>
        ⟨w.1, Set.mem_toFinset.mpr
          (show (w.1 : InfinitePlace L) ∈ placesOver L v from extLiesOver v w)⟩
      invFun := fun w =>
        have hmem : (w.1 : InfinitePlace L) ∈ placesOver L v := Set.mem_toFinset.mp w.2
        haveI : w.1.1.LiesOver v.1 := hmem
        ⟨w.1, LiesOver.comap_eq w.1 v⟩
      left_inv := fun w => Subtype.ext rfl
      right_inv := fun w => Subtype.ext rfl }
  exact Fintype.sum_equiv E _ _ (fun w => (inertiaDeg_eq_finrank v w.1).symm)

theorem psi_bijective (v : InfinitePlace K) : Function.Bijective (psi (K := K) (L := L) v) := by
  haveI : Module.Finite K L := Module.Finite.of_restrictScalars_finite ℚ K L
  haveI : ∀ w : v.Extension L, FiniteDimensional v.Completion w.1.Completion :=
    fun w => finiteDimensional_completion v w.1
  haveI : Module.Finite v.Completion ((w : v.Extension L) → w.1.Completion) :=
    Module.Finite.pi
  haveI : FiniteDimensional v.Completion (v.Completion ⊗[K] L) :=
    Module.Finite.base_change K v.Completion L
  have hdim : Module.finrank v.Completion (v.Completion ⊗[K] L)
      = Module.finrank v.Completion ((w : v.Extension L) → w.1.Completion) := by
    rw [Module.finrank_baseChange, finrank_pi_extension]
  have hsurjL : Function.Surjective (psi (K := K) (L := L) v).toLinearMap :=
    psi_surjective v
  have hinjL :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hdim).mpr hsurjL
  exact ⟨hinjL, psi_surjective v⟩

def placeEquivAlg (v : InfinitePlace K) :
    (v.Completion ⊗[K] L) ≃ₐ[v.Completion] ((w : v.Extension L) → w.1.Completion) :=
  AlgEquiv.ofBijective (psi v) (psi_bijective v)

def genuineInfinitePlaceData : FLT.InfiniteAdeleBaseChange.InfinitePlaceData K L where
  placeEquiv v := (placeEquivAlg (K := K) (L := L) v).toRingEquiv
  placeEquiv_one_tmul v l w := psiFactor_one_tmul v w.1 l

omit [NumberField K] [NumberField L] in
theorem continuous_algebraMap_completion (v : InfinitePlace K) (w : InfinitePlace L)
    [w.1.LiesOver v.1] : Continuous (algebraMap v.Completion w.Completion) := by
  have he : (algebraMap v.Completion w.Completion : v.Completion → w.Completion)
      = fun c => c • (1 : w.Completion) := by
    funext c
    rw [Algebra.algebraMap_eq_smul_one]
  rw [he]
  exact continuous_id.smul continuous_const

set_option maxHeartbeats 400000 in
theorem continuous_conorm :
    Continuous (genuineInfinitePlaceData (K := K) (L := L)).conorm := by
  refine continuous_pi fun w => ?_
  haveI : w.1.LiesOver (w.comap (algebraMap K L)).1 := liesOver_of_comap_eq rfl
  have hcomp : (fun x : InfiniteAdeleRing K =>
      (genuineInfinitePlaceData (K := K) (L := L)).conorm x w)
      = fun x => algebraMap ((w.comap (algebraMap K L)).Completion) w.Completion
          (x (w.comap (algebraMap K L))) := by
    funext x
    show psiFactor (w.comap (algebraMap K L)) w
        ((x (w.comap (algebraMap K L))) ⊗ₜ[K] (1 : L)) = _
    rw [psiFactor_tmul, map_one, mul_one]
  rw [hcomp]
  exact (continuous_algebraMap_completion _ w).comp (continuous_apply _)

end

end M4aHerbrand.ArchSemilocal


