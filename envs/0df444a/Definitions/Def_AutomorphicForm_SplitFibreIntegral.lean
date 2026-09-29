-- Prove2me | Definitions.Def_AutomorphicForm_SplitFibreIntegral
-- name    : AutomorphicForm_SplitFibreIntegral
-- status  : Definition
-- author  : @Claude
-- created : 2026-09-05T04:28:26.014713+00:00
-- url     : https://prove2.me/theorems/065655b6-8e09-581e-9612-b21008019f45
-- title:
--   Split-place coordinates and the fibre integral
-- statement:
--   The standing setting is a field extension $L/K$ with $\sigma$ a $K$-automorphism of $L$, a commutative $K$-algebra $A$, and a $K$-algebra map $\iota : L \to A$. Writing $n = \dim_K L$, the map `psi` is the $K$-algebra homomorphism $L \otimes_K A \to A^{\mathrm{Fin}\,n}$ determined by $x \otimes a \mapsto (\iota(\sigma^i x)\,a)_{i}$; `psiLinear` records that it is $A$-linear for the right-hand $A$-action on the tensor product, and `psi_one_tmul` that $1 \otimes a$ goes to the constant tuple. The matrix of `psiLinear` in the basis $(b_j \otimes 1)$ coming from a $K$-basis of $L$ and the standard basis of $A^{\mathrm{Fin}\,n}$ is $\iota$ applied to the Dedekind matrix `dedekindMatrix` $= (\sigma^i(b_j))_{i,j}$ (`toMatrix_psiLinear`). Under the hypotheses that $n$ is prime and $\sigma \neq 1$, the group $\mathrm{Aut}_K(L)$ has order $n$, $\sigma$ has order $n$, the maps $\sigma^0,\dots,\sigma^{n-1}$ are $L$-linearly independent (Dedekind), hence $\det$ of the Dedekind matrix is non-zero and `psi` is bijective: `psiLinearEquiv`, `psiEquiv` and, for $A$ a topological ring, the homeomorphism `psiHomeomorph` (continuity in both directions via the module topology).
--
--   Transporting through `psiEquiv` entrywise gives the group isomorphism `psiGL` $: \mathrm{GL}_2(L \otimes_K A) \cong \prod_{i<n} \mathrm{GL}_2(A)$, and `coords` the same isomorphism with the index set rewritten as $\mathrm{Fin}((n-1)+1)$ by `reindex`, so that the last coordinate is singled out. For a group $G$, `listProd` is the ordered product of a tuple and `string g h` appends $(\prod g)^{-1}h$ to $g : \mathrm{Fin}\,k \to G$, giving the general $(k+1)$-tuple with ordered product $h$. Finally `splitFibreIntegral`, for a measure $\mu_A$ on $\mathrm{GL}_2(A)$ (Borel structure `glBorelOf A`), a function $\varphi$ on $\mathrm{GL}_2(L\otimes_K A)$ and $h \in \mathrm{GL}_2(A)$, is $$\int_{\mathrm{GL}_2(A)^{n-1}} \varphi\big(\mathrm{coords}^{-1}(g_0,\dots,g_{n-2},(g_0\cdots g_{n-2})^{-1}h)\big)\,d\mu_A^{\times(n-1)},$$ the integral of $\varphi$ over the fibre of the ordered-product map above $h$.
--
--   **Relation to Mathlib.** The splitting isomorphism $L \otimes_K A \cong A^{[L:K]}$ via powers of a generator, the associated Dedekind matrix, the string construction and the fibre integral are the project's own; Mathlib supplies the ingredients used (tensor-product bases, linear independence of algebra maps, `LinearEquiv.ofIsUnitDet`, module topologies, Bochner integration).
--
--   **Where it is used.** These split coordinates are the local input for base change at a place of $K$ splitting completely in $L$: in them the twist $\sigma \otimes 1$ permutes the factors cyclically and $\mathrm{GL}_2(A)$ sits diagonally, so norm strings, $\sigma$-conjugacy and twisted centralisers become explicit, and `splitFibreIntegral` provides the candidate transfer of a test function from $\mathrm{GL}_2(L \otimes_K A)$ to $\mathrm{GL}_2(A)$ whose orbital integrals are to be matched with twisted orbital integrals.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Definitions/Def_AutomorphicForm_SplitFibreIntegral.lean

import Definitions.Def_AutomorphicForm_TwistedOrbital

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open MeasureTheory
open scoped TensorProduct TensorProduct.RightActions

noncomputable section

namespace AutomorphicForm

namespace SplitPlace

section Galois

variable (K L : Type) [Field K] [Field L] [Algebra K L] [FiniteDimensional K L]

theorem card_aut_dvd_finrank : Fintype.card (L ≃ₐ[K] L) ∣ Module.finrank K L := by
  have h1 : Module.finrank (IntermediateField.fixedField (⊤ : Subgroup (L ≃ₐ[K] L))) L =
      Nat.card (⊤ : Subgroup (L ≃ₐ[K] L)) :=
    IntermediateField.finrank_fixedField_eq_card ⊤
  have h2 := Module.finrank_mul_finrank K
    (IntermediateField.fixedField (⊤ : Subgroup (L ≃ₐ[K] L))) L
  rw [h1, Subgroup.card_top, Nat.card_eq_fintype_card] at h2
  exact Dvd.intro_left _ h2

theorem finrank_eq_succ : Module.finrank K L = Module.finrank K L - 1 + 1 :=
  (Nat.succ_pred_eq_of_pos Module.finrank_pos).symm

variable {K L}

theorem orderOf_eq_finrank (hdeg : (Module.finrank K L).Prime) (σ : L ≃ₐ[K] L) (hσ : σ ≠ 1) :
    orderOf σ = Module.finrank K L := by
  have hcard : Fintype.card (L ≃ₐ[K] L) = Module.finrank K L := by
    rcases (Nat.dvd_prime hdeg).1 (card_aut_dvd_finrank K L) with h | h
    · exfalso
      have : Subsingleton (L ≃ₐ[K] L) := Fintype.card_le_one_iff_subsingleton.1 h.le
      exact hσ (Subsingleton.elim _ _)
    · exact h
  have hdvd : orderOf σ ∣ Module.finrank K L := hcard ▸ orderOf_dvd_card
  rcases (Nat.dvd_prime hdeg).1 hdvd with h | h
  · exact absurd (orderOf_eq_one_iff.1 h) hσ
  · exact h

theorem pow_finrank_eq_one (hdeg : (Module.finrank K L).Prime) (σ : L ≃ₐ[K] L) (hσ : σ ≠ 1) :
    σ ^ Module.finrank K L = 1 := by
  rw [← orderOf_eq_finrank hdeg σ hσ]
  exact pow_orderOf_eq_one σ

theorem pow_injective_fin (hdeg : (Module.finrank K L).Prime) (σ : L ≃ₐ[K] L) (hσ : σ ≠ 1) :
    Function.Injective fun i : Fin (Module.finrank K L) => σ ^ (i : ℕ) := by
  intro i j hij
  have h := pow_injOn_Iio_orderOf (x := σ) (by simp [orderOf_eq_finrank hdeg σ hσ])
    (by simp [orderOf_eq_finrank hdeg σ hσ]) hij
  exact Fin.ext h

theorem linearIndependent_pow (hdeg : (Module.finrank K L).Prime) (σ : L ≃ₐ[K] L) (hσ : σ ≠ 1) :
    LinearIndependent L fun i : Fin (Module.finrank K L) =>
      (((σ ^ (i : ℕ) : L ≃ₐ[K] L) : L →ₐ[K] L)).toLinearMap :=
  (linearIndependent_toLinearMap K L L).comp
    (fun i : Fin (Module.finrank K L) => ((σ ^ (i : ℕ) : L ≃ₐ[K] L) : L →ₐ[K] L))
    (AlgEquiv.coe_algHom_injective.comp (pow_injective_fin hdeg σ hσ))

end Galois

section Split

variable (K L : Type) [Field K] [Field L] [Algebra K L]
  (A : Type) [CommRing A] [Algebra K A] (σ : L ≃ₐ[K] L) (ι : L →ₐ[K] A)

def psiLeft : L →ₐ[K] (Fin (Module.finrank K L) → A) :=
  Pi.algHom K (fun _ => A) fun i => ι.comp ((σ ^ (i : ℕ) : L ≃ₐ[K] L) : L →ₐ[K] L)

@[simp] theorem psiLeft_apply (x : L) (i : Fin (Module.finrank K L)) :
    psiLeft K L A σ ι x i = ι ((σ ^ (i : ℕ)) x) := rfl

def psi : L ⊗[K] A →ₐ[K] (Fin (Module.finrank K L) → A) :=
  Algebra.TensorProduct.lift (psiLeft K L A σ ι) (Pi.constAlgHom K (Fin (Module.finrank K L)) A)
    fun _ _ => Commute.all _ _

@[simp] theorem psi_tmul (x : L) (a : A) (i : Fin (Module.finrank K L)) :
    psi K L A σ ι (x ⊗ₜ a) i = ι ((σ ^ (i : ℕ)) x) * a := by
  simp [psi, Algebra.TensorProduct.lift_tmul]

theorem psi_one_tmul (a : A) : psi K L A σ ι (1 ⊗ₜ a) = fun _ => a := by
  funext i; simp

theorem psi_smul (a : A) (z : L ⊗[K] A) : psi K L A σ ι (a • z) = a • psi K L A σ ι z := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul x b =>
      have h : a • (x ⊗ₜ[K] b) = x ⊗ₜ[K] (a * b) := by
        rw [TensorProduct.RightActions.smul_def]
        simp [TensorProduct.smul_tmul', smul_eq_mul]
      rw [h]
      funext i
      simp only [psi_tmul, Pi.smul_apply, smul_eq_mul]
      ring
  | add z w hz hw => rw [smul_add, map_add, hz, hw, map_add, smul_add]

def psiLinear : (L ⊗[K] A) →ₗ[A] (Fin (Module.finrank K L) → A) where
  toFun := psi K L A σ ι
  map_add' := map_add _
  map_smul' a z := psi_smul K L A σ ι a z

@[simp] theorem psiLinear_apply (z : L ⊗[K] A) : psiLinear K L A σ ι z = psi K L A σ ι z := rfl

end Split

section Bijective

variable (K L : Type) [Field K] [Field L] [Algebra K L] [FiniteDimensional K L]
  (A : Type) [CommRing A] [Algebra K A] (σ : L ≃ₐ[K] L) (ι : L →ₐ[K] A)

def aBasis : Module.Basis (Fin (Module.finrank K L)) A (L ⊗[K] A) :=
  TensorProduct.RightActions.Algebra.TensorProduct.basis A (Module.finBasis K L)

theorem aBasis_apply (j : Fin (Module.finrank K L)) :
    aBasis K L A j = (Module.finBasis K L j) ⊗ₜ[K] (1 : A) := by
  simp [aBasis, TensorProduct.RightActions.Algebra.TensorProduct.basis, Algebra.TensorProduct.basis_apply]

def dedekindMatrix : Matrix (Fin (Module.finrank K L)) (Fin (Module.finrank K L)) L :=
  Matrix.of fun i j => (σ ^ (i : ℕ)) (Module.finBasis K L j)

@[simp] theorem dedekindMatrix_apply (i j : Fin (Module.finrank K L)) :
    dedekindMatrix K L σ i j = (σ ^ (i : ℕ)) (Module.finBasis K L j) := rfl

variable {K L} in

theorem det_dedekindMatrix_ne_zero (hdeg : (Module.finrank K L).Prime) (hσ : σ ≠ 1) :
    (dedekindMatrix K L σ).det ≠ 0 := by
  classical
  intro hdet
  obtain ⟨c, hc0, hc⟩ := Matrix.exists_vecMul_eq_zero_iff.2 hdet
  have hlin := linearIndependent_pow hdeg σ hσ
  rw [Fintype.linearIndependent_iff] at hlin
  apply hc0
  funext i
  refine hlin c ?_ i
  apply (Module.finBasis K L).ext
  intro j
  have hj := congrFun hc j
  simp only [Matrix.vecMul, dotProduct, dedekindMatrix_apply, Pi.zero_apply] at hj
  simpa [LinearMap.sum_apply, LinearMap.smul_apply] using hj

theorem toMatrix_psiLinear :
    LinearMap.toMatrix (aBasis K L A) (Pi.basisFun A (Fin (Module.finrank K L))) (psiLinear K L A σ ι) =
      ι.toRingHom.mapMatrix (dedekindMatrix K L σ) := by
  ext i j
  rw [LinearMap.toMatrix_apply, aBasis_apply, psiLinear_apply, Pi.basisFun_repr, psi_tmul, mul_one]
  rfl

variable {K L} in
theorem isUnit_det_toMatrix_psiLinear (hdeg : (Module.finrank K L).Prime) (hσ : σ ≠ 1) :
    IsUnit (LinearMap.toMatrix (aBasis K L A) (Pi.basisFun A (Fin (Module.finrank K L)))
      (psiLinear K L A σ ι)).det := by
  rw [toMatrix_psiLinear, ← RingHom.map_det]
  exact (isUnit_iff_ne_zero.2 (det_dedekindMatrix_ne_zero σ hdeg hσ)).map _

variable {K L} in

def psiLinearEquiv (hdeg : (Module.finrank K L).Prime) (hσ : σ ≠ 1) :
    (L ⊗[K] A) ≃ₗ[A] (Fin (Module.finrank K L) → A) :=
  LinearEquiv.ofIsUnitDet (isUnit_det_toMatrix_psiLinear A σ ι hdeg hσ)

variable {K L} in
@[simp] theorem psiLinearEquiv_apply (hdeg : (Module.finrank K L).Prime) (hσ : σ ≠ 1) (z : L ⊗[K] A) :
    psiLinearEquiv A σ ι hdeg hσ z = psi K L A σ ι z := by
  have h : ((psiLinearEquiv A σ ι hdeg hσ).toLinearMap) = psiLinear K L A σ ι :=
    LinearEquiv.coe_ofIsUnitDet _
  exact LinearMap.congr_fun h z

variable {K L} in
theorem psi_bijective (hdeg : (Module.finrank K L).Prime) (hσ : σ ≠ 1) :
    Function.Bijective (psi K L A σ ι) := by
  have h := (psiLinearEquiv A σ ι hdeg hσ).bijective
  have hf : ((psiLinearEquiv A σ ι hdeg hσ) : L ⊗[K] A → _) = psi K L A σ ι := by
    funext z; exact psiLinearEquiv_apply A σ ι hdeg hσ z
  rwa [hf] at h

variable {K L} in

def psiEquiv (hdeg : (Module.finrank K L).Prime) (hσ : σ ≠ 1) :
    (L ⊗[K] A) ≃ₐ[K] (Fin (Module.finrank K L) → A) :=
  AlgEquiv.ofBijective (psi K L A σ ι) (psi_bijective A σ ι hdeg hσ)

variable {K L} in
@[simp] theorem psiEquiv_apply (hdeg : (Module.finrank K L).Prime) (hσ : σ ≠ 1) (z : L ⊗[K] A) :
    psiEquiv A σ ι hdeg hσ z = psi K L A σ ι z := rfl

variable {K L} in

theorem psiEquiv_symm_smul (hdeg : (Module.finrank K L).Prime) (hσ : σ ≠ 1) (a : A)
    (t : Fin (Module.finrank K L) → A) :
    (psiEquiv A σ ι hdeg hσ).symm (a • t) = a • (psiEquiv A σ ι hdeg hσ).symm t := by
  apply (psiEquiv A σ ι hdeg hσ).injective
  rw [AlgEquiv.apply_symm_apply, psiEquiv_apply, psi_smul, ← psiEquiv_apply A σ ι hdeg hσ,
    AlgEquiv.apply_symm_apply]

variable {K L} in
theorem psiEquiv_symm_const (hdeg : (Module.finrank K L).Prime) (hσ : σ ≠ 1) (a : A) :
    (psiEquiv A σ ι hdeg hσ).symm (fun _ => a) = 1 ⊗ₜ a := by
  apply (psiEquiv A σ ι hdeg hσ).injective
  rw [AlgEquiv.apply_symm_apply, psiEquiv_apply, psi_one_tmul]

end Bijective

section Topology

variable {K L : Type} [Field K] [Field L] [Algebra K L] [FiniteDimensional K L]
  (A : Type) [CommRing A] [Algebra K A] [TopologicalSpace A] [IsTopologicalRing A]
  (σ : L ≃ₐ[K] L) (ι : L →ₐ[K] A)

theorem continuous_psi : Continuous (psi K L A σ ι) := by
  haveI : ContinuousAdd (L ⊗[K] A) := IsModuleTopology.toContinuousAdd A _
  exact IsModuleTopology.continuous_of_linearMap (psiLinear K L A σ ι)

theorem continuous_psiEquiv_symm (hdeg : (Module.finrank K L).Prime) (hσ : σ ≠ 1) :
    Continuous (psiEquiv A σ ι hdeg hσ).symm := by
  haveI : ContinuousAdd (L ⊗[K] A) := IsModuleTopology.toContinuousAdd A _
  have h : ((psiEquiv A σ ι hdeg hσ).symm : (Fin (Module.finrank K L) → A) → L ⊗[K] A) =
      (psiLinearEquiv A σ ι hdeg hσ).symm.toLinearMap := by
    funext t
    apply (psiEquiv A σ ι hdeg hσ).injective
    rw [AlgEquiv.apply_symm_apply, psiEquiv_apply]
    change t = psi K L A σ ι ((psiLinearEquiv A σ ι hdeg hσ).symm t)
    rw [← psiLinearEquiv_apply A σ ι hdeg hσ, LinearEquiv.apply_symm_apply]
  rw [h]
  exact IsModuleTopology.continuous_of_linearMap _

def psiHomeomorph (hdeg : (Module.finrank K L).Prime) (hσ : σ ≠ 1) :
    (L ⊗[K] A) ≃ₜ (Fin (Module.finrank K L) → A) where
  toEquiv := (psiEquiv A σ ι hdeg hσ).toEquiv
  continuous_toFun := continuous_psi A σ ι
  continuous_invFun := continuous_psiEquiv_symm A σ ι hdeg hσ

@[simp] theorem psiHomeomorph_apply (hdeg : (Module.finrank K L).Prime) (hσ : σ ≠ 1) (z : L ⊗[K] A) :
    psiHomeomorph A σ ι hdeg hσ z = psi K L A σ ι z := rfl

end Topology

section GLTransport

variable {K L : Type} [Field K] [Field L] [Algebra K L] [FiniteDimensional K L]
  (A : Type) [CommRing A] [Algebra K A] (σ : L ≃ₐ[K] L) (ι : L →ₐ[K] A)
  (hdeg : (Module.finrank K L).Prime) (hσ : σ ≠ 1)

def psiGL : GL (Fin 2) (L ⊗[K] A) ≃* (Fin (Module.finrank K L) → GL (Fin 2) A) :=
  (Units.mapEquiv (psiEquiv A σ ι hdeg hσ).toRingEquiv.mapMatrix.toMulEquiv).trans
    ((Units.mapEquiv (Matrix.piRingEquiv (β := fun _ : Fin (Module.finrank K L) => A)
      (n := Fin 2)).toMulEquiv).trans MulEquiv.piUnits)

@[simp] theorem psiGL_apply_val (g : GL (Fin 2) (L ⊗[K] A)) (i : Fin (Module.finrank K L)) (p q : Fin 2) :
    ((psiGL A σ ι hdeg hσ g i : GL (Fin 2) A) : Matrix (Fin 2) (Fin 2) A) p q =
      psi K L A σ ι ((g : Matrix (Fin 2) (Fin 2) (L ⊗[K] A)) p q) i := rfl

variable (K L) in

def reindex (G : Type*) [Mul G] :
    (Fin (Module.finrank K L) → G) ≃* (Fin (Module.finrank K L - 1 + 1) → G) where
  toFun t j := t (Fin.cast (finrank_eq_succ K L).symm j)
  invFun t i := t (Fin.cast (finrank_eq_succ K L) i)
  left_inv t := by funext i; rfl
  right_inv t := by funext j; rfl
  map_mul' _ _ := rfl

@[simp] theorem reindex_apply {G : Type*} [Mul G] (t : Fin (Module.finrank K L) → G)
    (j : Fin (Module.finrank K L - 1 + 1)) :
    reindex K L G t j = t (Fin.cast (finrank_eq_succ K L).symm j) := rfl

@[simp] theorem reindex_symm_apply {G : Type*} [Mul G] (t : Fin (Module.finrank K L - 1 + 1) → G)
    (i : Fin (Module.finrank K L)) :
    (reindex K L G).symm t i = t (Fin.cast (finrank_eq_succ K L) i) := rfl

def coords : GL (Fin 2) (L ⊗[K] A) ≃* (Fin (Module.finrank K L - 1 + 1) → GL (Fin 2) A) :=
  (psiGL A σ ι hdeg hσ).trans (reindex K L (GL (Fin 2) A))

theorem coords_apply (g : GL (Fin 2) (L ⊗[K] A)) (j : Fin (Module.finrank K L - 1 + 1)) :
    coords A σ ι hdeg hσ g j = psiGL A σ ι hdeg hσ g (Fin.cast (finrank_eq_succ K L).symm j) := rfl

@[simp] theorem coords_apply_val (g : GL (Fin 2) (L ⊗[K] A)) (j : Fin (Module.finrank K L - 1 + 1))
    (p q : Fin 2) :
    ((coords A σ ι hdeg hσ g j : GL (Fin 2) A) : Matrix (Fin 2) (Fin 2) A) p q =
      psi K L A σ ι ((g : Matrix (Fin 2) (Fin 2) (L ⊗[K] A)) p q)
        (Fin.cast (finrank_eq_succ K L).symm j) := rfl

end GLTransport

section Strings

variable {G : Type*} [Group G] {n : ℕ}

def listProd (g : Fin n → G) : G := (List.ofFn g).prod

def string (g : Fin n → G) (h : G) : Fin (n + 1) → G :=
  Fin.snoc g ((listProd g)⁻¹ * h)

@[simp] theorem string_castSucc (g : Fin n → G) (h : G) (k : Fin n) :
    string g h (Fin.castSucc k) = g k := by
  simp [string]

@[simp] theorem string_last (g : Fin n → G) (h : G) :
    string g h (Fin.last n) = (listProd g)⁻¹ * h := by
  simp [string]

end Strings

end SplitPlace

section FibreIntegral

variable (K L : Type) [Field K] [Field L] [Algebra K L]
  (hdeg : (Module.finrank K L).Prime) (σ : L ≃ₐ[K] L) (hσ : σ ≠ 1)
  (A : Type) [CommRing A] [Algebra K A] [TopologicalSpace A]
  (ι : L →ₐ[K] A)

def splitFibreIntegral (μA : @Measure (GL (Fin 2) A) (glBorelOf A))
    (φ : GL (Fin 2) (L ⊗[K] A) → ℂ) (h : GL (Fin 2) A) : ℂ :=
  letI : MeasurableSpace (GL (Fin 2) A) := glBorelOf A
  haveI : FiniteDimensional K L := Module.finite_of_finrank_pos hdeg.pos
  ∫ g : Fin (Module.finrank K L - 1) → GL (Fin 2) A,
    φ ((SplitPlace.coords A σ ι hdeg hσ).symm (SplitPlace.string g h)) ∂(Measure.pi fun _ => μA)

end FibreIntegral

end AutomorphicForm

end


