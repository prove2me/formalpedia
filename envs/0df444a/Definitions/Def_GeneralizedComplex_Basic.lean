-- Prove2me | Definitions.Def_GeneralizedComplex_Basic
-- name    : GeneralizedComplex_Basic
-- status  : Definition
-- author  : @Lucas
-- created : 2026-10-12T23:43:44.712644+00:00
-- url     : https://prove2.me/theorems/6497eaf5-9bb9-4cb4-9915-0b563b604558
-- title:
--   Generalized complex linear algebra: $T\oplus T^*$, generalized almost complex structures, $L(E,\varepsilon)$, type
-- statement:
--   Shared definitions for the linear algebra of generalized complex geometry.
--
--   Let $T=\mathbb R^N$ (a tangent space of an $N$-manifold) and identify $T^*$ with $\mathbb R^N$ via the standard dual basis. The file defines, on the generalized tangent space $T\oplus T^*$ (modelled as coordinates indexed by $\mathrm{Fin}\,N\sqcup\mathrm{Fin}\,N$, vector part first, one-form part second):
--
--   1. the natural inner product $\langle X+\xi,Y+\eta\rangle=\tfrac12(\xi(Y)+\eta(X))$ (over $\mathbb R$ or $\mathbb C$);
--   2. **generalized almost complex structures**: real matrices $\mathcal J$ with $\mathcal J^2=-1$ preserving the inner product;
--   3. the $\sqrt{-1}$-eigenspace $L=\{v:\ \mathcal J v=\sqrt{-1}\,v\}\subseteq\mathbb C^N\oplus\mathbb C^N$ and the complex conjugate subspace $\bar L$;
--   4. isotropic subspaces ($\langle\ell,\ell'\rangle=0$ on $L$) and maximal isotropic subspaces (isotropic of dimension $N$);
--   5. the projection $\pi_T(L)$ to $T$, the **type** $2(N-\dim_{\mathbb C}\pi_T(L))$ and the **real index** $\dim_{\mathbb C}(L\cap\bar L)$;
--   6. $L(E,\varepsilon)=\{X+\xi: X\in E,\ \xi|_E=\varepsilon(X,\cdot)\}$ for a subspace $E\subseteq T$ and a bilinear form $\varepsilon$ on $E$;
--   7. the B-field shift $e^B(X+\xi)=X+\xi+i_XB$;
--   8. the model structures $\mathcal J_{J_0}(X+\xi)=-J_0X+\xi\circ J_0$ of an almost complex structure $J_0$ and $\mathcal J_\omega(X+\xi)=-(\omega^\flat)^{-1}\xi+\omega^\flat X$ of a 2-form $\omega$, where $\omega^\flat X=i_X\omega$.
--
--   These are the objects of the sections *Definition* and *Maximal isotropic subbundles* of the source, taken fiberwise.
--
--   **Formalization Note** A 2-form $B$ on $T$ is a matrix with $B(X,Y)=X^{\mathsf T}BY$, so $i_XB=B^{\mathsf T}X$ in coordinates. For a singular $\omega$, the Lean matrix inverse in $\mathcal J_\omega$ is $0$; statements about $\mathcal J_\omega$ assume $\det\omega\ne0$.
-- source:
--   Wikipedia, "Generalized complex structure", revision oldid=1288019306, https://en.wikipedia.org/w/index.php?title=Generalized_complex_structure&oldid=1288019306, sections Definition and Maximal isotropic subbundles

import Mathlib

/-!
Fiberwise (linear-algebraic) model of generalized complex geometry, following the Wikipedia
article "Generalized complex structure" (oldid 1288019306), sections *Definition* and
*Maximal isotropic subbundles*.

A fiber of the tangent bundle of an `N`-manifold is modelled by `𝕜^N` (`Fin N → 𝕜`), a fiber of
the cotangent bundle by `𝕜^N` paired with it through the standard dual basis, and a fiber of the
generalized tangent bundle `T ⊕ T*` by `GIdx N → 𝕜`, where `GIdx N = Fin N ⊕ Fin N`: the `inl`
coordinates carry the vector part `X` and the `inr` coordinates carry the one-form part `ξ`.
-/

namespace GeneralizedComplex

open Matrix

/-- Coordinates of the generalized tangent space `T ⊕ T*` of an `N`-dimensional space:
`Sum.inl i` indexes the vector part, `Sum.inr i` the one-form part. -/
abbrev GIdx (N : ℕ) := Fin N ⊕ Fin N

/-- The vector part `X` of `X + ξ ∈ T ⊕ T*`. -/
def vecPart {𝕜 : Type*} {N : ℕ} (u : GIdx N → 𝕜) : Fin N → 𝕜 := fun i => u (Sum.inl i)

/-- The one-form part `ξ` of `X + ξ ∈ T ⊕ T*`. -/
def formPart {𝕜 : Type*} {N : ℕ} (u : GIdx N → 𝕜) : Fin N → 𝕜 := fun i => u (Sum.inr i)

/-- The natural inner product of signature `(N, N)` on `T ⊕ T*`:
`⟨X + ξ, Y + η⟩ = ½ (ξ(Y) + η(X))`. -/
noncomputable def pairing {𝕜 : Type*} [Field 𝕜] {N : ℕ} (u v : GIdx N → 𝕜) : 𝕜 :=
  (formPart u ⬝ᵥ vecPart v + formPart v ⬝ᵥ vecPart u) / 2

/-- A generalized almost complex structure on the (real) generalized tangent space:
a real endomorphism `𝒥` of `T ⊕ T*` with `𝒥² = -Id` preserving the natural inner product. -/
structure IsGenAlmostComplex {N : ℕ} (J : Matrix (GIdx N) (GIdx N) ℝ) : Prop where
  sq_eq_neg_one : J * J = -1
  pairing_mulVec : ∀ u v : GIdx N → ℝ, pairing (J *ᵥ u) (J *ᵥ v) = pairing u v

/-- The `√-1`-eigenspace `L = {v ∈ (T ⊕ T*) ⊗ ℂ : 𝒥 v = i v}` of (the complexification of) a real
endomorphism `𝒥` of `T ⊕ T*`. -/
noncomputable def plusIEigenspace {N : ℕ} (J : Matrix (GIdx N) (GIdx N) ℝ) :
    Submodule ℂ (GIdx N → ℂ) :=
  LinearMap.ker ((J.map (fun x : ℝ => (x : ℂ))).mulVecLin - Complex.I • LinearMap.id)

/-- The complex conjugate `L̄ = {v : v̄ ∈ L}` of a complex subspace `L ⊆ ℂ^ι`. -/
def conjSubmodule {ι : Type*} (L : Submodule ℂ (ι → ℂ)) : Submodule ℂ (ι → ℂ) where
  carrier := {v | star v ∈ L}
  add_mem' {a b} ha hb := by
    show star (a + b) ∈ L
    rw [star_add]
    exact L.add_mem ha hb
  zero_mem' := by simp
  smul_mem' c v hv := by
    show star (c • v) ∈ L
    rw [star_smul]
    exact L.smul_mem _ hv

/-- A subspace `L ⊆ T ⊕ T*` (real or complexified) is isotropic if
`⟨ℓ, ℓ'⟩ = 0` for all `ℓ, ℓ' ∈ L`. -/
def IsIsotropic {𝕜 : Type*} [Field 𝕜] {N : ℕ} (L : Submodule 𝕜 (GIdx N → 𝕜)) : Prop :=
  ∀ u ∈ L, ∀ v ∈ L, pairing u v = 0

/-- A subspace `L ⊆ T ⊕ T*` is maximal isotropic if it is isotropic and its rank equals `N`. -/
def IsMaximalIsotropic {𝕜 : Type*} [Field 𝕜] {N : ℕ} (L : Submodule 𝕜 (GIdx N → 𝕜)) : Prop :=
  IsIsotropic L ∧ Module.finrank 𝕜 L = N

/-- The projection `π_T(L) ⊆ T` of a subspace `L ⊆ T ⊕ T*` onto the tangent space. -/
def tangentProjection {𝕜 : Type*} [Field 𝕜] {N : ℕ} (L : Submodule 𝕜 (GIdx N → 𝕜)) :
    Submodule 𝕜 (Fin N → 𝕜) :=
  L.map (LinearMap.funLeft 𝕜 𝕜 Sum.inl)

/-- The type of a complex subspace `L ⊆ (T ⊕ T*) ⊗ ℂ`, as defined in the source: `2N` minus the
real dimension of the projection of `L` onto `T ⊗ ℂ`, i.e. `2 (N - dim_ℂ π_T(L))`. -/
noncomputable def genType {N : ℕ} (L : Submodule ℂ (GIdx N → ℂ)) : ℕ :=
  2 * (N - Module.finrank ℂ (tangentProjection L))

/-- The real index `r` of `L ⊆ (T ⊕ T*) ⊗ ℂ`: the complex dimension of `L ∩ L̄`. -/
noncomputable def realIndex {N : ℕ} (L : Submodule ℂ (GIdx N → ℂ)) : ℕ :=
  Module.finrank ℂ ↥(L ⊓ conjSubmodule L)

/-- The subspace `L(E, ε) ⊆ T ⊕ T*` attached to a subspace `E ⊆ T` and a bilinear form `ε` on `E`:
all `X + ξ` with `X ∈ E` and `ξ|_E = ε(X) = ε(X, ·)`. -/
def isotropicOfPair {𝕜 : Type*} [Field 𝕜] {N : ℕ} (E : Submodule 𝕜 (Fin N → 𝕜))
    (ε : LinearMap.BilinForm 𝕜 E) : Submodule 𝕜 (GIdx N → 𝕜) where
  carrier := {u | ∃ h : vecPart u ∈ E, ∀ Y : E, formPart u ⬝ᵥ (Y : Fin N → 𝕜) = ε ⟨vecPart u, h⟩ Y}
  add_mem' {a b} ha hb := by
    obtain ⟨ha, ha'⟩ := ha
    obtain ⟨hb, hb'⟩ := hb
    refine ⟨E.add_mem ha hb, fun Y => ?_⟩
    have h1 : (⟨vecPart (a + b), E.add_mem ha hb⟩ : E) = ⟨vecPart a, ha⟩ + ⟨vecPart b, hb⟩ := rfl
    rw [h1, map_add, LinearMap.add_apply, ← ha' Y, ← hb' Y]
    exact add_dotProduct _ _ _
  zero_mem' := by
    refine ⟨E.zero_mem, fun Y => ?_⟩
    have h0 : (⟨vecPart (0 : GIdx N → 𝕜), E.zero_mem⟩ : E) = 0 := rfl
    rw [h0, map_zero, LinearMap.zero_apply]
    exact zero_dotProduct _
  smul_mem' c u hu := by
    obtain ⟨hu, hu'⟩ := hu
    refine ⟨E.smul_mem c hu, fun Y => ?_⟩
    have h1 : (⟨vecPart (c • u), E.smul_mem c hu⟩ : E) = c • ⟨vecPart u, hu⟩ := rfl
    rw [h1, map_smul, LinearMap.smul_apply, ← hu' Y]
    exact smul_dotProduct _ _ _

/-- The B-field shift `e^B : X + ξ ↦ X + ξ + i_X B` of `T ⊕ T*` determined by a matrix `B`
(the 2-form `B(X, Y) = Xᵀ B Y`, so `(i_X B)_j = ∑ᵢ Xᵢ Bᵢⱼ`). -/
def bShift {𝕜 : Type*} [CommRing 𝕜] {N : ℕ} (B : Matrix (Fin N) (Fin N) 𝕜) :
    Matrix (GIdx N) (GIdx N) 𝕜 :=
  fromBlocks 1 0 Bᵀ 1

/-- The generalized almost complex structure of an almost complex structure `J₀` on `T`:
`𝒥_{J₀}(X + ξ) = -J₀ X + ξ ∘ J₀`. -/
def complexStructureGen {N : ℕ} (J₀ : Matrix (Fin N) (Fin N) ℝ) : Matrix (GIdx N) (GIdx N) ℝ :=
  fromBlocks (-J₀) 0 0 J₀ᵀ

/-- The generalized almost complex structure of a nondegenerate 2-form `ω` on `T`:
`𝒥_ω(X + ξ) = -ω♭⁻¹ ξ + ω♭ X`, where `ω♭ X = i_X ω` (matrix `ωᵀ`). -/
noncomputable def symplecticGen {N : ℕ} (ω : Matrix (Fin N) (Fin N) ℝ) :
    Matrix (GIdx N) (GIdx N) ℝ :=
  fromBlocks 0 (-(ωᵀ)⁻¹) ωᵀ 0

end GeneralizedComplex


