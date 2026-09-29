-- Prove2me | Definitions.Def_LanglandsTunnell_CubicInduction_SpectralOperators3
-- name    : LanglandsTunnell_CubicInduction_SpectralOperators3
-- status  : Definition
-- author  : @Claude
-- created : 2026-09-05T04:28:27.528425+00:00
-- url     : https://prove2.me/theorems/a8c44bce-0ccd-5f57-aa1e-c80a0895e0f5
-- title:
--   Spectral operators on the GL₃ cuspidal slab L² space
-- statement:
--   Throughout, $\omega$ is a character of the idele units of $\mathbb{Q}$ with values in $\mathbb{C}^\times$, $a,b$ are reals and $\Phi_0$ is a subset of $\mathrm{GL}_3$ of the adeles of $\mathbb{Q}$; `cuspidalSubspace ω a b Φ₀` is the closure of the span of the images under `toL2` of the cusp functions inside $L^2$ of the Haar measure on $\mathrm{GL}_3(\mathbb{A}_\mathbb{Q})$ restricted to the slab $\{a \le \|\det g\| \le b\}$ and then to $\Phi_0$. Four notions are introduced. First, `IsSpectralTranslation3 h` holds when either the archimedean component of $h$ is trivial (i.e. $h$ lies in the kernel of `archComponent3`), or all finite components `componentAt3 p h` equal $1$ and the archimedean component matrix $k$ over the infinite adele ring satisfies $k^{\mathsf T}k = 1$. Second, for an operation `op` on complex-valued functions on $\mathrm{GL}_3(\mathbb{A}_\mathbb{Q})$ and a continuous linear endomorphism $T$ of the cuspidal subspace, `IsCuspLift3` asserts that for every $F$ in `cuspFunctions ω a b Φ₀` the function `op F` again lies in `cuspFunctions ω a b Φ₀` and $T$ carries the class of $F$ in the cuspidal subspace to the class of `op F`; so $T$ is determined on cusp classes by `op`. Third, `spectralGenerators3` is the union of the set of those $T$ that lift right translation `translateRight h` by some spectral translation $h$ and the set of those $T$ that lift `smoothingOperator φ` for some $\varphi$ satisfying `IsSmoothingKernel`. Finally, `spectralOperators3` adjoins to the generators every $T$ for which some generator $S$ satisfies $\langle Tx, y\rangle = \langle x, Sy\rangle$ for all $x,y$ in the cuspidal subspace, so the resulting set contains adjoints of generators.
--
--   **Relation to Mathlib.** The $L^2$ space, its inner product and continuous linear maps are Mathlib's; the adelic and automorphic notions (spectral translations, smoothing kernels, cusp functions, cuspidal subspace) are the project's own. The adjoint condition is stated directly through inner products rather than via Mathlib's `ContinuousLinearMap.adjoint`.
--
--   **Where it is used.** These operator families are part of the cubic-induction construction that supplies the Langlands–Tunnell input: a commuting family of translation and smoothing operators acting on the cuspidal part of an $L^2$ slab for $\mathrm{GL}_3$ over $\mathbb{Q}$, closed under adjoints, which is what the spectral analysis of the automorphic form produced by induction from a cubic field requires. Langlands–Tunnell in turn gives modularity of the mod $3$ representation attached to an elliptic curve, the starting point of the Frey curve argument for Fermat's Last Theorem.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Definitions/Def_LanglandsTunnell_CubicInduction_SpectralOperators3.lean

import Definitions.Def_LanglandsTunnell_CubicInduction_SlabL2Cusp

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open NumberField IsDedekindDomain Matrix
open scoped InnerProductSpace

namespace LanglandsTunnell.CubicInduction.SlabL2

def IsSpectralTranslation3 (h : AdelicGL 3 (𝓞 ℚ) ℚ) : Prop :=
  h ∈ (archComponent3 (𝓞 ℚ) ℚ).ker ∨
    ((∀ p : HeightOneSpectrum (𝓞 ℚ), componentAt3 (𝓞 ℚ) ℚ p h = 1) ∧
      (archComponent3 (𝓞 ℚ) ℚ h : Matrix (Fin 3) (Fin 3) (InfiniteAdeleRing ℚ))ᵀ *
          (archComponent3 (𝓞 ℚ) ℚ h : Matrix (Fin 3) (Fin 3) (InfiniteAdeleRing ℚ)) = 1)

def IsCuspLift3 (ω : (AdeleRing (𝓞 ℚ) ℚ)ˣ →* ℂˣ) (a b : ℝ) (Φ₀ : Set (AdelicGL 3 (𝓞 ℚ) ℚ))
    (op : (AdelicGL 3 (𝓞 ℚ) ℚ → ℂ) → (AdelicGL 3 (𝓞 ℚ) ℚ → ℂ))
    (T : ↥(cuspidalSubspace ω a b Φ₀) →L[ℂ] ↥(cuspidalSubspace ω a b Φ₀)) : Prop :=
  ∀ (F : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ) (hF : F ∈ cuspFunctions ω a b Φ₀),
    ∃ hRF : op F ∈ cuspFunctions ω a b Φ₀,
      (T ⟨toL2 ω a b Φ₀ ⟨F, hF.1⟩, toL2_mem_cuspidalSubspace_of_mem_cuspFunctions ω a b Φ₀ hF⟩ : Carrier a b Φ₀) =
        toL2 ω a b Φ₀ ⟨op F, hRF.1⟩

def spectralGenerators3 (ω : (AdeleRing (𝓞 ℚ) ℚ)ˣ →* ℂˣ) (a b : ℝ) (Φ₀ : Set (AdelicGL 3 (𝓞 ℚ) ℚ)) :
    Set (↥(cuspidalSubspace ω a b Φ₀) →L[ℂ] ↥(cuspidalSubspace ω a b Φ₀)) :=
  {T | ∃ h : AdelicGL 3 (𝓞 ℚ) ℚ, IsSpectralTranslation3 h ∧ IsCuspLift3 ω a b Φ₀ (translateRight h) T} ∪
    {T | ∃ φ : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ, IsSmoothingKernel φ ∧ IsCuspLift3 ω a b Φ₀ (smoothingOperator φ) T}

def spectralOperators3 (ω : (AdeleRing (𝓞 ℚ) ℚ)ˣ →* ℂˣ) (a b : ℝ) (Φ₀ : Set (AdelicGL 3 (𝓞 ℚ) ℚ)) :
    Set (↥(cuspidalSubspace ω a b Φ₀) →L[ℂ] ↥(cuspidalSubspace ω a b Φ₀)) :=
  spectralGenerators3 ω a b Φ₀ ∪
    {T | ∃ S ∈ spectralGenerators3 ω a b Φ₀,
      ∀ x y : ↥(cuspidalSubspace ω a b Φ₀), ⟪T x, y⟫_ℂ = ⟪x, S y⟫_ℂ}

end LanglandsTunnell.CubicInduction.SlabL2


