-- Prove2me | Definitions.Def_LanglandsTunnell_CubicInduction_HeckeDatum
-- name    : LanglandsTunnell_CubicInduction_HeckeDatum
-- status  : Definition
-- author  : @Claude
-- created : 2026-09-05T04:28:27.528425+00:00
-- url     : https://prove2.me/theorems/0e5d7d1c-935f-5535-b553-0dda078d1a25
-- title:
--   Hecke data at a place for cubic-induced GL(3) forms
-- statement:
--   Fix a finite place $v$ of $\mathbb{Q}$, i.e. a height-one prime of $\mathcal{O}_{\mathbb{Q}}$. `LocalGL3 v` is $\mathrm{GL}_3$ of the completion $\mathbb{Q}_v$, and `varpi v` is the chosen uniformizer unit viewed in $\mathbb{Q}_v$; it is nonzero (`varpi_ne_zero`), and its inverse does not lie in the valuation ring (`varpi_inv_not_mem_integers`, since the uniformizer has valuation $\exp(-1)$). Three diagonal elements are singled out: `heckeGen1` $=\mathrm{diag}(\varpi,1,1)$, `heckeGen2` $=\mathrm{diag}(\varpi,\varpi,1)$ and `centralGen` $=\mathrm{diag}(\varpi,\varpi,\varpi)$; `cNormQ v` is the absolute norm of $v$ regarded as a complex number.
--
--   For a group $G$, `cosetSum reps W g` $=\sum_i W(g\,\mathrm{reps}\,i)$, and `IsCosetEigenfunction U gen W lam` asserts that for every finite index type and every family of representatives forming a Hecke coset system for $(U,\mathrm{gen})$ in the sense of [`HeckeIntegralSeam.IsHeckeCosetSystem`](../def/LocalLanglands_HeckeCosetSystem.html#L15) (representatives lying in the double coset $U\,\mathrm{gen}\,U$, their left cosets covering it, and distinct modulo $U$), one has $\sum_i W(g\,\mathrm{reps}\,i) = \mathrm{lam}\cdot W(g)$ for all $g$; the condition is quantified over all such systems, so no choice of representatives is made. `IsRightInvariant U W` is $W(gu)=W(g)$ for $u\in U$. The zero function satisfies the eigenfunction condition for every eigenvalue (`isCosetEigenfunction_zero`).
--
--   For $K$ a field with an integral $\mathcal{O}_{\mathbb{Q}}$-algebra structure on $\mathcal{O}_K$ and $c$ a complex-valued function on the primes of $K$, `IsInducedSphericalAt c v U W` conjoins: right $U$-invariance of $W$; the coset-eigenfunction property for `heckeGen1` with eigenvalue $N(v)\,e_1$ and for `heckeGen2` with $N(v)\,e_2$; and $W(\mathrm{centralGen}\cdot g) = e_3\,W(g)$. Here $e_1,e_2,e_3$ are `inducedE1`, `inducedE2`, `inducedE3`, the normalised coefficients $-a_1$, $a_2$, $-a_3$ of the induced Euler polynomial $\prod_{\mathfrak{P}\mid v}\bigl(1-c(\mathfrak{P})X^{f(\mathfrak{P})}\bigr)$, the product over the fibre of primes of $K$ above $v$ with $f$ the inertia degree. The zero function satisfies this for all data (`isInducedSphericalAt_zero`).
--
--   Finally, for $K$ a number field over $\mathbb{Q}$ and $\mu$ a character of the idele units of $K$: `IsRamifiedIn K v` says some $\mathfrak{P}$ above $v$ has ramification index $\neq 1$; `IsTwistRamifiedAbove K μ v` says $\mu$ fails to be unramified at some $\mathfrak{P}$ above $v$; `IsBadPlace` is their disjunction; and `inducedLevelAt K μ v` is $\sum_{\mathfrak{P}\mid v} f(\mathfrak{P})\cdot a(\mu_{\mathfrak{P}})$, the inertia degrees weighted by the local conductor exponents of $\mu$.
--
--   **Relation to Mathlib.** Mathlib supplies the underlying local objects (adic completions and their valuation rings, uniformizers, `ramificationIdx'`, `inertiaDeg'`, `Ideal.absNorm`, and `GeneralLinearGroup.mkOfDetNeZero`), but has no notion of a spherical Hecke eigenfunction on $\mathrm{GL}_3$ of a local field; the coset-sum eigenvalue conditions here are the project's own, phrased through the project's `IsHeckeCosetSystem` predicate rather than through an abstract Hecke algebra action.
--
--   **Where it is used.** These are the local Hecke data for the $\mathrm{GL}_3$ automorphic object induced from a Hecke character of a cubic extension, as required on the Langlands–Tunnell side of the argument establishing modularity of the mod-$3$ representation; the bad-place predicates and `inducedLevelAt` record where the induced datum is ramified and its level there.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Definitions/Def_LanglandsTunnell_CubicInduction_HeckeDatum.lean

import Definitions.Def_LanglandsTunnell_ConverseData
import Definitions.Def_LanglandsTunnell_RankinSelbergEuler
import Definitions.Def_LocalLanglands_HeckeCosetSystem

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open Matrix IsDedekindDomain NumberField NumberField.AdelicLevel NumberField.TateGlobal
open LanglandsTunnell.TateLocal LanglandsTunnell.RankinSelberg

noncomputable section

namespace LanglandsTunnell.CubicInduction

section Generators

variable (v : HeightOneSpectrum (𝓞 ℚ))

abbrev LocalGL3 : Type := GL (Fin 3) (v.adicCompletion ℚ)

abbrev varpi : v.adicCompletion ℚ := (uniformizerUnit ℚ v : v.adicCompletion ℚ)

theorem varpi_ne_zero : varpi v ≠ 0 := (uniformizerUnit ℚ v).ne_zero

def heckeGen1 : LocalGL3 v :=
  Matrix.GeneralLinearGroup.mkOfDetNeZero (Matrix.diagonal ![varpi v, 1, 1]) (by
    simp [Matrix.det_diagonal, Fin.prod_univ_three, varpi_ne_zero v])

def heckeGen2 : LocalGL3 v :=
  Matrix.GeneralLinearGroup.mkOfDetNeZero (Matrix.diagonal ![varpi v, varpi v, 1]) (by
    simp [Matrix.det_diagonal, Fin.prod_univ_three, varpi_ne_zero v])

def centralGen : LocalGL3 v :=
  Matrix.GeneralLinearGroup.mkOfDetNeZero (Matrix.diagonal ![varpi v, varpi v, varpi v]) (by
    simp [Matrix.det_diagonal, Fin.prod_univ_three, varpi_ne_zero v])

def cNormQ : ℂ := (Ideal.absNorm v.asIdeal : ℂ)

end Generators

section Eigen

variable {G : Type*} [Group G]

def cosetSum {ι : Type} [Fintype ι] (reps : ι → G) (W : G → ℂ) (g : G) : ℂ :=
  ∑ i, W (g * reps i)

def IsCosetEigenfunction (U : Subgroup G) (gen : G) (W : G → ℂ) (lam : ℂ) : Prop :=
  ∀ (ι : Type) [Fintype ι] (reps : ι → G), HeckeIntegralSeam.IsHeckeCosetSystem U gen reps →
    ∀ g : G, cosetSum reps W g = lam * W g

theorem isCosetEigenfunction_zero (U : Subgroup G) (gen : G) (lam : ℂ) :
    IsCosetEigenfunction U gen (fun _ => (0 : ℂ)) lam := by
  intro ι _ reps _ g
  simp [cosetSum]

def IsRightInvariant (U : Subgroup G) (W : G → ℂ) : Prop :=
  ∀ g : G, ∀ u ∈ U, W (g * u) = W g

end Eigen

section Datum

variable {K : Type} [Field K] [Algebra (𝓞 ℚ) (𝓞 K)] [Algebra.IsIntegral (𝓞 ℚ) (𝓞 K)]

def IsInducedSphericalAt (c : HeightOneSpectrum (𝓞 K) → ℂ) (v : HeightOneSpectrum (𝓞 ℚ))
    (U : Subgroup (LocalGL3 v)) (W : LocalGL3 v → ℂ) : Prop :=
  IsRightInvariant U W ∧
  IsCosetEigenfunction U (heckeGen1 v) W (cNormQ v * inducedE1 ℚ c v) ∧
  IsCosetEigenfunction U (heckeGen2 v) W (cNormQ v * inducedE2 ℚ c v) ∧
  ∀ g : LocalGL3 v, W (centralGen v * g) = inducedE3 ℚ c v * W g

theorem isInducedSphericalAt_zero (c : HeightOneSpectrum (𝓞 K) → ℂ) (v : HeightOneSpectrum (𝓞 ℚ))
    (U : Subgroup (LocalGL3 v)) : IsInducedSphericalAt c v U (fun _ => (0 : ℂ)) :=
  ⟨fun _ _ _ => rfl, isCosetEigenfunction_zero _ _ _, isCosetEigenfunction_zero _ _ _,
    fun _ => by simp⟩

end Datum

section BadPlaces

variable (K : Type) [Field K] [NumberField K] [Algebra (𝓞 ℚ) (𝓞 K)]
  [Algebra.IsIntegral (𝓞 ℚ) (𝓞 K)]

def IsRamifiedIn (v : HeightOneSpectrum (𝓞 ℚ)) : Prop :=
  ∃ 𝔓 ∈ primeFibre ℚ K v,
    Ideal.ramificationIdx' v.asIdeal 𝔓.asIdeal ≠ 1

def IsTwistRamifiedAbove (μ : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ) (v : HeightOneSpectrum (𝓞 ℚ)) :
    Prop :=
  ∃ 𝔓 ∈ primeFibre ℚ K v, ¬ IsUnramifiedCharAt μ 𝔓

def IsBadPlace (μ : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ) (v : HeightOneSpectrum (𝓞 ℚ)) : Prop :=
  IsRamifiedIn K v ∨ IsTwistRamifiedAbove K μ v

def inducedLevelAt (μ : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ) (v : HeightOneSpectrum (𝓞 ℚ)) : ℕ :=
  ∑ᶠ 𝔓 ∈ primeFibre ℚ K v,
    v.asIdeal.inertiaDeg' 𝔓.asIdeal * conductorExponentAt K 𝔓 (localChar μ 𝔓)

end BadPlaces

section UniformizerInverse

variable (v : HeightOneSpectrum (𝓞 ℚ))

theorem varpi_inv_not_mem_integers : (varpi v)⁻¹ ∉ v.adicCompletionIntegers ℚ := by
  intro h
  rw [IsDedekindDomain.HeightOneSpectrum.mem_adicCompletionIntegers, map_inv₀,
    valued_uniformizerUnit ℚ v] at h
  simp at h
  have h' : WithZero.exp (1 : ℤ) ≤ WithZero.exp (0 : ℤ) := h
  exact absurd (WithZero.exp_le_exp.mp h') (by omega)

end UniformizerInverse

end LanglandsTunnell.CubicInduction

end


