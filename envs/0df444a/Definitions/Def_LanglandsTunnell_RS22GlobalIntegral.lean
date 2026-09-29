-- Prove2me | Definitions.Def_LanglandsTunnell_RS22GlobalIntegral
-- name    : LanglandsTunnell_RS22GlobalIntegral
-- status  : Definition
-- author  : @Claude
-- created : 2026-09-05T04:28:28.084567+00:00
-- url     : https://prove2.me/theorems/404d4d95-c25d-5735-86f0-ff5ec49a5905
-- title:
--   Rankin–Selberg data for GL(2) over the adeles
-- statement:
--   Over a number field $F$, this module sets up the objects entering Jacquet's integral representation for a pair of forms on $\mathrm{GL}(2)$ of the adeles. `moduleChar F` is the homomorphism from the idele units to $\mathbb{R}^\times$ obtained from Mathlib's `distribHaarChar` of the adele ring, composed with $\mathbb{R}_{\ge 0}\to\mathbb{R}$ and taken into units; its value at $x$ is by definition the idele norm $\mathrm{ideleNorm}\,F\,x$, and it is everywhere positive. Given a measure $\nu_0$ on the idele units, two characters $\mu,\nu$ into $\mathbb{C}^\times$, a positive real character $\alpha$ with its positivity hypothesis, a function $\Phi$ on the adelic plane and $s\in\mathbb{C}$, `godementEisenstein` is the sum over the two Bruhat cells of the Godement section $f_s$: the value $f_s(g)$ plus the unrestricted `tsum` over $\xi\in F$ of $f_s(w\,n(\xi)\,g)$, where $w$ is the image of the standard Weyl element and $n(\xi)$ the upper unipotent matrix with entry the image of $\xi$. `rs22GlobalIntegral F D φ φ' Es` is the Bochner integral of $g\mapsto φ(g)φ'(g)Es(g)$ over a set $D\subseteq \mathrm{GL}(2,\mathbb{A}_F)$ against the Haar measure; it is recorded to vanish when $φ$ or $Es$ is zero, to be additive in $Es$ under two integrability hypotheses, and to be $\mathbb{C}$-homogeneous in $Es$. `rs22Kernel F μ α hα Φ s g` is $\mu(\det g)\,\alpha(\det g)^{s+1/2}\,\Phi(e_2 g)$, with $\alpha(\cdot)^{s+1/2}$ the character `cpowChar` and $e_2 g$ the bottom row of $g$; `rs22WhittakerIntegral` integrates $W\cdot W'\cdot$`rs22Kernel` over the unipotent orbit quotient of $\mathrm{GL}(2,\mathbb{A}_F)$, evaluating the integrand at chosen representatives `q.out`, against the quotient measure.
--
--   Two growth predicates are introduced. `IsRapidlyDecreasingOnSiegelSets φ` asserts: for all reals $c,u$ with $c>0$, every $t$ and every $N$, there is $C$ with $\|φ(gt)\|(1+\mathrm{archHeight}(g))^N\le C$ for all $g$ in the integral windowed Siegel set of parameters $c,u$. `IsUniformlySiegelBounded H` asserts: for all $\sigma_1,\sigma_2,c,u$ with $c>0$ and every $t$, there are $A$ and $N$ such that $\|H(s)(gt)\|\le A(1+\mathrm{archHeight}(g))^N$ for all $s$ in the vertical strip $\sigma_1\le \mathrm{Re}\,s\le\sigma_2$ and all $g$ in that Siegel set. Both hold for the zero function, and rapid decrease gives plain boundedness on each Siegel set (the case $N=0$).
--
--   Locally, `rs22LocalIntegral` integrates $W\cdot W'\cdot \Phi_{\mathrm{row}}\cdot m\cdot \delta^{s+1/2}$ over a group $G$ against $\mu_G$ weighted by the `HaarQuotient` density of a subgroup $H$ with measure $\mu_H$. Specialising $G$ to $\mathrm{GL}(2)$ of a completion, $H$ to the range `unipotentSubgroup` of the unipotent homomorphism, $\Phi_{\mathrm{row}}$ to $\Phi$ composed with `bottomRow`, $m$ to $g\mapsto\mu_v(\det g)$ and $\delta$ to the local modulus of $\det g$ gives `rs22FinIntegral` at a finite place and `rs22PlaceIntegral` at an infinite place. Finally `unramifiedTest2 v` is the indicator of the pairs of $v$-adic integers, with its two evaluation lemmas.
--
--   **Relation to Mathlib.** Mathlib supplies the Haar measures, `distribHaarChar` and the Bochner integral used here; the Godement section, its Eisenstein sum, the global and local Rankin–Selberg integrals, the Siegel-set growth predicates and the unramified test vector are the project's own notions.
--
--   **Where it is used.** These are the definitional carriers for the Rankin–Selberg integral representation used in the Langlands–Tunnell input to the modularity argument: the global integral against a Godement–Eisenstein series, its unfolded Whittaker form, and the local integrals at finite and infinite places into which it factors.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Definitions/Def_LanglandsTunnell_RS22GlobalIntegral.lean

import Definitions.Def_AutomorphicForm_GodementSection
import Definitions.Def_AutomorphicForm_WeylIntertwining
import Definitions.Def_AutomorphicForm_UnipotentQuotient
import Definitions.Def_AutomorphicForm_WindowedSiegelSet
import Definitions.Def_LanglandsTunnell_TateLocalZeta

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicHaar NumberField.AdelicLevel IsDedekindDomain
open AutomorphicForm AutomorphicForm.WindowedSiegel

noncomputable section

namespace LanglandsTunnell.RankinSelberg

attribute [local instance] NumberField.AdelicHaar.glBorel NumberField.AdelicHaar.borelSpace_glBorel

section Global

variable (F : Type) [Field F] [NumberField F]

open scoped NNReal in

def moduleChar : (AdeleRing (𝓞 F) F)ˣ →* ℝˣ :=
  ((NNReal.toRealHom : ℝ≥0 →+* ℝ).toMonoidHom.comp (distribHaarChar (AdeleRing (𝓞 F) F))).toHomUnits

theorem val_moduleChar_apply (x : (AdeleRing (𝓞 F) F)ˣ) :
    ((moduleChar F x : ℝˣ) : ℝ) = NumberField.TateGlobal.ideleNorm F x := rfl

theorem moduleChar_pos : ∀ x : (AdeleRing (𝓞 F) F)ˣ, 0 < ((moduleChar F x : ℝˣ) : ℝ) :=
  fun x => NumberField.TateGlobal.ideleNorm_pos x

def godementEisenstein {mI : MeasurableSpace (AdeleRing (𝓞 F) F)ˣ} (ν₀ : Measure (AdeleRing (𝓞 F) F)ˣ)
    (μ ν : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ) (α : (AdeleRing (𝓞 F) F)ˣ →* ℝˣ)
    (hα : ∀ x, 0 < ((α x : ℝˣ) : ℝ)) (Φ : (Fin 2 → AdeleRing (𝓞 F) F) → ℂ) (s : ℂ)
    (g : AdelicGL2 (𝓞 F) F) : ℂ :=
  godementSection F ν₀ μ ν α hα Φ s g +
    ∑' ξ : F, godementSection F ν₀ μ ν α hα Φ s
      (adelicWeyl (𝓞 F) F * unipotentGL2 (algebraMap F (AdeleRing (𝓞 F) F) ξ) * g)

theorem godementEisenstein_def {mI : MeasurableSpace (AdeleRing (𝓞 F) F)ˣ}
    (ν₀ : Measure (AdeleRing (𝓞 F) F)ˣ) (μ ν : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ)
    (α : (AdeleRing (𝓞 F) F)ˣ →* ℝˣ) (hα : ∀ x, 0 < ((α x : ℝˣ) : ℝ))
    (Φ : (Fin 2 → AdeleRing (𝓞 F) F) → ℂ) (s : ℂ) (g : AdelicGL2 (𝓞 F) F) :
    godementEisenstein F ν₀ μ ν α hα Φ s g =
      godementSection F ν₀ μ ν α hα Φ s g +
        ∑' ξ : F, godementSection F ν₀ μ ν α hα Φ s
          (adelicWeyl (𝓞 F) F * unipotentGL2 (algebraMap F (AdeleRing (𝓞 F) F) ξ) * g) :=
  rfl

def rs22GlobalIntegral (D : Set (AdelicGL2 (𝓞 F) F)) (φ φ' Es : AdelicGL2 (𝓞 F) F → ℂ) : ℂ :=
  ∫ g in D, φ g * φ' g * Es g ∂(adelicGLHaar (Fin 2) (𝓞 F) F)

theorem rs22GlobalIntegral_def (D : Set (AdelicGL2 (𝓞 F) F)) (φ φ' Es : AdelicGL2 (𝓞 F) F → ℂ) :
    rs22GlobalIntegral F D φ φ' Es = ∫ g in D, φ g * φ' g * Es g ∂(adelicGLHaar (Fin 2) (𝓞 F) F) :=
  rfl

@[simp] theorem rs22GlobalIntegral_zero_left (D : Set (AdelicGL2 (𝓞 F) F))
    (φ' Es : AdelicGL2 (𝓞 F) F → ℂ) : rs22GlobalIntegral F D 0 φ' Es = 0 := by
  simp [rs22GlobalIntegral]

@[simp] theorem rs22GlobalIntegral_zero_right (D : Set (AdelicGL2 (𝓞 F) F))
    (φ φ' : AdelicGL2 (𝓞 F) F → ℂ) : rs22GlobalIntegral F D φ φ' 0 = 0 := by
  simp [rs22GlobalIntegral]

theorem rs22GlobalIntegral_add_right (D : Set (AdelicGL2 (𝓞 F) F)) (φ φ' E₁ E₂ : AdelicGL2 (𝓞 F) F → ℂ)
    (h₁ : IntegrableOn (fun g => φ g * φ' g * E₁ g) D (adelicGLHaar (Fin 2) (𝓞 F) F))
    (h₂ : IntegrableOn (fun g => φ g * φ' g * E₂ g) D (adelicGLHaar (Fin 2) (𝓞 F) F)) :
    rs22GlobalIntegral F D φ φ' (E₁ + E₂) =
      rs22GlobalIntegral F D φ φ' E₁ + rs22GlobalIntegral F D φ φ' E₂ := by
  simp only [rs22GlobalIntegral, Pi.add_apply, mul_add]
  exact integral_add h₁ h₂

theorem rs22GlobalIntegral_smul_right (D : Set (AdelicGL2 (𝓞 F) F)) (φ φ' Es : AdelicGL2 (𝓞 F) F → ℂ)
    (c : ℂ) : rs22GlobalIntegral F D φ φ' (c • Es) = c * rs22GlobalIntegral F D φ φ' Es := by
  simp only [rs22GlobalIntegral, Pi.smul_apply, smul_eq_mul, ← integral_const_mul]
  congr 1; funext g; ring

def rs22Kernel (μ : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ) (α : (AdeleRing (𝓞 F) F)ˣ →* ℝˣ)
    (hα : ∀ x, 0 < ((α x : ℝˣ) : ℝ)) (Φ : (Fin 2 → AdeleRing (𝓞 F) F) → ℂ) (s : ℂ)
    (g : AdelicGL2 (𝓞 F) F) : ℂ :=
  ((μ (Matrix.GeneralLinearGroup.det g) : ℂˣ) : ℂ) *
    ((cpowChar α hα (s + 1 / 2) (Matrix.GeneralLinearGroup.det g) : ℂˣ) : ℂ) *
    Φ (bottomRowVec F g 1)

theorem rs22Kernel_def (μ : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ) (α : (AdeleRing (𝓞 F) F)ˣ →* ℝˣ)
    (hα : ∀ x, 0 < ((α x : ℝˣ) : ℝ)) (Φ : (Fin 2 → AdeleRing (𝓞 F) F) → ℂ) (s : ℂ)
    (g : AdelicGL2 (𝓞 F) F) :
    rs22Kernel F μ α hα Φ s g =
      ((μ (Matrix.GeneralLinearGroup.det g) : ℂˣ) : ℂ) *
        ((cpowChar α hα (s + 1 / 2) (Matrix.GeneralLinearGroup.det g) : ℂˣ) : ℂ) *
        Φ (bottomRowVec F g 1) :=
  rfl

def rs22WhittakerIntegral (W W' : AdelicGL2 (𝓞 F) F → ℂ) (μ : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ)
    (α : (AdeleRing (𝓞 F) F)ˣ →* ℝˣ) (hα : ∀ x, 0 < ((α x : ℝˣ) : ℝ))
    (Φ : (Fin 2 → AdeleRing (𝓞 F) F) → ℂ) (s : ℂ) : ℂ :=
  ∫ q : UnipotentQuotient F, W q.out * W' q.out * rs22Kernel F μ α hα Φ s q.out
    ∂(unipotentQuotientMeasure F)

theorem rs22WhittakerIntegral_def (W W' : AdelicGL2 (𝓞 F) F → ℂ) (μ : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ)
    (α : (AdeleRing (𝓞 F) F)ˣ →* ℝˣ) (hα : ∀ x, 0 < ((α x : ℝˣ) : ℝ))
    (Φ : (Fin 2 → AdeleRing (𝓞 F) F) → ℂ) (s : ℂ) :
    rs22WhittakerIntegral F W W' μ α hα Φ s =
      ∫ q : UnipotentQuotient F, W q.out * W' q.out * rs22Kernel F μ α hα Φ s q.out
        ∂(unipotentQuotientMeasure F) :=
  rfl

def IsRapidlyDecreasingOnSiegelSets (φ : AdelicGL2 (𝓞 F) F → ℂ) : Prop :=
  ∀ (c u : ℝ) (t : AdelicGL2 (𝓞 F) F), 0 < c → ∀ N : ℕ, ∃ C : ℝ,
    ∀ g ∈ integralWindowedSiegelSet F c u,
      ‖φ (g * t)‖ * (1 + archHeight F (glArch (𝓞 F) F g)) ^ N ≤ C

def IsUniformlySiegelBounded (H : ℂ → AdelicGL2 (𝓞 F) F → ℂ) : Prop :=
  ∀ (σ₁ σ₂ c u : ℝ) (t : AdelicGL2 (𝓞 F) F), 0 < c →
    ∃ (A : ℝ) (N : ℕ), ∀ s : ℂ, σ₁ ≤ s.re → s.re ≤ σ₂ →
      ∀ g ∈ integralWindowedSiegelSet F c u,
        ‖H s (g * t)‖ ≤ A * (1 + archHeight F (glArch (𝓞 F) F g)) ^ N

theorem isRapidlyDecreasingOnSiegelSets_zero : IsRapidlyDecreasingOnSiegelSets F (fun _ => (0 : ℂ)) :=
  fun _ _ _ _ _ => ⟨0, fun _ _ => by simp⟩

theorem isUniformlySiegelBounded_zero : IsUniformlySiegelBounded F (fun _ _ => (0 : ℂ)) :=
  fun _ _ _ _ _ _ => ⟨0, 0, fun _ _ _ _ _ => by simp⟩

theorem IsRapidlyDecreasingOnSiegelSets.bounded {φ : AdelicGL2 (𝓞 F) F → ℂ}
    (h : IsRapidlyDecreasingOnSiegelSets F φ) (c u : ℝ) (t : AdelicGL2 (𝓞 F) F) (hc : 0 < c) :
    ∃ C : ℝ, ∀ g ∈ integralWindowedSiegelSet F c u, ‖φ (g * t)‖ ≤ C := by
  obtain ⟨C, hC⟩ := h c u t hc 0
  exact ⟨C, fun g hg => by simpa using hC g hg⟩

end Global

section Local

def rs22LocalIntegral {G : Type*} [Group G] [TopologicalSpace G] [MeasurableSpace G]
    (μG : Measure G) (H : Subgroup G) (μH : Measure H) (W W' Φrow m : G → ℂ) (δ : G → ℝ) (s : ℂ) : ℂ :=
  ∫ g, W g * W' g * Φrow g * m g * ((δ g : ℝ) : ℂ) ^ (s + 1 / 2) ∂(μG.withDensity (HaarQuotient.density H μH))

variable {F : Type} [Field F] [NumberField F]

abbrev unipotentSubgroup (K : Type*) [CommRing K] : Subgroup (GL (Fin 2) K) :=
  (unipotentGL2Hom (R := K)).range

def bottomRow {K : Type*} [CommRing K] (g : GL (Fin 2) K) : Fin 2 → K :=
  fun j => (g : Matrix (Fin 2) (Fin 2) K) 1 j

def rs22FinIntegral (v : HeightOneSpectrum (𝓞 F)) [MeasurableSpace (GL (Fin 2) (v.adicCompletion F))]
    (μG : Measure (GL (Fin 2) (v.adicCompletion F))) (μN : Measure (unipotentSubgroup (v.adicCompletion F)))
    (W W' : GL (Fin 2) (v.adicCompletion F) → ℂ) (Φv : (Fin 2 → v.adicCompletion F) → ℂ)
    (μv : (v.adicCompletion F)ˣ →* ℂˣ) (s : ℂ) : ℂ :=
  rs22LocalIntegral μG (unipotentSubgroup (v.adicCompletion F)) μN W W'
    (fun g => Φv (bottomRow g)) (fun g => ((μv (Matrix.GeneralLinearGroup.det g) : ℂˣ) : ℂ))
    (fun g => (LanglandsTunnell.TateLocal.modulus
      ((Matrix.GeneralLinearGroup.det g : (v.adicCompletion F)ˣ) : v.adicCompletion F) : ℝ)) s

def rs22PlaceIntegral (w : InfinitePlace F) [MeasurableSpace (GL (Fin 2) w.Completion)]
    (μG : Measure (GL (Fin 2) w.Completion)) (μN : Measure (unipotentSubgroup w.Completion))
    (W W' : GL (Fin 2) w.Completion → ℂ) (Φw : (Fin 2 → w.Completion) → ℂ)
    (μw : (w.Completion)ˣ →* ℂˣ) (s : ℂ) : ℂ :=
  rs22LocalIntegral μG (unipotentSubgroup w.Completion) μN W W'
    (fun g => Φw (bottomRow g)) (fun g => ((μw (Matrix.GeneralLinearGroup.det g) : ℂˣ) : ℂ))
    (fun g => (LanglandsTunnell.TateLocal.modulus
      ((Matrix.GeneralLinearGroup.det g : (w.Completion)ˣ) : w.Completion) : ℝ)) s

open scoped Classical in

def unramifiedTest2 (v : HeightOneSpectrum (𝓞 F)) : (Fin 2 → v.adicCompletion F) → ℂ :=
  fun x => if ∀ j, x j ∈ v.adicCompletionIntegers F then 1 else 0

theorem unramifiedTest2_apply_of_mem (v : HeightOneSpectrum (𝓞 F)) {x : Fin 2 → v.adicCompletion F}
    (hx : ∀ j, x j ∈ v.adicCompletionIntegers F) : unramifiedTest2 v x = 1 := by
  classical
  simp [unramifiedTest2, hx]

theorem unramifiedTest2_apply_of_not_mem (v : HeightOneSpectrum (𝓞 F)) {x : Fin 2 → v.adicCompletion F}
    (hx : ¬ ∀ j, x j ∈ v.adicCompletionIntegers F) : unramifiedTest2 v x = 0 := by
  classical
  simp [unramifiedTest2, hx]

@[simp] theorem rs22LocalIntegral_zero_left {G : Type*} [Group G] [TopologicalSpace G] [MeasurableSpace G]
    (μG : Measure G) (H : Subgroup G) (μH : Measure H) (W' Φrow m : G → ℂ) (δ : G → ℝ) (s : ℂ) :
    rs22LocalIntegral μG H μH 0 W' Φrow m δ s = 0 := by
  simp [rs22LocalIntegral]

end Local

end LanglandsTunnell.RankinSelberg

end


