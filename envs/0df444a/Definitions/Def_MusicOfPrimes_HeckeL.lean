-- Prove2me | Definitions.Def_MusicOfPrimes_HeckeL
-- name    : MusicOfPrimes_HeckeL
-- status  : Definition
-- author  : @LG
-- created : 2026-11-20T20:30:02.25645+00:00
-- url     : https://prove2.me/theorems/0644f176-3e1c-4d9f-a759-b389aac32bf1
-- title:
--   Hecke characters and Hecke $L$-functions over a number field
-- statement:
--   This definition layer introduces the Hecke $L$-functions attached to unitary Hecke characters of an arbitrary number field $F$, in the normalization of Masullo's *The Music of the Primes* (Introduction, §1.2).
--
--   A **unitary Hecke character** of $F$ (`HeckeChar F`) is a continuous homomorphism $\chi:\mathrm{GL}_1(\mathbf{A}_F)\to\mathbb{C}^\times$ from the idele group with $|\chi(g)|=1$ for all $g$, trivial on the principal ideles $F^\times$; equivalently, a continuous unitary character of the idele class group $C_F$. No unramifiedness restriction is imposed.
--
--   For $\operatorname{Re}(s)>1$, the **finite Hecke $L$-function** is the absolutely convergent Euler product
--
--   $$L_f(s,\chi)=\prod_{v\nmid\infty}\bigl(1-\chi_v(\pi_v)\,q_v^{-s}\bigr)^{-1},$$
--
--   where $v$ runs over the finite places of $F$, $q_v$ is the residue-field size, $\pi_v$ a uniformizer, and the local factor at a ramified place is $1$ (`heckeEulerProduct`). The **archimedean factor** (`heckeGammaFactor`) is
--
--   $$\gamma(s,\chi)=\prod_{v\mid\infty,\ v\ \mathrm{real}}\Gamma_{\mathbb{R}}\bigl(s+i\tau_v+\varepsilon_v\bigr)\ \prod_{v\mid\infty,\ v\ \mathrm{complex}}\Gamma_{\mathbb{C}}\bigl(s+i\tau_v+|m_v|/2\bigr),$$
--
--   where the parameters $\tau_v\in\mathbb{R}$, $\varepsilon_v\in\{0,1\}$, $m_v\in\mathbb{Z}$ describe the archimedean components of $\chi$ (`archτ`, `archm`, chosen via the proved archimedean-classification theorem). The **completed Hecke $L$-function** is $L(s,\chi)=\gamma(s,\chi)\,L_f(s,\chi)$.
--
--   Both functions are provided as total functions $\mathbb{C}\to\mathbb{C}$ (`heckeLFin`, `heckeLCompleted`). If $\chi$ is not a pure norm power $|\cdot|_F^{i\tau_0}$ (`normPowChar F τ₀`), the finite part continues to an entire function and the completed part to an entire function agreeing with $\gamma\cdot L_f$ on $\operatorname{Re}(s)>0$. If $\chi=|\cdot|_F^{i\tau_0}$, then $L_f(s,\chi)=\zeta_F(s+i\tau_0)$ and $L(s,\chi)=|d_F|^{-(s+i\tau_0)/2}\,\Lambda_F(s+i\tau_0)$, where $\zeta_F$ is the continued Dedekind zeta function and $\Lambda_F$ its completed version: the finite part has one simple pole, at $s=1-i\tau_0$, and the completed part has simple poles at $s=-i\tau_0$ and $s=1-i\tau_0$. The continuations are obtained by choice from the platform's proved Tate-thesis continuation theorems; uniqueness of analytic continuation makes the choices immaterial.
--
--   This layer is the analytic foundation for the mission's goal (the zero-free half-plane $\operatorname{Re}(s)>\tfrac12$ for $L_f$) and its critical-line milestone, and is reusable for any formalization involving Hecke $L$-functions over general number fields.
--
--   **Formalization Note.** Lean functions are total, so at the pole points the values are unspecified junk; every theorem about zeros excludes those points explicitly. Specification lemmas (`heckeLFinNe_spec`, `heckeLCompletedNe_spec`, `archτ_spec`, `archm_spec`, `normPowτ_spec`) record the defining properties of the chosen continuations. The completed function carries no conductor/discriminant prefactor; the symmetric normalization differs by the nowhere-vanishing factor $|d_F|^{s/2}$, leaving zero sets and pole sets unchanged.
-- source:
--   Alessandro Maria Masullo, The Music of the Primes (November 2026), https://math216.wordpress.com/wp-content/uploads/2026/11/the-music-of-the-primes.pdf — Introduction §1.2 (p. 12, definitions of L_f(s,chi) and L(s,chi)) and §1.8.5.1; Chapter 3 (Idelic Zeta Functions), §3.2, pp. 122-128. Continuation inputs: proved platform theorems NumberField.TateGlobal.exists_differentiable_eq_eulerProduct_and_eq_prod_Gamma_mul_of_archLocalChar_eq_of_ne_normPowChar, NumberField.TateGlobal.exists_archParam_weight_archLocalChar_eq_of_isUnitaryChar, NumberField.exists_differentiableOn_eq_tprod_inv_one_sub_absNorm_cpow_neg_and_tendsto_sub_one_mul, NumberField.exists_completedDedekindZeta_package (Tate's thesis; Cassels-Frohlich, Algebraic Number Theory, Ch. XV).

import Theorems.Thm_NumberField_TateGlobal_exists_differentiable_eq_eulerProduct_and_eq_prod_Gamma_mul_of_archLocalChar_eq_of_ne_normPowChar
import Theorems.Thm_NumberField_TateGlobal_exists_archParam_weight_archLocalChar_eq_of_isUnitaryChar
import Theorems.Thm_NumberField_exists_differentiableOn_eq_tprod_inv_one_sub_absNorm_cpow_neg_and_tendsto_sub_one_mul
import Theorems.Thm_NumberField_exists_completedDedekindZeta_package

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

open NumberField IsDedekindDomain AutomorphicForm NumberField.TateGlobal Complex
open scoped Classical BigOperators

noncomputable section

namespace MusicOfPrimes

variable (F : Type) [Field F] [NumberField F]

structure HeckeChar where
  toFun : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ
  cont : Continuous (fun z => ((toFun z : ℂˣ) : ℂ))
  unitary : IsUnitaryChar (𝓞 F) F toFun
  classChar : IsIdeleClassChar (𝓞 F) F toFun

def archτ (χ : HeckeChar F) : InfinitePlace F → ℝ :=
  Classical.choose (exists_archParam_weight_archLocalChar_eq_of_isUnitaryChar F χ.toFun χ.unitary χ.cont)

def archm (χ : HeckeChar F) : InfinitePlace F → ℤ :=
  Classical.choose (Classical.choose_spec
    (exists_archParam_weight_archLocalChar_eq_of_isUnitaryChar F χ.toFun χ.unitary χ.cont))

theorem archτ_spec (χ : HeckeChar F) :
    ∀ (v : InfinitePlace F) (x : (v.Completion)ˣ),
      0 < (InfinitePlace.Completion.extensionEmbedding v (x : v.Completion)).re →
      (InfinitePlace.Completion.extensionEmbedding v (x : v.Completion)).im = 0 →
      ((archLocalChar χ.toFun v x : ℂˣ) : ℂ) =
        (((ideleNorm F (archUnitHom v x)) : ℝ) : ℂ) ^ (((archτ F χ v : ℝ) : ℂ) * I) :=
  (Classical.choose_spec (Classical.choose_spec
    (exists_archParam_weight_archLocalChar_eq_of_isUnitaryChar F χ.toFun χ.unitary χ.cont))).1

theorem archm_spec (χ : HeckeChar F) :
    ∀ (v : InfinitePlace F) (x : (v.Completion)ˣ),
      ‖InfinitePlace.Completion.extensionEmbedding v (x : v.Completion)‖ = 1 →
      ((archLocalChar χ.toFun v x : ℂˣ) : ℂ) =
        (InfinitePlace.Completion.extensionEmbedding v (x : v.Completion)) ^ (archm F χ v) :=
  (Classical.choose_spec (Classical.choose_spec
    (exists_archParam_weight_archLocalChar_eq_of_isUnitaryChar F χ.toFun χ.unitary χ.cont))).2.1

def heckeEulerProduct (χ : HeckeChar F) (s : ℂ) : ℂ :=
  ∏' v : HeightOneSpectrum (𝓞 F),
    (1 - (if IsUnramifiedCharAt χ.toFun v then ((χ.toFun (uniformizerIdele F v) : ℂˣ) : ℂ) else 0) *
      (((Ideal.absNorm v.asIdeal : ℕ) : ℂ) ^ (-s)))⁻¹

def heckeGammaFactor (χ : HeckeChar F) (s : ℂ) : ℂ :=
  ∏ v : InfinitePlace F,
    (if v.IsReal then
      Gammaℝ (s + ((archτ F χ v : ℝ) : ℂ) * I + (((archm F χ v).natAbs % 2 : ℕ) : ℂ))
    else
      Gammaℂ (s + ((archτ F χ v : ℝ) : ℂ) * I + (((archm F χ v).natAbs : ℕ) : ℂ) / 2))

def IsNormPowChar (χ : HeckeChar F) : Prop := ∃ τ₀ : ℝ, χ.toFun = normPowChar F τ₀

def normPowτ (χ : HeckeChar F) (h : IsNormPowChar F χ) : ℝ := Classical.choose h

theorem normPowτ_spec (χ : HeckeChar F) (h : IsNormPowChar F χ) :
    χ.toFun = normPowChar F (normPowτ F χ h) := Classical.choose_spec h

private def neThm (χ : HeckeChar F) (h : ¬ IsNormPowChar F χ) :
    ∃ (L Λ : ℂ → ℂ), Differentiable ℂ L ∧ Differentiable ℂ Λ ∧
      (∀ w : ℂ, 1 < w.re → L w = heckeEulerProduct F χ w) ∧
      (∀ s : ℂ, 0 < s.re → Λ s = heckeGammaFactor F χ s * L s) :=
  exists_differentiable_eq_eulerProduct_and_eq_prod_Gamma_mul_of_archLocalChar_eq_of_ne_normPowChar
    F χ.toFun χ.cont χ.unitary χ.classChar (archτ F χ) (archm F χ) (archτ_spec F χ) (archm_spec F χ)
    (fun τ₀ hτ₀ => h ⟨τ₀, hτ₀⟩)

def heckeLFinNe (χ : HeckeChar F) (h : ¬ IsNormPowChar F χ) : ℂ → ℂ :=
  Classical.choose (neThm F χ h)

def heckeLCompletedNe (χ : HeckeChar F) (h : ¬ IsNormPowChar F χ) : ℂ → ℂ :=
  Classical.choose (Classical.choose_spec (neThm F χ h))

theorem heckeLFinNe_spec (χ : HeckeChar F) (h : ¬ IsNormPowChar F χ) :
    Differentiable ℂ (heckeLFinNe F χ h) ∧
    (∀ w : ℂ, 1 < w.re → heckeLFinNe F χ h w = heckeEulerProduct F χ w) :=
  let hs := Classical.choose_spec (Classical.choose_spec (neThm F χ h))
  ⟨hs.1, hs.2.2.1⟩

theorem heckeLCompletedNe_spec (χ : HeckeChar F) (h : ¬ IsNormPowChar F χ) :
    Differentiable ℂ (heckeLCompletedNe F χ h) ∧
    (∀ s : ℂ, 0 < s.re → heckeLCompletedNe F χ h s = heckeGammaFactor F χ s * heckeLFinNe F χ h s) :=
  let hs := Classical.choose_spec (Classical.choose_spec (neThm F χ h))
  ⟨hs.2.1, hs.2.2.2⟩

def dedekindZetaCont : ℂ → ℂ :=
  Classical.choose
    (NumberField.exists_differentiableOn_eq_tprod_inv_one_sub_absNorm_cpow_neg_and_tendsto_sub_one_mul F ∅)

def dedekindCompleted : ℂ → ℂ :=
  Classical.choose (NumberField.exists_completedDedekindZeta_package F)

def heckeLFin (χ : HeckeChar F) : ℂ → ℂ :=
  if h : IsNormPowChar F χ then
    fun s => dedekindZetaCont F (s + (normPowτ F χ h : ℂ) * I)
  else heckeLFinNe F χ h

def heckeLCompleted (χ : HeckeChar F) : ℂ → ℂ :=
  if h : IsNormPowChar F χ then
    fun s => ((((|NumberField.discr F| : ℤ) : ℂ)) ^ ((s + (normPowτ F χ h : ℂ) * I) / 2))⁻¹ *
      dedekindCompleted F (s + (normPowτ F χ h : ℂ) * I)
  else heckeLCompletedNe F χ h

end MusicOfPrimes

end


