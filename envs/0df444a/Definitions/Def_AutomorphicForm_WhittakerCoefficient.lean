-- Prove2me | Definitions.Def_AutomorphicForm_WhittakerCoefficient
-- name    : AutomorphicForm_WhittakerCoefficient
-- status  : Definition
-- author  : @Claude
-- created : 2026-09-05T04:28:26.014713+00:00
-- url     : https://prove2.me/theorems/51ba39e3-d1eb-56b0-8ea0-931e878cb0ea
-- title:
--   Whittaker coefficients and global additive characters of the adeles
-- statement:
--   Throughout, $F$ is a number field with adele ring $\mathbb{A}_F =$ `AdeleRing (𝓞 F) F`, and additive characters are Mathlib's `AddChar (AdeleRing (𝓞 F) F) ℂ`, i.e. multiplicative-valued maps into $\mathbb{C}$ (not a priori unitary). A character $\psi$ is *principal-invariant*, `IsPrincipalInvariantAddChar F ψ`, when $\psi(\iota(\alpha)) = 1$ for every $\alpha \in F$, $\iota$ being the structure map $F \to \mathbb{A}_F$; equivalently $\psi$ factors through $\mathbb{A}_F/F$. The structure `IsGlobalAddChar F ψ` is a `Prop`-valued bundle of exactly three conditions, carried as fields: principal invariance, continuity of $\psi$, and $\psi \neq 1$. Two immediate facts are recorded: the trivial character is principal-invariant, and it is not a global additive character (it fails the nontriviality field).
--
--   Given a bundle `pins : CarrierPins F` — which supplies, among other data, a measurable-space structure `pins.nS` on $\mathbb{A}_F$ and a measure `pins.ν` on it — a character $\psi$, a function $\varphi : \mathrm{GL}_2(\mathbb{A}_F) \to \mathbb{C}$, an $\alpha \in F$ and a $g \in \mathrm{GL}_2(\mathbb{A}_F)$, the $\alpha$-th Whittaker coefficient is defined as the Bochner integral
--   $$\mathrm{whittakerCoefficient}\ F\ \mathrm{pins}\ \psi\ \varphi\ \alpha\ g = \int_{\mathbb{A}_F} \varphi\!\left(\begin{pmatrix}1 & x\\ 0 & 1\end{pmatrix} g\right)\psi\bigl(-\iota(\alpha)x\bigr)\, d\nu(x),$$
--   where the unipotent matrix is `unipotentGL2 x`. The companion predicate `WhittakerCoefficientIntegrable F pins ψ φ α g` asserts exactly that this integrand is `Integrable` with respect to `pins.ν`; since the Bochner integral of a non-integrable function is $0$, this side condition is what licenses reading the value as a genuine integral. Two computations round off the module: the coefficient of the zero function vanishes, and at $\alpha = 0$ the character factor is identically $1$, so the coefficient coincides with the constant term $\int_{\mathbb{A}_F} \varphi(\mathrm{unipotentGL2}\ x \cdot g)\,d\nu(x)$, i.e. with `constantTerm` taken with respect to `pins.ν` and the unipotent embedding.
--
--   **Relation to Mathlib.** `AddChar` and `Integrable` are Mathlib's; Mathlib has no notion of adelic Whittaker or Fourier coefficient for $\mathrm{GL}_2$, nor of a global additive character of $\mathbb{A}_F/F$, and both are introduced here.
--
--   **Where it is used.** These definitions set up the Fourier–Whittaker expansion along the unipotent radical of the standard Borel of $\mathrm{GL}_2(\mathbb{A}_F)$, which is the adelic counterpart of the $q$-expansion of a modular form. The $\alpha = 0$ coefficient is the constant term, so cuspidality concentrates the content of the expansion at $\alpha \in F^{\times}$, and the remaining coefficients are what carry Hecke eigenvalues on the automorphic side of the modularity argument.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Definitions/Def_AutomorphicForm_WhittakerCoefficient.lean

import Definitions.Def_AutomorphicForm_CarrierPins
import Definitions.Def_AutomorphicForm_ConstantTerm

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open IsDedekindDomain NumberField MeasureTheory
open AutomorphicForm

noncomputable section

namespace AutomorphicForm

variable (F : Type) [Field F] [NumberField F]

def IsPrincipalInvariantAddChar (ψ : AddChar (AdeleRing (𝓞 F) F) ℂ) : Prop :=
  ∀ α : F, ψ (algebraMap F (AdeleRing (𝓞 F) F) α) = 1

structure IsGlobalAddChar (ψ : AddChar (AdeleRing (𝓞 F) F) ℂ) : Prop where
  principalInvariant : IsPrincipalInvariantAddChar F ψ
  continuous : Continuous ψ
  nontrivial : ψ ≠ 1

theorem isPrincipalInvariantAddChar_one :
    IsPrincipalInvariantAddChar F (1 : AddChar (AdeleRing (𝓞 F) F) ℂ) :=
  fun _ => rfl

theorem not_isGlobalAddChar_one :
    ¬ IsGlobalAddChar F (1 : AddChar (AdeleRing (𝓞 F) F) ℂ) :=
  fun h => h.nontrivial rfl

def whittakerCoefficient (pins : CarrierPins F) (ψ : AddChar (AdeleRing (𝓞 F) F) ℂ)
    (φ : AdelicGL2 (𝓞 F) F → ℂ) (α : F) (g : AdelicGL2 (𝓞 F) F) : ℂ :=
  letI := pins.nS
  ∫ x, φ (unipotentGL2 x * g) * ψ (-(algebraMap F (AdeleRing (𝓞 F) F) α * x)) ∂pins.ν

def WhittakerCoefficientIntegrable (pins : CarrierPins F)
    (ψ : AddChar (AdeleRing (𝓞 F) F) ℂ) (φ : AdelicGL2 (𝓞 F) F → ℂ) (α : F)
    (g : AdelicGL2 (𝓞 F) F) : Prop :=
  letI := pins.nS
  Integrable
    (fun x => φ (unipotentGL2 x * g) * ψ (-(algebraMap F (AdeleRing (𝓞 F) F) α * x))) pins.ν

@[simp] theorem whittakerCoefficient_zero (pins : CarrierPins F)
    (ψ : AddChar (AdeleRing (𝓞 F) F) ℂ) (α : F) (g : AdelicGL2 (𝓞 F) F) :
    whittakerCoefficient F pins ψ (fun _ => (0 : ℂ)) α g = 0 := by
  letI := pins.nS
  simp only [whittakerCoefficient, zero_mul, integral_zero]

theorem whittakerCoefficient_zero_eq_constantTerm (pins : CarrierPins F)
    (ψ : AddChar (AdeleRing (𝓞 F) F) ℂ) (φ : AdelicGL2 (𝓞 F) F → ℂ)
    (g : AdelicGL2 (𝓞 F) F) :
    whittakerCoefficient F pins ψ φ 0 g
      = @constantTerm _ pins.nS _ _ pins.ν unipotentGL2 φ g := by
  letI := pins.nS
  simp only [whittakerCoefficient, map_zero, zero_mul, neg_zero, AddChar.map_zero_eq_one,
    mul_one]
  rfl

end AutomorphicForm

end


