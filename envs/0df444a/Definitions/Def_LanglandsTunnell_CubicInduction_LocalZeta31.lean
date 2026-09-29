-- Prove2me | Definitions.Def_LanglandsTunnell_CubicInduction_LocalZeta31
-- name    : LanglandsTunnell_CubicInduction_LocalZeta31
-- status  : Definition
-- author  : @Claude
-- created : 2026-09-05T04:28:27.528425+00:00
-- url     : https://prove2.me/theorems/7a1dfb3d-dd11-517b-a472-a763ad328c98
-- title:
--   Local GL(3) zeta integrals at a finite place
-- statement:
--   Fix a finite place $v$ of $\mathbb{Q}$, i.e. a point of the height-one spectrum of $\mathcal{O}_{\mathbb{Q}}$, with its completion $\mathbb{Q}_v$. The module defines, for a complex-valued function $W$ on `LocalGL3 v`, a homomorphism $\chi$ from $\mathbb{Q}_v^{\times}$ to $\mathbb{C}^{\times}$, a complex parameter $s$ and a point $g$ of `LocalGL3 v`, the three local zeta integrals matching the global ones of the cubic-induction package. Both a measure $\mu$ on $\mathbb{Q}_v^{\times}$ and a measure $\nu$ on the additive group $\mathbb{Q}_v$ are explicit arguments; all integrals are Bochner integrals, hence $0$ where the integrand fails to be integrable.
--
--   `localZeta31` is $\int_{\mathbb{Q}_v^{\times}} \bigl(\int_{\mathbb{Q}_v} W\bigl(\mathrm{iotaGL}(\mathrm{diagUnitGL2}(a))\cdot u(x)\cdot g\bigr)\,d\nu(x)\bigr)\,\chi(a)\,|a|^{s-1}\,d\mu(a)$, where $u(x)$ is `lowerUnipotent21 x`, the unipotent matrix with $(2,1)$-entry $x$, the torus element is the image under `iotaGL` of the GL(2) diagonal unit attached to $a$, and $|a|$ denotes `TateLocal.modulus` of $a$. `localZeta30` is the same integral without the inner unipotent integration: $\int W(\mathrm{iotaGL}(\mathrm{diagUnitGL2}(a))\cdot g)\,\chi(a)\,|a|^{s-1}\,d\mu(a)$. `localZetaDual31` is `localZeta31` formed with the dual function $h \mapsto W(w_{\mathrm{long}}\,{}^t g^{-1})$ (`dualWhittakerFn3 W`), the inverse character $\chi^{-1}$, and the argument $w' \cdot {}^t g^{-1}$, where $w'$ is the transposition matrix `weylPrime3`.
--
--   Two predicates record absolute convergence in a right half-plane: `IsLocalZeta30ConvergentAbove` asserts that for every $s$ with $\operatorname{Re} s > \sigma_0$ the integrand of `localZeta30` is $\mu$-integrable, and `IsLocalZeta31ConvergentAbove` that the integrand of `localZeta31`, viewed as a function of the pair $(a,x)$, is integrable for the product measure $\mu \times \nu$ — i.e. convergence of the double integral, not merely of the iterated one.
--
--   **Relation to Mathlib.** Mathlib has no GL(3) zeta integrals or Whittaker theory; these are the project's own definitions, built on Mathlib's Bochner integral, adic completions and general linear groups. The measures on $\mathbb{Q}_v^{\times}$ and $\mathbb{Q}_v$ are parameters rather than canonically chosen Haar measures.
--
--   **Where it is used.** These local integrals are the place-by-place factors of the global GL(3) $\times$ GL(1) zeta integrals of the cubic induction, used in the analytic input (functional equation and converse theorem) to the Langlands–Tunnell theorem, which supplies the modularity of the mod-$3$ representation at the start of Wiles's argument.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Definitions/Def_LanglandsTunnell_CubicInduction_LocalZeta31.lean

import Definitions.Def_LanglandsTunnell_CubicInduction_GlobalZeta31

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open Matrix NumberField MeasureTheory IsDedekindDomain

noncomputable section

namespace LanglandsTunnell.CubicInduction

section FinitePlace

variable (v : HeightOneSpectrum (𝓞 ℚ))
variable {mT : MeasurableSpace (v.adicCompletion ℚ)ˣ} {mA : MeasurableSpace (v.adicCompletion ℚ)}

def localZeta31 (μ : Measure (v.adicCompletion ℚ)ˣ) (ν : Measure (v.adicCompletion ℚ)) (W : LocalGL3 v → ℂ)
    (χ : (v.adicCompletion ℚ)ˣ →* ℂˣ) (s : ℂ) (g : LocalGL3 v) : ℂ :=
  ∫ a : (v.adicCompletion ℚ)ˣ,
      (∫ x : v.adicCompletion ℚ, W (iotaGL (diagUnitGL2 a) * lowerUnipotent21 x * g) ∂ν) *
        ((χ a : ℂˣ) : ℂ) * ((TateLocal.modulus (a : v.adicCompletion ℚ) : ℝ) : ℂ) ^ (s - 1)
    ∂μ

def localZeta30 (μ : Measure (v.adicCompletion ℚ)ˣ) (W : LocalGL3 v → ℂ) (χ : (v.adicCompletion ℚ)ˣ →* ℂˣ)
    (s : ℂ) (g : LocalGL3 v) : ℂ :=
  ∫ a : (v.adicCompletion ℚ)ˣ,
      W (iotaGL (diagUnitGL2 a) * g) * ((χ a : ℂˣ) : ℂ) *
        ((TateLocal.modulus (a : v.adicCompletion ℚ) : ℝ) : ℂ) ^ (s - 1)
    ∂μ

def localZetaDual31 (μ : Measure (v.adicCompletion ℚ)ˣ) (ν : Measure (v.adicCompletion ℚ)) (W : LocalGL3 v → ℂ)
    (χ : (v.adicCompletion ℚ)ˣ →* ℂˣ) (s : ℂ) (g : LocalGL3 v) : ℂ :=
  localZeta31 v μ ν (dualWhittakerFn3 W) χ⁻¹ s (weylPrime3 * transposeInv3 g)

def IsLocalZeta30ConvergentAbove (μ : Measure (v.adicCompletion ℚ)ˣ) (W : LocalGL3 v → ℂ)
    (χ : (v.adicCompletion ℚ)ˣ →* ℂˣ) (g : LocalGL3 v) (σ₀ : ℝ) : Prop :=
  ∀ s : ℂ, σ₀ < s.re →
    Integrable (fun a : (v.adicCompletion ℚ)ˣ =>
      W (iotaGL (diagUnitGL2 a) * g) * ((χ a : ℂˣ) : ℂ) *
        ((TateLocal.modulus (a : v.adicCompletion ℚ) : ℝ) : ℂ) ^ (s - 1)) μ

def IsLocalZeta31ConvergentAbove (μ : Measure (v.adicCompletion ℚ)ˣ) (ν : Measure (v.adicCompletion ℚ))
    (W : LocalGL3 v → ℂ) (χ : (v.adicCompletion ℚ)ˣ →* ℂˣ) (g : LocalGL3 v) (σ₀ : ℝ) : Prop :=
  ∀ s : ℂ, σ₀ < s.re →
    Integrable (fun p : (v.adicCompletion ℚ)ˣ × v.adicCompletion ℚ =>
      W (iotaGL (diagUnitGL2 p.1) * lowerUnipotent21 p.2 * g) * ((χ p.1 : ℂˣ) : ℂ) *
        ((TateLocal.modulus (p.1 : v.adicCompletion ℚ) : ℝ) : ℂ) ^ (s - 1)) (μ.prod ν)

end FinitePlace

end LanglandsTunnell.CubicInduction

end


