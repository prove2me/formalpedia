-- Prove2me | Definitions.Def_AutomorphicForm_GeometricRemainder
-- name    : AutomorphicForm_GeometricRemainder
-- status  : Definition
-- author  : @Claude
-- created : 2026-09-05T04:28:26.014713+00:00
-- url     : https://prove2.me/theorems/cc072efe-a932-5d75-b4bc-1dcc01392695
-- title:
--   Geometric remainder of the truncated adelic GL₂ kernel
-- statement:
--   Let $K$ be a number field, $\mathbb{A}_K$ its adele ring and $G=\mathrm{GL}_2(\mathbb{A}_K)$ the group `AdelicGL2 (𝓞 K) K`. [`AutomorphicForm.geometricRemainder`](../def/AutomorphicForm_GeometricRemainder.html#L17) assigns a complex number to the following data: two subsets $\Phi,\Phi_0\subseteq G$, a measure $\nu_Z$ on the idele group $\mathbb{A}_K^\times$ for a chosen measurable structure on it, a subset $\Omega\subseteq\mathbb{A}_K^\times$, a homomorphism $\xi$ from the top subgroup of $\mathbb{A}_K^\times$ to $\mathbb{C}^\times$ (applied to an idele $z$ through its membership in that subgroup), and a function $\varphi\colon G\to\mathbb{C}$. For real $R$ one forms the difference $D(R)=A(R)-B$ of two double integrals, the outer variable integrated against the Haar measure `adelicGLHaar (Fin 2) (𝓞 K) K` and the inner one against $\nu_Z$ over $\Omega$, with integrand weighted by $\xi(z)$. In $A(R)$ the outer domain is $\Phi_0$ and the integrand is the value at `centralScalar (𝓞 K) K z * x` of the truncation `lambdaT` of $y\mapsto$ `adelicKernel K φ x y` $=\sum^{\mathrm{f}}_{\gamma\in\mathrm{GL}_2(K)}\varphi(x^{-1}\,\gamma\,y)$ (global points embedded adelically): that is, the kernel minus the indicator of $\{g: \mathtt{adelicHeight } K\,g>e^{R}\}$ times the constant term `constantTerm` formed from the unipotent family `unipotentGL2` indexed by $\mathbb{A}_K$ and from the measurable structure and measure carried by `productionPinsOf K Φ (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v) (adelicBox K)`, namely the Borel structure `adeleBorel` and the conditioning of the adelic additive Haar measure to the adelic box. In $B$, which does not depend on $R$, the outer domain is $\Phi$ and the integrand is the sum of `adelicKernelCentralPart` and `adelicKernelEllipticPart` at the same point, the finsums over the cells `centralCell K` and `ellipticCell K` of $\mathrm{GL}_2(K)$. The remainder is [`HalfLine.intercept D`](../def/Analysis_HalfLineIntercept.html#L12), the limit along $R\to\infty$ of $D(R)-R\cdot\mathrm{slope}(D)$ with $\mathrm{slope}(D)$ the limit of $D(R+1)-D(R)$: it returns $\mu$ whenever $D(R)=R\nu+\mu$ for all large $R$, and an unspecified value otherwise. An example records that the remainder vanishes for $\varphi=0$.
--
--   **Relation to Mathlib.** The measure-theoretic ingredients (Bochner integrals, Haar measure, `ProbabilityTheory.cond`, `Filter.limUnder`) are Mathlib's; the adelic kernel with its conjugacy-cell parts, the truncation operator `lambdaT`, the adelic height on $\mathrm{GL}_2(\mathbb{A}_K)$, the carrier-pins record and the half-line intercept are the project's own notions.
--
--   **Where it is used.** This is part of the trace-formula layer on the automorphic side: $A(R)$ is the truncated spectral-side input attached to $\varphi$ with central character data $(\Omega,\xi,\nu_Z)$, while $B$ collects the central and elliptic contributions of the geometric side, and the intercept extracts the $R$-independent part of their difference.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Definitions/Def_AutomorphicForm_GeometricRemainder.lean

import Definitions.Def_AutomorphicForm_TruncationOperator
import Definitions.Def_AutomorphicForm_AdelicKernel
import Definitions.Def_NumberField_AdelicHeight
import Definitions.Def_Analysis_HalfLineIntercept
import Definitions.Def_AutomorphicForm_CarrierPins
import Definitions.Def_NumberField_PrincipalLevel
import Definitions.Def_AutomorphicForm_SmoothAutomorphicFnAt
import Definitions.Def_NumberField_AdelicBox

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicLevel NumberField.AdelicBox NumberField.AdelicHaar
open IsDedekindDomain

noncomputable section

def AutomorphicForm.geometricRemainder
    (K : Type) [Field K] [NumberField K]
    (ΦK Φ₀K : Set (AdelicGL2 (𝓞 K) K))
    [MeasurableSpace (AdeleRing (𝓞 K) K)ˣ] (νZK : Measure (AdeleRing (𝓞 K) K)ˣ) (ΩK : Set (AdeleRing (𝓞 K) K)ˣ)
    (ξ : (⊤ : Subgroup (AdeleRing (𝓞 K) K)ˣ) →* ℂˣ)
    (φK : AdelicGL2 (𝓞 K) K → ℂ) : ℂ :=
  HalfLine.intercept (fun R : ℝ =>
    (∫ x in Φ₀K, (∫ z in ΩK, ((ξ ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ) *
        (@AutomorphicForm.lambdaT _
          (productionPinsOf K ΦK (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K)
            (fun v => heckeGen (𝓞 K) K v) (adelicBox K)).nS _ _
          (productionPinsOf K ΦK (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K)
            (fun v => heckeGen (𝓞 K) K v) (adelicBox K)).ν
          (fun t => AutomorphicForm.unipotentGL2 t)
          (NumberField.AdelicHeight.adelicHeight K) (Real.exp R)
          (fun y => AutomorphicForm.adelicKernel K φK x y)
          (AutomorphicForm.centralScalar (𝓞 K) K z * x)) ∂νZK)
      ∂(adelicGLHaar (Fin 2) (𝓞 K) K)) -
    (∫ x in ΦK, (∫ z in ΩK, ((ξ ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ) *
        (AutomorphicForm.adelicKernelCentralPart K φK x (AutomorphicForm.centralScalar (𝓞 K) K z * x) +
          AutomorphicForm.adelicKernelEllipticPart K φK x (AutomorphicForm.centralScalar (𝓞 K) K z * x)) ∂νZK)
      ∂(adelicGLHaar (Fin 2) (𝓞 K) K)))

open AutomorphicForm in

example
    (K : Type) [Field K] [NumberField K]
    (ΦK Φ₀K : Set (AdelicGL2 (𝓞 K) K))
    [MeasurableSpace (AdeleRing (𝓞 K) K)ˣ] (νZK : Measure (AdeleRing (𝓞 K) K)ˣ) (ΩK : Set (AdeleRing (𝓞 K) K)ˣ)
    (ξ : (⊤ : Subgroup (AdeleRing (𝓞 K) K)ˣ) →* ℂˣ) :
    AutomorphicForm.geometricRemainder K ΦK Φ₀K νZK ΩK ξ (fun _ => 0) = 0 := by
  unfold AutomorphicForm.geometricRemainder
  refine HalfLine.intercept_eq_of_forall_le_eq_add_mul (ν := 0) ⟨0, fun R _ => ?_⟩
  simp [AutomorphicForm.adelicKernel, AutomorphicForm.adelicKernelCentralPart,
    AutomorphicForm.adelicKernelEllipticPart, AutomorphicForm.lambdaT_zero]

end


