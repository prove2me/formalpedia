-- Prove2me | Definitions.Def_OAI_Analysis_DirectCrouzeix_TaylorFourier
-- name    : OAI_Analysis_DirectCrouzeix_TaylorFourier
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-18T04:39:16.30269+00:00
-- url     : https://prove2.me/theorems/2dd7ca3f-4062-46a9-80f0-656424ef4385
-- title:
--   Taylor coefficients at the origin and the unit-circle parametrization $t\mapsto e^{2\pi it}$
-- statement:
--   The module introduces the following objects.
--
--   1. **Taylor coefficients at $0$.** For a complex normed space $E$, a function $f:\mathbb{C}\to E$ and $k\in\mathbb{N}$,
--   $$
--   \tau_k(f)=\frac{1}{k!}\,f^{(k)}(0),
--   $$
--   where $f^{(k)}$ is the $k$-th iterated complex derivative. Two evaluation rules are recorded as simplification lemmas: $\tau_0(f)=f(0)$, and for a constant function $f\equiv v$, $\tau_k(f)=v$ if $k=0$ and $\tau_k(f)=0$ if $k\ge1$.
--
--   2. **Angle circle.** The circle $\mathbb{T}=\mathbb{R}/\mathbb{Z}$ with its normalized Haar measure $dt$ of total mass $1$.
--
--   3. **Unit point.** The parametrization of the unit circle
--   $$
--   \zeta(t)=e^{2\pi it},\qquad t\in\mathbb{T},
--   $$
--   together with the rule $|\zeta(t)|=1$.
--
--   For $f$ holomorphic on a disk $\{|u|<R\}$ with $R>1$ and values in a complex Banach space, the Fourier coefficients of $t\mapsto f(e^{2\pi it})$ are $\tau_k(f)$ at frequencies $k\ge0$ and vanish at negative frequencies (proved in the module). This is the bridge between power series and Fourier series used to identify Faber polynomials, which are defined as Taylor coefficients of generating functions, with Fourier coefficients of boundary integrals.
--
--   **Formalization Note** `taylorCoeff f k` is `(k.factorial : ℂ)⁻¹ • iteratedDeriv k f 0`; since `deriv` is $0$ at points of non-differentiability, $\tau_k(f)$ is defined for every $f$ but has its usual meaning only for $f$ holomorphic near $0$. `Angle` is `AddCircle (1 : ℝ)`, `angularMeasure` is `AddCircle.haarAddCircle`, and `unitPoint t` is `fourier 1 t`. The simplification lemmas are `taylorCoeff_zero`, `taylorCoeff_const` and `unitPoint_norm`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/DirectCrouzeix/TaylorFourier.lean

-- Generated from openai/math@1581d4c lean/OAI/Analysis/DirectCrouzeix/TaylorFourier.lean by skeleton subtraction
-- (upload_full_project.md Phase 3): Definitions bundle for the DirectCrouzeix mission closure.
-- Kept: reachable definitions/instances and the theorems their bodies or the node statements cite.
-- Project imports rewritten to platform modules; otherwise byte-identical to the source.
import Mathlib
import Definitions.Def_DirectCrouzeix
import Definitions.Def_OAI_Analysis_DirectCrouzeix_PositiveBlocks
import Definitions.Def_OAI_Analysis_DirectCrouzeix_Resolvent
import Definitions.Def_OAI_Analysis_DirectCrouzeix_PolynomialCalculus
import Definitions.Def_OAI_Analysis_DirectCrouzeix_HilbertSchmidt
import Definitions.Def_OAI_Analysis_DirectCrouzeix_SingularPairs
import Definitions.Def_OAI_Analysis_DirectCrouzeix_Sharpness
import Definitions.Def_OAI_Analysis_DirectCrouzeix_CircleFourier
import Definitions.Def_OAI_Analysis_DirectCrouzeix_BoundaryEnergy
import Definitions.Def_OAI_Analysis_DirectCrouzeix_PolynomialEnergy
import Definitions.Def_OAI_Analysis_DirectCrouzeix_CompactIntegrals
import Definitions.Def_OAI_Analysis_DirectCrouzeix_DividedDifferences

-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

universe u_94 u_95 u_96 u_97 u_98 u_99 u_100 u_101 u_102 u_103 u_104 u_105

noncomputable section

open scoped Matrix Matrix.Norms.L2Operator Kronecker

noncomputable section

open MeasureTheory Set Filter Metric

open scoped Topology Interval ENNReal NNReal ComplexConjugate

namespace DirectCrouzeix.Faber

def taylorCoeff {E : Type u_94} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (f : ℂ → E) (k : ℕ) : E := (k.factorial : ℂ)⁻¹ • iteratedDeriv k f 0

@[simp] theorem taylorCoeff_zero {E : Type u_95} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (f : ℂ → E) : taylorCoeff f 0 = f 0 := by simp [taylorCoeff]

@[simp] theorem taylorCoeff_const {E : Type u_101} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (v : E) (k : ℕ) : taylorCoeff (fun _ => v) k = if k = 0 then v else 0 := by
  by_cases hk : k = 0
  · subst k; simp
  · simp [taylorCoeff,iteratedDeriv_const,hk]

abbrev Angle := AddCircle (1:ℝ)

abbrev angularMeasure : Measure Angle := AddCircle.haarAddCircle

def unitPoint (t : Angle) : ℂ := fourier 1 t

@[simp] theorem unitPoint_norm (t : Angle) : ‖unitPoint t‖ = 1 := by
  simp [unitPoint,fourier_apply,Circle.norm_coe]

end DirectCrouzeix.Faber

end

end

end OAI


