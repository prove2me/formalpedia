-- Prove2me | Definitions.Def_OAI_Analysis_DirectCrouzeix_DiskMapping
-- name    : OAI_Analysis_DirectCrouzeix_DiskMapping
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-18T04:56:07.713452+00:00
-- url     : https://prove2.me/theorems/041bd08c-39f7-4831-a2e0-9bcf3b5bb0a8
-- title:
--   The disk automorphism $z\mapsto(z-a)/(1-\bar a z)$
-- statement:
--   For complex numbers $a$ and $z$ the module defines
--
--   $$
--   \varphi_a(z)=\frac{z-a}{1-\overline{a}\,z},
--   $$
--
--   and records the two values $\varphi_a(a)=0$ and $\varphi_a(0)=-a$ as simplification lemmas; these hold for every $a\in\mathbb{C}$.
--
--   For $|a|<1$ the denominator does not vanish on the closed unit disk, $\varphi_a$ maps the open unit disk $\mathbb{D}$ injectively into itself, and $\varphi_a'(z)=(1-|a|^{2})/(1-\overline{a}z)^{2}$, so $|\varphi_a'(0)|=1-|a|^{2}$ and $|\varphi_a'(a)|=1/(1-|a|^{2})$; these properties are proved in the module. They drive the improvement step of the Riemann mapping argument: if a normalized embedding $f$ of a simply connected open set $U$ into $\mathbb{D}$ with $f(a_0)=0$ omits a point $b\in\mathbb{D}$, then composing with $\varphi_b$, taking a holomorphic square root $h$ and composing with $\varphi_{h(a_0)}$ yields a normalized embedding with strictly larger $|f'(a_0)|$.
--
--   **Formalization Note** `diskMobius a z` is `(z - a) / (1 - conj a * z)`; Lean's convention gives the value $0$ when the denominator vanishes, which cannot happen for $|a|<1$ and $|z|\le1$. The simplification lemmas are `diskMobius_self` and `diskMobius_zero`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/DirectCrouzeix/DiskMapping.lean

-- Generated from openai/math@1581d4c lean/OAI/Analysis/DirectCrouzeix/DiskMapping.lean by skeleton subtraction
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
import Definitions.Def_OAI_Analysis_DirectCrouzeix_TaylorFourier
import Definitions.Def_OAI_Analysis_DirectCrouzeix_FaberPolynomials
import Definitions.Def_OAI_Analysis_DirectCrouzeix_BoundaryKernel
import Definitions.Def_OAI_Analysis_DirectCrouzeix_KernelContraction
import Definitions.Def_OAI_Analysis_DirectCrouzeix_FaberEnergy
import Definitions.Def_OAI_Analysis_DirectCrouzeix_FaberCalculus
import Definitions.Def_OAI_Analysis_DirectCrouzeix_NormalFamilies
import Definitions.Def_OAI_Analysis_DirectCrouzeix_ExtremalEmbedding

namespace OAI

noncomputable section

open scoped Matrix Matrix.Norms.L2Operator Kronecker

noncomputable section

open MeasureTheory Set Filter Metric

open scoped Topology Interval ENNReal NNReal ComplexConjugate

noncomputable section

open Filter Metric Set

open scoped Topology ComplexConjugate

namespace DirectCrouzeix

namespace Conformal

open Function Complex

open scoped Pointwise

def diskMobius (a z : ℂ) : ℂ := (z - a) / (1 - conj a * z)

@[simp] theorem diskMobius_self (a : ℂ) : diskMobius a a = 0 := by simp [diskMobius]

@[simp] theorem diskMobius_zero (a : ℂ) : diskMobius a 0 = -a := by simp [diskMobius]

open InnerProductSpace Real

end Conformal

end DirectCrouzeix

end

end

end

end OAI


