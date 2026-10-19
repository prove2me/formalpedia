-- Prove2me | Definitions.Def_OAI_Analysis_DirectCrouzeix_CompactIntegrals
-- name    : OAI_Analysis_DirectCrouzeix_CompactIntegrals
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-18T04:35:59.6689+00:00
-- url     : https://prove2.me/theorems/3ca5691c-e035-47dc-a98d-44c434622ef3
-- title:
--   Weighted integrals of a function along the segment from $u$ to $v$ in the complex plane
-- statement:
--   The module introduces the following objects.
--
--   1. **Parameter interval.** The closed interval $[0,1]$, regarded as a measure space with Lebesgue measure.
--
--   2. **Chord.** For $u,v\in\mathbb{C}$ and $t\in\mathbb{R}$,
--   $$
--   \gamma_{u,v}(t)=(1-t)\,u+t\,v ;
--   $$
--   as $t$ runs through $[0,1]$ this traverses the segment from $u$ to $v$.
--
--   3. **Chord integral.** For a function $f:\mathbb{C}\to\mathbb{C}$, a weight $w:[0,1]\to\mathbb{C}$ and points $u,v\in\mathbb{C}$,
--   $$
--   I_w[f](u,v)=\int_0^1 w(t)\,f\big((1-t)\,u+t\,v\big)\,dt .
--   $$
--
--   These integrals give representations of divided differences that remain meaningful on the diagonal $u=v$. If $g$ is holomorphic on an open convex set $s$ containing $u$ and $v$, the fundamental theorem of calculus gives $(v-u)\,I_1[g'](u,v)=g(v)-g(u)$, where $I_1$ is the chord integral with weight $w\equiv1$, so $I_1[g'](u,v)$ is the divided difference of $g$ for $u\ne v$ and equals $g'(u)$ for $u=v$. For $f$ holomorphic on such an $s$ and a continuous weight $w$, differentiating under the integral sign in $u$ (respectively $v$) produces the chord integral of $f'$ with weight $w(t)(1-t)$ (respectively $w(t)\,t$); these facts are proved in the module.
--
--   **Formalization Note** `Parameter` is the subtype `Set.Icc (0 : ℝ) 1` with the restriction of Lebesgue measure, `chord u v t` is `(1-t) • u + t • v`, and `chordIntegral f w u v` is the Bochner integral `∫ t : Parameter, w t * f (chord u v t)`, which is $0$ by convention when the integrand is not integrable; this does not occur for continuous $f$ and $w$.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/DirectCrouzeix/CompactIntegrals.lean

-- Generated from openai/math@1581d4c lean/OAI/Analysis/DirectCrouzeix/CompactIntegrals.lean by skeleton subtraction
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

namespace OAI

universe u_87 u_88 u_89 u_90 u_91 u_92 u_93

noncomputable section

open scoped Matrix Matrix.Norms.L2Operator Kronecker

noncomputable section

open MeasureTheory Set Filter Metric

open scoped Topology Interval ENNReal NNReal ComplexConjugate

namespace DirectCrouzeix.Faber

abbrev Parameter := Set.Icc (0 : ℝ) 1

def chord (u v : ℂ) (t : ℝ) : ℂ := (1-t) • u + t • v

def chordIntegral (f : ℂ → ℂ) (w : Parameter → ℂ) (u v : ℂ) : ℂ :=
  ∫ t : Parameter, w t * f (chord u v t)

end DirectCrouzeix.Faber

end

end

end OAI


