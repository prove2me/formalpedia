-- Prove2me | Definitions.Def_OAI_Analysis_DirectCrouzeix_NormalFamilies
-- name    : OAI_Analysis_DirectCrouzeix_NormalFamilies
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-18T04:52:45.295843+00:00
-- url     : https://prove2.me/theorems/11a78b2d-ef1f-42a1-b34d-7ec38cd0d040
-- title:
--   Extension by zero of a function defined on a subset of the complex plane
-- statement:
--   Let $U\subseteq\mathbb{C}$ be any set and let $f:U\to\mathbb{C}$ be a function defined only on $U$. The module defines its extension by zero $\widetilde f:\mathbb{C}\to\mathbb{C}$,
--
--   $$
--   \widetilde f(z)=\begin{cases}f(z),&z\in U,\\ 0,&z\notin U,\end{cases}
--   $$
--
--   and records as a simplification lemma that $\widetilde f(z)=f(z)$ for every $z\in U$.
--
--   Normal-family arguments are naturally carried out in the space $C(U,\mathbb{C})$ of continuous functions on $U$, whose compact-open topology is the topology of locally uniform convergence, while holomorphy, derivatives and injectivity are expressed for functions on all of $\mathbb{C}$. The extension by zero transfers between the two settings: for open $U$, convergence of $F_n$ to $G$ in $C(U,\mathbb{C})$ implies locally uniform convergence of $\widetilde{F_n}$ to $\widetilde G$ on $U$. This is used in the Montel-type compactness step of the proof of the Riemann mapping theorem in this development.
--
--   **Formalization Note** `extend U f z` is defined by `if h : z ∈ U then f ⟨z, h⟩ else 0` using classical decidability of membership, for `f : U → ℂ` on the subtype `U`; the simplification lemma is `extend_coe`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/DirectCrouzeix/NormalFamilies.lean

-- Generated from openai/math@1581d4c lean/OAI/Analysis/DirectCrouzeix/NormalFamilies.lean by skeleton subtraction
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

namespace OAI

universe u_131

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

def extend (U : Set ℂ) (f : U → ℂ) (z : ℂ) : ℂ := by
  classical
  exact if h : z ∈ U then f ⟨z, h⟩ else 0

@[simp] theorem extend_coe {U : Set ℂ} (f : U → ℂ) (z : U) : extend U f z = f z := by
  simp [extend, z.property]

open Function Complex

open scoped Pointwise

end Conformal

end DirectCrouzeix

end

end

end

end OAI


