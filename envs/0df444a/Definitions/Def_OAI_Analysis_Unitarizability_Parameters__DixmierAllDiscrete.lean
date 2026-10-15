-- Prove2me | Definitions.Def_OAI_Analysis_Unitarizability_Parameters__DixmierAllDiscrete
-- name    : OAI_Analysis_Unitarizability_Parameters__DixmierAllDiscrete
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-15T07:26:01.013117+00:00
-- url     : https://prove2.me/theorems/cc9bbff4-336e-45a8-b8e7-31f2f603f29a
-- title:
--   Endpoint capacity $\lceil d^\ell\rho^\ell\rceil$ and fibre dimension $\lceil 2r_\ell\log(2d^\ell)\rceil$
-- statement:
--   Let $d\in\mathbb{N}$, $\rho\in\mathbb{R}$ and $\ell\in\mathbb{N}$. Write $\lceil t\rceil_+$ for the natural-number ceiling of a real number $t$ (the least natural number $\ge t$, so $\lceil t\rceil_+=0$ for $t\le0$) and $\log$ for the natural logarithm.
--
--   1. **Endpoint capacity.**
--   $$r_\ell=r(d,\rho,\ell)=\bigl\lceil d^{\ell}\rho^{\ell}\bigr\rceil_+ .$$
--   2. **Fibre dimension.**
--   $$k_\ell=k(d,\rho,\ell)=\bigl\lceil 2\,r_\ell\,\log(2d^{\ell})\bigr\rceil_+ .$$
--
--   In the construction for a non-amenable group, $d=|S|\ge2$ is the size of a finite set $S\ni1$ whose right regular sum satisfies $\|\sum_{t\in S}R_t\|\le d\rho$ with $0<\rho<1$. The labels at stage $\ell$ are the $d^\ell$ words of length $\ell$; $r_\ell$ is the capacity of a sparse mask for these words, and $k_\ell$ coincides with the frame dimension $\lceil2r\log(2n)\rceil_+$ for $n=d^\ell$ vectors and capacity $r=r_\ell$, i.e. it is the dimension of the fibre $\mathbb{C}^{k_\ell}$ carrying the frame vectors indexed by the words. The module proves that $k_\ell/d^\ell\to0$ as $\ell\to\infty$ whenever $d\ge2$ and $0\le\rho<1$, so a kernel energy of at least $d^\ell$ at stage $\ell$ is unbounded relative to the fibre dimension.
--
--   **Formalization Note** `endpointCapacity d ρ ℓ` and `fiberDimension d ρ ℓ` use `Nat.ceil` and `Real.log`. Lean's convention $\log0=0$ only matters in the degenerate case $d=0$, $\ell\ge1$; for $\rho<0$ and odd $\ell$ the capacity is $0$.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/Unitarizability/Parameters.lean

-- Generated from openai/math@1581d4c lean/OAI/Analysis/Unitarizability/Parameters.lean by skeleton subtraction
-- (upload_full_project.md Phase 3): Definitions bundle for the DixmierAllDiscrete mission closure.
-- Kept: reachable definitions/instances and the theorems their bodies or the node statements cite.
-- Project imports rewritten to platform modules; otherwise byte-identical to the source.
import Mathlib
import Definitions.Def_DixmierAllDiscrete
import Definitions.Def_OAI_Analysis_Unitarizability_KernelEnergy__DixmierAllDiscrete
import Definitions.Def_OAI_Analysis_Unitarizability_KernelObstruction__DixmierAllDiscrete
import Definitions.Def_OAI_Analysis_Unitarizability_Cocycle__DixmierAllDiscrete
import Definitions.Def_OAI_Analysis_Unitarizability_HilbertSum__DixmierAllDiscrete
import Definitions.Def_OAI_Analysis_Unitarizability_Triangular__DixmierAllDiscrete
import Definitions.Def_OAI_Analysis_Unitarizability_InvariantProjection__DixmierAllDiscrete
import Definitions.Def_OAI_Analysis_Unitarizability_SumObstruction__DixmierAllDiscrete
import Definitions.Def_OAI_Analysis_Unitarizability_SparseMask__DixmierAllDiscrete
import Definitions.Def_OAI_Analysis_Unitarizability_EndpointAssignment__DixmierAllDiscrete
import Definitions.Def_OAI_Analysis_Unitarizability_SparseSplitting__DixmierAllDiscrete
import Definitions.Def_OAI_Analysis_Unitarizability_Regular__DixmierAllDiscrete
import Definitions.Def_OAI_Analysis_Unitarizability_VectorMean__DixmierAllDiscrete
import Definitions.Def_OAI_Analysis_Unitarizability_FiniteSigns__DixmierAllDiscrete
import Definitions.Def_OAI_Analysis_Unitarizability_FiniteSynthesis__DixmierAllDiscrete
import Definitions.Def_OAI_Analysis_Unitarizability_SignMatrix__DixmierAllDiscrete

namespace OAI

/-! Ceiling parameters and dimension-ratio asymptotics. -/
noncomputable section
namespace Dixmier
open Filter Topology

def endpointCapacity (d : ℕ) (ρ : ℝ) (ℓ : ℕ) : ℕ := ⌈(d : ℝ)^ℓ * ρ^ℓ⌉₊
def fiberDimension (d : ℕ) (ρ : ℝ) (ℓ : ℕ) : ℕ :=
  ⌈2 * (endpointCapacity d ρ ℓ : ℝ) * Real.log (2 * (d : ℝ)^ℓ)⌉₊

end Dixmier

end

end OAI


