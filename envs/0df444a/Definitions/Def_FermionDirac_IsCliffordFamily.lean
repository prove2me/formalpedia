-- Prove2me | Definitions.Def_FermionDirac_IsCliffordFamily
-- name    : FermionDirac_IsCliffordFamily
-- status  : Definition
-- author  : @LG
-- created : 2026-11-25T01:11:44.869718+00:00
-- url     : https://prove2.me/theorems/c8aad7b7-c739-4e1c-bb6e-0628e12c3959
-- title:
--   Clifford families $\gamma^\mu\gamma^\nu+\gamma^\nu\gamma^\mu=2\eta^{\mu\nu}I_n$, and the associated involutions
-- statement:
--   A **Clifford family** of size $n$ is a choice of four $n\times n$ complex matrices $\gamma^\mu$, one for each Lorentz index $\mu\in\mathrm{Fin}\,1\oplus\mathrm{Fin}\,3$ (one time direction and three spatial directions), satisfying the Clifford relation of the Dirac algebra against the Minkowski metric $\eta=\mathrm{diag}(1,-1,-1,-1)$:
--   $$\gamma^\mu\gamma^\nu+\gamma^\nu\gamma^\mu=2\,\eta^{\mu\nu}\,I_n\qquad\text{for all }\mu,\nu.$$
--   Each member squares to $\pm I_n$ and is therefore invertible, and distinct members anticommute. Dirac's $4\times4$ matrices are a Clifford family; the mission's goal is that no smaller nonzero size exists.
--
--   The bundle also defines, for any family $\gamma$, the associated **involutions** $\mathrm{inv}^\mu=c_\mu\gamma^\mu$ with $c_\mu=1$ for the time index and $c_\mu=i$ for the three spatial indices — that is, $\gamma^0,\,i\gamma^1,\,i\gamma^2,\,i\gamma^3$. When $\gamma$ is a Clifford family these four matrices square to $I_n$ and pairwise anticommute; at size $n=2$ they would be four anticommuting $2\times2$ involutions, which the mission's $2\times2$ bound forbids.
--
--   **Formalization Note.** The metric is the real `minkowskiMatrix`, coerced entrywise to $\mathbb{C}$. The size $n$ is implicit. The predicate itself allows $n=0$ (the empty matrices satisfy the relation vacuously); the exclusion of size zero lives in the goal theorem's set, not here. `involutions` is defined for an arbitrary family, with no Clifford hypothesis.
-- source:
--   Physlib, `PhyslibAlpha/Relativity/Fermions/Dirac/MinimalDimension.lean`, `Fermion.Dirac.IsCliffordFamily` (L59–L61) and `Fermion.Dirac.IsCliffordFamily.involutions` (L113–L116). https://github.com/leanprover-community/physlib/blob/85bb8f5df598f6701be57a70f06e08069e30589c/PhyslibAlpha/Relativity/Fermions/Dirac/MinimalDimension.lean#L59-L61 ; https://github.com/leanprover-community/physlib/blob/85bb8f5df598f6701be57a70f06e08069e30589c/PhyslibAlpha/Relativity/Fermions/Dirac/MinimalDimension.lean#L113-L116

import Mathlib
import Definitions.Def_minkowskiMatrix

namespace Fermion.Dirac

open Matrix Complex

/-- A family of `n × n` matrices with `γ^μ γ^ν + γ^ν γ^μ = 2 η^{μν} 1`. -/
def IsCliffordFamily {n : ℕ} (γ : Fin 1 ⊕ Fin 3 → Matrix (Fin n) (Fin n) ℂ) : Prop :=
  ∀ μ ν, γ μ * γ ν + γ ν * γ μ = (2 * (minkowskiMatrix μ ν : ℂ)) • 1

namespace IsCliffordFamily

/-- `γ^0, i γ^1, i γ^2, i γ^3`: four involutions that anticommute. -/
noncomputable def involutions {n : ℕ} (γ : Fin 1 ⊕ Fin 3 → Matrix (Fin n) (Fin n) ℂ)
    (μ : Fin 1 ⊕ Fin 3) : Matrix (Fin n) (Fin n) ℂ :=
  (Sum.elim (fun _ => (1 : ℂ)) (fun _ => I) μ) • γ μ

end IsCliffordFamily

end Fermion.Dirac


