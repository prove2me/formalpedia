-- Prove2me | Definitions.Def_GevreyGibbsSep_Supplement_WarmStartQAlg
-- name    : GevreyGibbsSep_Supplement_WarmStartQAlg
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T09:59:00.865303+00:00
-- url     : https://prove2.me/theorems/ec25f597-02dc-4214-9633-38f9de52b98b
-- title:
--   Warm-started first-order quantum algorithm with heralded success
-- statement:
--   A **warm-started first-order quantum algorithm** with $T$ oracle calls, on the $N$-grid and with workspace label set $W$, acts on the register $\ell^2(\mathbb R^d\times\mathbb R^d\times W)$ with computational basis $|x\rangle|b\rangle|w\rangle$ (a query point $x$, an answer register $b$ and a workspace label $w$). It consists of
--
--   1. an isometry $\mathrm{load}:\mathbb C^{(2N+1)^d}\to\ell^2(\mathbb R^d\times\mathbb R^d\times W)$ that places one copy of a warm-start state $|\phi\rangle$ on the $N$-grid into the register;
--   2. unitaries $U_0,\dots,U_T$;
--   3. for each of the $T$ oracle calls, a choice between the gradient oracle $O_{\nabla E}$ and its inverse;
--   4. a **herald** $\mathrm{flag}$ on basis labels: the run succeeds exactly when the final computational-basis measurement returns a label $z$ with $\mathrm{flag}(z)=\mathrm{true}$;
--   5. a classical post-processing kernel $\mathrm{post}$ that turns a measured label into a random point of the torus $\mathbb T^d$.
--
--   None of these components depends on the instance $E$ or on the warm-start state $\phi$: the instance enters only through the oracle, the warm start only through the loading map.
--
--   This is the algorithm model of Theorem A.3, which prepares a sample from a Gibbs state from a warm start with constant overlap.
--
--   **Formalization Note** It follows the published first-order algorithm model of the mission (exact-real registers, oracle $(x,b,w)\mapsto(x,b+\nabla E(x),w)$), with the fixed start vector replaced by the loading isometry and a success flag added.
-- source:
--   Olivucci, Sobchuk, Hoque, Hnybida, Kim, Shayeghi, Ronagh, Provable Quantum–Classical Separation for Continuous Gibbs Sampling, arXiv:2608.24527 (held version, sha256 d4fd40eb…), Theorem A.3, p.31; query model p.6

import Mathlib
import Definitions.Def_GevreyGibbsSep_Torus
import Definitions.Def_GevreyGibbsSep_QReg
import Definitions.Def_GevreyGibbsSep_QH
import Definitions.Def_GevreyGibbsSep_Grid

open MeasureTheory
open scoped ENNReal InnerProductSpace

namespace GevreyGibbsSep

namespace Supplement

/-- A warm-started first-order quantum algorithm with heralded success and `T` gradient-oracle
calls (Olivucci et al., *Provable Quantum–Classical Separation for Continuous Gibbs Sampling*,
arXiv:2608.24527 (held version, sha256 d4fd40eb…), Theorem A.3, p.31: "a quantum algorithm with
access to a warm-start state `|ϕ⟩` … that, on heralded success …, returns a sample"; query model
p.6). It consists of

* an isometry `load` that places one copy of the warm-start state `|ϕ⟩ ∈ ℂ^{(2N+1)^d}` (a state
  on the `N`-grid) into the register `ℓ²(ℝ^d × ℝ^d × W)`;
* unitaries `U_0, …, U_T`;
* for each of the `T` oracle calls a choice of `O_∇E` or its inverse;
* a herald `flag` on the computational-basis label measured at the end (success iff `true`);
* a classical post-processing kernel `post` turning the measured label into a point of `T^d`.

None of these depends on the instance `E` or on the warm-start state `ϕ`.

**Formalization Note** This follows the published `GevreyGibbsSep.FirstOrderQAlg` (reading R1 of
the mission: exact-real registers, oracle `(x, b, w) ↦ (x, b + ∇E(x), w)`), with the fixed start
vector replaced by the loading isometry and a success flag added. Intermediate measurements are
covered by deferred measurement. -/
structure WarmStartQAlg (d : ℕ) (W : Type) (N T : ℕ) where
  /-- The instance-independent isometry loading the warm-start state. -/
  load : EuclideanSpace ℂ (Grid d N) →ₗᵢ[ℂ] QH d W
  /-- The instance-independent unitaries `U_0, …, U_T`. -/
  U : Fin (T + 1) → (QH d W ≃ₗᵢ[ℂ] QH d W)
  /-- Whether the `i`-th oracle call is `O_∇E^†` (`true`) or `O_∇E` (`false`). -/
  useInv : Fin T → Bool
  /-- The herald: the run succeeds iff the measured basis label `z` has `flag z = true`. -/
  flag : QReg d W → Bool
  /-- Classical post-processing of the measured basis label into a point of `T^d`. -/
  post : QReg d W → ProbabilityMeasure (Torus d)

end Supplement

end GevreyGibbsSep


