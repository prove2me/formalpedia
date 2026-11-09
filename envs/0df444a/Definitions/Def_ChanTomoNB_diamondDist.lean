-- Prove2me | Definitions.Def_ChanTomoNB_diamondDist
-- name    : ChanTomoNB_diamondDist
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T11:28:12.501256+00:00
-- url     : https://prove2.me/theorems/8f56d3e9-c3fc-4b2f-b05e-f672a5113a84
-- title:
--   Diamond norm distance $\|\mathcal E-\mathcal F\|_\diamond$ with reference $\mathcal H_R\cong\mathbb C^{d_1}$
-- statement:
--   For superoperators $\mathcal E,\mathcal F:L(\mathcal H_A)\to L(\mathbb C^{d_2})$, $\mathcal H_A\cong\mathbb C^{d_1}$, the **diamond norm distance** is
--   $$
--   \|\mathcal E-\mathcal F\|_\diamond=\max_{\substack{\rho_{AR}\succeq0\\ \operatorname{tr}\rho_{AR}=1}}\big\|\big((\mathcal E-\mathcal F)\otimes\mathcal I_R\big)(\rho_{AR})\big\|_1,\qquad \mathcal H_R\cong\mathbb C^{d_1},
--   $$
--   where $\mathcal I_R$ is the identity channel on the reference system.
--
--   It is the second error metric of the tomography problem, and dominates the Choi trace norm distance.
--
--   **Formalization Note** The reference system is fixed to $\mathcal H_R\cong\mathcal H_A$, as printed. The maximum is written as the real supremum of the set of values, which is nonempty and bounded. Defined for all linear maps.
-- source:
--   Chen, Oufkir, Quantum channel tomography: optimal bounds in the near-boundary regime, arXiv:2611.03639v1, §2.1, p.10

import Mathlib
import Definitions.Def_WildeQIT_traceNorm
import Definitions.Def_ChanTomoNB_QChan

open Matrix
open scoped ComplexOrder

namespace ChanTomoNB

/-- `(Φ ⊗ I_R)(ρ)` for `ρ ∈ L(H_A ⊗ H_R)` with the reference `H_R ≅ H_A`: the map `Φ` is applied
to every block `ρ_{x x'} = (⟨a, x| ρ |a', x'⟩)_{a,a'}`. Chen, Oufkir, arXiv:2611.03639v1, §2.1,
p.10. The result is indexed by `B × R`, output first. -/
def ampR {A B : Type} (Φ : Superop A B) (ρ : Matrix (A × A) (A × A) ℂ) :
    Matrix (B × A) (B × A) ℂ :=
  Matrix.of fun p q => Φ (Matrix.of fun a a' => ρ (a, p.2) (a', q.2)) p.1 q.1

/-- The diamond norm distance
`‖E − F‖_⋄ = max_{ρ_{AR} ⪰ 0, tr ρ_{AR} = 1} ‖((E − F) ⊗ I_R)(ρ_{AR})‖₁`, `H_R ≅ ℂ^{d1}`.
Chen, Oufkir, *Quantum channel tomography: optimal bounds in the near-boundary regime*,
arXiv:2611.03639v1, §2.1, p.10.

**Formalization Note.** The reference system is fixed to `H_R ≅ H_A`, as printed. The maximum is
written as the real `sSup` of the set of values; the set is nonempty (for a nonempty input space)
and bounded, so this is the paper's maximum. Defined for all linear maps `E, F`, so it applies to
estimates that are not channels. `‖·‖₁` is the published `WildeQIT.traceNorm`. -/
noncomputable def diamondDist {A B : Type} [Fintype A] [Fintype B] [DecidableEq A]
    [DecidableEq B] (E F : Superop A B) : ℝ :=
  sSup {t : ℝ | ∃ ρ : Matrix (A × A) (A × A) ℂ, ρ.PosSemidef ∧ ρ.trace = 1 ∧
    t = WildeQIT.traceNorm (ampR (E - F) ρ)}

end ChanTomoNB


