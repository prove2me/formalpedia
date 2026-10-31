-- Prove2me | Definitions.Def_DiffCtrlRobust_ModelsConverge
-- name    : DiffCtrlRobust_ModelsConverge
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T02:47:25.428745+00:00
-- url     : https://prove2.me/theorems/f935d38d-b436-4ede-a016-0e65bbf5f784
-- title:
--   Convergence of the models: (A5)(i) and (A5)(ii)
-- statement:
--   The approximating models $(b_n,\sigma_n,c_n)$ converge to $(b,\sigma,c)$ if:
--
--   1. (A5)(i) $\sigma_n(x)\to\sigma(x)$ for a.e. $x\in\mathbb R^d$;
--   2. (A5)(ii) (continuous convergence in controls) for a.e. $x\in\mathbb R^d$: whenever $\zeta_n\to\zeta$ in $\mathbb U$, we have $c_n(x,\zeta_n)\to c(x,\zeta)$ and $b_n(x,\zeta_n)\to b(x,\zeta)$.
--
--   **Formalization Note** In (ii) the null set does not depend on the sequence: this is "$c_n(x,\cdot)\to c(x,\cdot)$, $b_n(x,\cdot)\to b(x,\cdot)$ continuously on compact set $\mathbb U$" (p.12), the form the proof uses. Allowing the null set to depend on the sequence makes Theorems 3.3 and 3.4 false; see the note of `theorem_3_3`.
-- source:
--   Pradhan & Yüksel, arXiv:2205.05894v2, §2.2, p.7, (2.13), (2.14); p.12, before (3.10)

import Definitions.Def_EthierKurtz_SDEState
import Definitions.Def_EthierKurtz_SDEDiffusion

open MeasureTheory ProbabilityTheory Filter EthierKurtz
open scoped ENNReal NNReal Topology BigOperators

namespace DiffCtrlRobust

/-- Parts (i) and (ii) of (A5) (arXiv:2205.05894v2, §2.2, p.7): `σₙ(x) → σ(x)` for a.e. `x`, (2.13),
and continuous convergence in controls, (2.14): for a.e. `x`, whenever `ζₙ → ζ`,
`cₙ(x, ζₙ) → c(x, ζ)` and `bₙ(x, ζₙ) → b(x, ζ)`.

**Formalization Note.** The exceptional null set in (ii) does not depend on the sequence. This is
the sense in which the proof uses (2.14): "`cₙ(x, ·) → c(x, ·)`, `bₙ(x, ·) → b(x, ·)` continuously
on compact set `U`" (p.12). If the null set could depend on the sequence, Theorems 3.3 and 3.4 would
be false; the counterexample is in the statements of those theorems. -/
structure ModelsConverge {d : ℕ} {U : Type*} [TopologicalSpace U]
    (b : SDEState d → U → SDEState d) (σ : SDEState d → SDEDiffusion d)
    (c : SDEState d → U → ℝ) (bs : ℕ → SDEState d → U → SDEState d)
    (σs : ℕ → SDEState d → SDEDiffusion d) (cs : ℕ → SDEState d → U → ℝ) : Prop where
  /-- (A5)(i), (2.13). -/
  diffusion : ∀ᵐ x, Tendsto (fun n => σs n x) atTop (𝓝 (σ x))
  /-- (A5)(ii), (2.14). -/
  controls : ∀ᵐ x, ∀ (ζs : ℕ → U) (ζ : U), Tendsto ζs atTop (𝓝 ζ) →
    Tendsto (fun n => cs n x (ζs n)) atTop (𝓝 (c x ζ)) ∧
    Tendsto (fun n => bs n x (ζs n)) atTop (𝓝 (b x ζ))

end DiffCtrlRobust


