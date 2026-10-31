-- Prove2me | Definitions.Def_StrategyproofMultidim_IsContinuous
-- name    : StrategyproofMultidim_IsContinuous
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T03:13:09.807337+00:00
-- url     : https://prove2.me/theorems/d5717166-e6db-4ba4-871f-6e48fc2467ac
-- title:
--   Continuous mechanism (class $\bar\Gamma$), read as indifference at a flip
-- statement:
--   A mechanism is **continuous** if whenever positive profiles $v^l\to\tilde v$ (with $\tilde v$ positive), buyer $i$'s decision on object $k$ equals $\zeta\in\{0,1\}$ along the sequence but not at $\tilde v$, then buyer $i$ is indifferent at $\tilde v$ between its truthful outcome and the bundle $(\zeta,d_i^{-k}(\tilde v))$ at the price the mechanism charges for it:
--
--   1. there is a positive report $w_i$ with $d_i(w_i,\tilde v_{-i})=(\zeta,d_i^{-k}(\tilde v))$, and
--   2. every such $w_i$ satisfies $u(\mu_i(w_i,\tilde v_{-i});\tilde v_i)=u(\mu_i(\tilde v);\tilde v_i)$.
--
--   $\bar\Gamma_{M,N}$ is the class of continuous mechanisms in $\Gamma_{M,N}$.
--
--   **Formalization Note** Printed Definition 4 uses the same price $p_i(\tilde v)$ on both sides; then the equation reads $\tilde v_i^k(\zeta-d_i^k(\tilde v))=0$, impossible as $\tilde v_i^k>0$, and no mechanism in $\Gamma_{M,N}$ is continuous (the Pivotal mechanism, which p.16 asserts to be continuous, fails it). The definition above follows the prose of p.12 ("she is indifferent between getting and not getting the object"). Convergence is in the product topology, which is the topology of the Frobenius distance of pp.11–12.
-- source:
--   Basu, Mukherjee, Strategyproof multidimensional mechanism design without unit demand, IIM Calcutta WPS No 875 (April 2022), Definition 4, p.12 (PDF p.13)

import Mathlib
import Definitions.Def_StrategyproofMultidim_util
import Definitions.Def_StrategyproofMultidim_PosProfile

namespace StrategyproofMultidim

/-- **Continuous mechanism, the class `Γ̄`** (Definition 4, p.12), in the reading of the
prose of p.12.
Basu, Mukherjee, *Strategyproof multidimensional mechanism design without unit demand*,
IIM Calcutta WPS No 875 (April 2022), p.12: "Definition 4. A mechanism μ is said to be continuous if for any ζ ∈ {0, 1}, any
i ∈ N, any k ∈ M, and any sequence of profiles {vˡ} that converges to ṽ; whenever dᵢᵏ(vˡ) = ζ
for all l, dᵢᵏ(ṽ) ≠ ζ ⟹ [u(dᵢ(ṽ), pᵢ(ṽ); ṽᵢ) = u((ζ, dᵢ⁻ᵏ(ṽ)), pᵢ(ṽ); ṽᵢ)]" and "whenever
the allotment decision of a buyer i is not preserved in limit, the transfer assigned to i at the
limit profile is such that she is indifferent between getting and not getting the object."

Whenever positive profiles `vˡ → ṽ` (with `ṽ` positive), buyer `i`'s decision on object `k` is
`ζ` along the sequence but not at `ṽ`, then (a) buyer `i` has a positive report `w` with which,
the others reporting `ṽ₋ᵢ`, it obtains the decision vector `(ζ, dᵢ⁻ᵏ(ṽ))`, and (b) every such
report gives buyer `i` (at its true valuation `ṽᵢ`) the same utility as truthful reporting.

**Formalization Note.** Read literally, the printed condition compares the same price on both
sides and reduces to `ṽᵢᵏ (ζ − dᵢᵏ(ṽ)) = 0`, impossible for `ṽᵢᵏ > 0`; the literal class is empty.
The bundle `(ζ, dᵢ⁻ᵏ(ṽ))` is therefore priced at what `μ` charges for it, at a report
`w` that obtains it. Convergence is in the product topology on `Fin n → Fin m → ℝ`, which equals
the topology of the Frobenius norm used on p.11–12. -/
def IsContinuous {n m : ℕ} (μ : Mechanism n m) : Prop :=
  ∀ (ζ : Bool) (i : Fin n) (k : Fin m) (vs : ℕ → Fin n → Fin m → ℝ) (v : Fin n → Fin m → ℝ),
    (∀ l, PosProfile (vs l)) → PosProfile v → Filter.Tendsto vs Filter.atTop (nhds v) →
    (∀ l, μ.q (vs l) i k = ζ) → μ.q v i k ≠ ζ →
    (∃ w : Fin m → ℝ, (∀ k', 0 < w k') ∧
        μ.q (Function.update v i w) i = Function.update (μ.q v i) k ζ) ∧
    ∀ w : Fin m → ℝ, (∀ k', 0 < w k') →
      μ.q (Function.update v i w) i = Function.update (μ.q v i) k ζ →
      util μ (Function.update v i w) i (v i) = util μ v i (v i)

end StrategyproofMultidim


