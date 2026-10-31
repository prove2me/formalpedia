-- Prove2me | Definitions.Def_StrategyproofMultidim_Mechanism
-- name    : StrategyproofMultidim_Mechanism
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T03:11:43.558011+00:00
-- url     : https://prove2.me/theorems/fd877acd-9561-4257-b680-71cf937db9c4
-- title:
--   Direct mechanism $\mu=(d,p)$ for selling $m$ objects to $n$ buyers
-- statement:
--   A **direct mechanism** for selling objects $M=\{1,\dots,m\}$ to buyers $N=\{1,\dots,n\}$ is a map $\mu:\mathcal V\to\mathcal D\times\mathbb R^N_+$ that assigns to every reported valuation profile $v$ a decision matrix $d(v)$, with $d_i^k(v)=1$ if and only if buyer $i$ is sold object $k$, and a price $p_i(v)$ paid by each buyer $i$.
--
--   Here a mechanism is an instance of the general direct mechanism $(q,t)$ (decision rule and transfers) with buyers $\mathrm{Fin}\,n$, types $v_i\in\mathbb R^m$ and outcomes the Boolean $n\times m$ matrices.
--
--   **Formalization Note** Buyer $i$ and object $k$ of the paper are Lean indices $i-1$, $k-1$. Decisions are Booleans. The paper's codomain and domain restrictions are not part of the type: feasibility and non-negative prices are the predicate `IsMechanism`, positivity of valuations is the hypothesis `PosProfile` carried by every axiom, so values at non-positive profiles play no role.
-- source:
--   Basu, Mukherjee, Strategyproof multidimensional mechanism design without unit demand, IIM Calcutta WPS No 875 (April 2022), §3, p.5 (PDF p.6)

import Mathlib
import Definitions.Def_MechanismDesign_VCG_Model

namespace StrategyproofMultidim

/-- **Direct mechanism for selling `m` objects to `n` buyers** (§3, p.5).
Basu, Mukherjee, *Strategyproof multidimensional mechanism design without unit demand*,
IIM Calcutta WPS No 875 (April 2022), p.5: "A direct mechanism employed to accomplish this allocation exercise must be a
function: μ : 𝒱 ⟶ 𝒟 × ℝᴺ₊."

A mechanism is the published general direct mechanism `(q, t)` of
`MechanismDesign.VCG.DirectMechanism`, with buyers `Fin n`, each buyer's type a valuation vector
`Fin m → ℝ`, and outcomes the `n × m` Boolean decision matrices: `μ.q v i k = true` means buyer
`i` is sold object `k` at the reported profile `v` (the paper's `dᵢᵏ(v) = 1`), and `μ.t i v` is
the price `pᵢ(v)` buyer `i` pays.

**Formalization Note.** Buyers are `Fin n` and objects `Fin m`; the paper's buyer `i` / object
`k` is Lean index `i - 1` / `k - 1`. Decisions are `Bool`. The restrictions of the paper's
codomain `𝒟 × ℝᴺ₊` (each object sold to at most one buyer, non-negative prices) and of its domain
`𝒱 = (ℝᵐ₊₊)ⁿ` (positive valuations) are not bundled into the type: they are the predicate
`IsMechanism` and the positivity hypotheses `PosProfile` carried by every axiom, so the values of
`μ` at non-positive profiles are irrelevant. -/
abbrev Mechanism (n m : ℕ) : Type :=
  MechanismDesign.VCG.DirectMechanism (fun _ : Fin n => Fin m → ℝ) (Fin n → Fin m → Bool)

end StrategyproofMultidim


