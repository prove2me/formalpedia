-- Prove2me | Definitions.Def_SmoothedNash_BoundedDensity
-- name    : SmoothedNash_BoundedDensity
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T16:49:19.549306+00:00
-- url     : https://prove2.me/theorems/73690ae7-405c-4fe1-9530-bc7612e7a53d
-- title:
--   Assumption 1.18: bounded density games
-- statement:
--   Let $G$ be a random game on a probability space $(\Omega, \mathcal F, P)$ and let $M \in \mathbb R$. **Assumption 1.18 (bounded density games)** holds with constant $M$ if $M \ge 1$ and, for every mixed strategy profile $x \in (\Delta_n)^m$, the random deviation payoff vector $U(x) \in [0, 1]^{mn}$ has a probability density on $[0, 1]^{mn}$ that is everywhere at most $M^{mn}$.
--
--   Equivalently, for every Borel set $S \subseteq \mathbb R^{mn}$,
--   $$
--   P\bigl[U(x) \in S\bigr] \le M^{mn} \, \lambda\bigl(S \cap [0, 1]^{mn}\bigr),
--   $$
--   where $\lambda$ is Lebesgue measure on $\mathbb R^{mn}$.
--
--   This is the smoothed-analysis hypothesis under which Theorem 2.2 bounds the expected running time. Random action costs with bounded densities satisfy it (Corollary 2.11).
--
--   **Formalization Note** The assumption is stated as the measure inequality above. A density bounded by $M^{mn}$ on the cube gives it; conversely the inequality forces $U(x) \in [0, 1]^{mn}$ almost surely and gives a density at most $M^{mn}$ almost everywhere, which can be modified on a null set. The bound $M \ge 1$ is part of the assumption, as printed. Measurability of the random game is a hypothesis of the theorems.
-- source:
--   Attias–Dagan–Daskalakis–Yao–Zampetakis, Nash Equilibria, Variational Inequalities, and Fixed Points: Beating Brute Force via Smoothed Analysis, STOC 2027 submission (manuscript sha256 3f9ea37d…77a1ea53), Assumption 1.18, p.7

import Mathlib
import Definitions.Def_agt_games
import Definitions.Def_SmoothedNash_Game
import Definitions.Def_SmoothedNash_devVec
open MeasureTheory
open scoped ENNReal

namespace SmoothedNash

/-- **Assumption 1.18 (Bounded Density Games)** (Attias–Dagan–Daskalakis–Yao–Zampetakis, *Nash Equilibria, Variational Inequalities, and Fixed Points: Beating Brute Force via Smoothed Analysis*, STOC 2027 submission manuscript (sha256 3f9ea37d…77a1ea53), p.7), for a random game `G` on the
probability space `(Ω, P)`: `M ≥ 1`, and for every mixed strategy profile `x ∈ (Δ_n)^m` the random
deviation payoff vector `U(x) ∈ [0, 1]^{mn}` has a probability density on `[0, 1]^{mn}` that is
everywhere at most `M^{mn}`.

**Formalization Note** The density condition is stated as the equivalent measure inequality
`P[U(x) ∈ S] ≤ M^{mn} · λ(S ∩ [0, 1]^{mn})` for every Borel `S ⊆ ℝ^{mn}`, with `λ` Lebesgue
measure on `ℝ^{mn}` (`Fin m × Fin n → ℝ`). A density bounded by `M^{mn}` on the cube gives the
inequality; conversely the inequality forces `U(x) ∈ [0, 1]^{mn}` almost surely and absolute
continuity with respect to `λ` on the cube with Radon–Nikodym derivative at most `M^{mn}` almost
everywhere, which can be changed on a null set. The bound `M ≥ 1` is bundled as printed ("There
exists some `M ≥ 1`"). Measurability of the random game is a hypothesis of the theorems. -/
def BoundedDensity {m n : ℕ} {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (G : Ω → Game m n) (M : ℝ) : Prop :=
  1 ≤ M ∧ ∀ x : Fin m → Fin n → ℝ, AGT.IsMixedProfile (S := fun _ : Fin m => Fin n) x →
    ∀ S : Set (Fin m × Fin n → ℝ), MeasurableSet S →
      P {ω | devVec (G ω) x ∈ S} ≤ ENNReal.ofReal (M ^ (m * n)) * volume (S ∩ Set.Icc 0 1)

end SmoothedNash


