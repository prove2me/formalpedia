-- Prove2me | Definitions.Def_MonotonicSolutions_StrongMono_Axioms
-- name    : MonotonicSolutions_StrongMono_Axioms
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-27T20:03:08.997873+00:00
-- url     : https://prove2.me/theorems/3335a4c7-a8eb-4798-9e8a-d43483f3cda1
-- title:
--   Strong monotonicity (6), marginality (7), symmetry, dummy axiom (11), additivity
-- statement:
--   Let $\varphi$ assign to every cooperative game $v$ on $N = \{1, \dots, n\}$ (with $v(\emptyset) = 0$) a vector $\varphi(v) \in \mathbb{R}^N$, and let $v^i(S)$ denote the marginal contribution of player $i$ to the coalition $S$, Eq. (3). The following properties of $\varphi$ are used.
--
--   1. **Strong monotonicity**, Eq. (6): for all games $v, w$ and every player $i$,
--   $$v^i(S) \ge w^i(S) \text{ for all } S \subseteq N \quad \Longrightarrow \quad \varphi_i(v) \ge \varphi_i(w).$$
--   2. **Marginality** (independence), Eq. (7): for all games $v, w$ and every player $i$,
--   $$v^i(S) = w^i(S) \text{ for all } S \subseteq N \quad \Longrightarrow \quad \varphi_i(v) = \varphi_i(w).$$
--   3. **Symmetry**: for every permutation $\pi$ of $N$, every game $v$ and every player $i$,
--   $$\varphi_{\pi i}(\pi v) = \varphi_i(v), \qquad \text{where } (\pi v)(\pi S) = v(S) \text{ for all } S,$$
--   that is, $(\pi v)(T) = v(\pi^{-1} T)$: player $\pi i$ plays in $\pi v$ the role that player $i$ plays in $v$.
--   4. **Dummy axiom**, Eq. (11): for every game $v$ and every player $i$, $v^i(S) = 0$ for all $S$ implies $\varphi_i(v) = 0$.
--   5. **Additivity**: $\varphi(v + w) = \varphi(v) + \varphi(w)$ for all games $v, w$, where $(v+w)(S) = v(S) + w(S)$.
--
--   Strong monotonicity and symmetry are the two axioms of Theorem 2; marginality, the dummy axiom and additivity appear in the remarks after its proof.
--
--   **Formalization Note** The paper prints the permuted game as $\pi v(S) = v(\pi S)$ together with $\varphi_{\pi i}(\pi v) = \varphi_i(v)$. Read literally, the two halves are inconsistent: with $(\pi v)(S) = v(\pi S)$, the Shapley value satisfies $\mathrm{Sh}_j(\pi v) = \mathrm{Sh}_{\pi j}(v)$, so the displayed condition would require $\mathrm{Sh}_{\pi^2 i}(v) = \mathrm{Sh}_i(v)$, which fails for a 3-cycle and a game whose players differ; Theorem 2 would then be false. We formalize the standard reading $(\pi v)(\pi S) = v(S)$, i.e. `permGame π v T = v (π⁻¹ '' T)`. For transpositions, the only permutations the proof uses, the two readings coincide. Strong monotonicity is stated as `w^i(S) ≤ v^i(S) ∀ S → φ_i(w) ≤ φ_i(v)`, quantifying over all coalitions $S$ as in (3). Additivity uses the game `addGame v w` with values $v(S) + w(S)$.
-- source:
--   Young, Monotonic Solutions of Cooperative Games, Int. J. Game Theory 14 (1985), p. 69, Eq. (6) and symmetry; p. 70, Eq. (7); p. 71, Eq. (11) and Shapley's additivity axiom

import Mathlib
import Definitions.Def_MonotonicSolutions_StrongMono_Game

namespace MonotonicSolutions.StrongMono

/-- Strong monotonicity, Eq. (6) of Young (1985, p. 69): for all games `v, w` and every player
`i`, if `w^i(S) ≤ v^i(S)` for every coalition `S`, then `φ_i(w) ≤ φ_i(v)`. -/
def IsStronglyMonotonic {n : ℕ} (φ : Game n → Fin n → ℝ) : Prop :=
  ∀ (v w : Game n) (i : Fin n),
    (∀ S : Finset (Fin n), marginal w.1 i S ≤ marginal v.1 i S) → φ w i ≤ φ v i

/-- Marginality (independence), Eq. (7) of Young (1985, p. 70): a player's allocation depends
only on the vector of his marginal contributions; if `v^i(S) = w^i(S)` for every coalition `S`,
then `φ_i(v) = φ_i(w)`. -/
def IsMarginal {n : ℕ} (φ : Game n → Fin n → ℝ) : Prop :=
  ∀ (v w : Game n) (i : Fin n),
    (∀ S : Finset (Fin n), marginal v.1 i S = marginal w.1 i S) → φ v i = φ w i

/-- The permuted game `πv` (Young 1985, p. 69), in the standard reading `(πv)(πS) = v(S)`,
i.e. `(πv)(T) = v(π⁻¹ T)`: the coalition `π S` plays in `πv` the role `S` plays in `v`. -/
def permGame {n : ℕ} (π : Equiv.Perm (Fin n)) (v : Game n) : Game n :=
  ⟨fun T => v.1 (T.map π.symm.toEmbedding), by simpa using v.2⟩

/-- Symmetry (Young 1985, p. 69): for every permutation `π` of `N`, every game `v` and every
player `i`, `φ_{π i}(πv) = φ_i(v)`, where `(πv)(πS) = v(S)`. -/
def IsSymmetric {n : ℕ} (φ : Game n → Fin n → ℝ) : Prop :=
  ∀ (π : Equiv.Perm (Fin n)) (v : Game n) (i : Fin n), φ (permGame π v) (π i) = φ v i

/-- Shapley's dummy axiom, Eq. (11) of Young (1985, p. 71): if `v^i(S) = 0` for every
coalition `S`, then `φ_i(v) = 0`. -/
def SatisfiesDummy {n : ℕ} (φ : Game n → Fin n → ℝ) : Prop :=
  ∀ (v : Game n) (i : Fin n), (∀ S : Finset (Fin n), marginal v.1 i S = 0) → φ v i = 0

/-- The sum `v + w` of two games, `(v + w)(S) = v(S) + w(S)`; it vanishes at `∅`. -/
def addGame {n : ℕ} (v w : Game n) : Game n :=
  ⟨fun S => v.1 S + w.1 S, by simp [v.2, w.2]⟩

/-- Shapley's additivity axiom (Young 1985, p. 71): `φ(v + w) = φ(v) + φ(w)` for all games
`v, w`. -/
def IsAdditive {n : ℕ} (φ : Game n → Fin n → ℝ) : Prop :=
  ∀ v w : Game n, φ (addGame v w) = φ v + φ w

end MonotonicSolutions.StrongMono


