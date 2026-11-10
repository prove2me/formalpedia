-- Prove2me | Definitions.Def_SparseCCE_ThreePlayer_SparseCCE3
-- name    : SparseCCE_ThreePlayer_SparseCCE3
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-10T05:05:15.633347+00:00
-- url     : https://prove2.me/theorems/2b8a5c26-b9c7-409a-bdac-7024598fbb1d
-- title:
--   The search problem of Theorem 1: $1/p(N)$-approximate $T$-sparse CCE of a three-player game
-- statement:
--   Instances are three-player normal-form games with action sets $\mathrm{Fin}\,m_j$, $m_j\ge 1$, and rational utilities $U_j(b)\in[0,1]$. Their code `gameCode m U` is $m_1,m_2,m_3$ in self-delimiting binary followed, for each player, by its utility table as a rational vector of length $m_1m_2m_3$ (profiles in the canonical mixed-radix order). $N$ is the length of the instance string.
--
--   An answer is the code `sparseCode m w q` of rational weights $w\in\Delta([T])$ (a rational vector) followed by the rational mixed strategies $q^{(t)}_j\in\Delta(\mathrm{Fin}\,m_j)$, such that $\mu=\sum_t w_t\bigotimes_j q^{(t)}_j$ is a $1/p(N)$-CCE of the game (utilities read as reals). Every rational representation is an answer; there is no bound on the length of answers. $p$ is a polynomial with natural coefficients; $p(N)$ is evaluated at the instance length.
--
--   `SparseCCE3 T p` is a `TetrisHard.Rows.SearchProblem` (validity predicate and answer relation on bit strings), the setting of the published PPAD definitions.
-- source:
--   Fan Chen, Constantinos Daskalakis, Gabriele Farina, Noah Golowich and Charalampos Platanos, "On the Computation of Sparse Equilibria in Normal-Form Games", STOC 2027 submission (citation_basis: published; PDF SHA256 796c83067187974f1685ea4343c0c56d9f89e99484824615342fb7178ee023b5; PDF page = printed page). Theorem 1, p. 5; §2.2, pp. 12–13.

import Mathlib
import Definitions.Def_TetrisHard_Rows_Search
import Definitions.Def_CardinalMatching_encRatMatrix
import Definitions.Def_SparseCCE_ThreePlayer_NormalForm

namespace SparseCCE.ThreePlayer

open scoped BigOperators

/-- Action profiles of a three-player game in which player `j` has the actions `Fin (m j)`. -/
abbrev Profile3 (m : Fin 3 → ℕ) := (j : Fin 3) → Fin (m j)

/-- The binary code of a three-player normal-form game with rational utilities (the instance
of Theorem 1, p. 5, and §2.2, p. 12): the three action counts `m₁, m₂, m₃` in self-delimiting
binary, then, for each player `j`, its utility table as a rational vector of length
`m₁ m₂ m₃`, profiles listed in the canonical mixed-radix order `finPiFinEquiv`. -/
def gameCode (m : Fin 3 → ℕ) (U : Fin 3 → Profile3 m → ℚ) : List Bool :=
  (List.finRange 3).flatMap (fun j => QAlgorithms.LocalHamiltonian.encBin (m j)) ++
    (List.finRange 3).flatMap (fun j =>
      CardinalMatching.encRatVec (∏ i, m i) (fun k => U j (finPiFinEquiv.symm k)))

/-- The binary code of a `T`-sparse distribution given by its weights and components (§2.2,
p. 13: "represented by its weights and components"): the weight vector `w ∈ ℚ^T`, then for each
component `t` and player `j` the mixed strategy `p^{(t)}_j ∈ ℚ^{m_j}`. -/
def sparseCode {T : ℕ} (m : Fin 3 → ℕ) (w : Fin T → ℚ) (p : Fin T → (j : Fin 3) → Fin (m j) → ℚ) :
    List Bool :=
  CardinalMatching.encRatVec T w ++
    (List.finRange T).flatMap (fun t => (List.finRange 3).flatMap (fun j =>
      CardinalMatching.encRatVec (m j) (p t j)))

/-- The utilities of a rational game, as real numbers. -/
def realUtil {m : Fin 3 → ℕ} (U : Fin 3 → Profile3 m → ℚ) : Fin 3 → Profile3 m → ℝ :=
  fun j b => (U j b : ℝ)

/-- **The search problem of Theorem 1** (p. 5; §2.2, pp. 12–13): computing a
`1/p(N)`-approximate `T`-sparse coarse correlated equilibrium of a three-player normal-form game.

* Instances: codes `gameCode m U` of three-player games with `m_j ≥ 1` actions per player and
  rational utilities in `[0, 1]`; `N` is the length of the instance string.
* Answers: codes `sparseCode m w p` of rational weights `w ∈ Δ([T])` and rational mixed
  strategies `p^{(t)}_j ∈ Δ(B_j)` such that `μ = ∑_t w_t ⊗_j p^{(t)}_j` is a
  `1/p(N)`-approximate CCE. Every rational representation is an answer (no length bound). -/
def SparseCCE3 (T : ℕ) (p : Polynomial ℕ) : TetrisHard.Rows.SearchProblem where
  valid s := ∃ (m : Fin 3 → ℕ) (U : Fin 3 → Profile3 m → ℚ),
    (∀ j, 1 ≤ m j) ∧ (∀ j b, 0 ≤ U j b ∧ U j b ≤ 1) ∧ s = gameCode m U
  answer s t := ∃ (m : Fin 3 → ℕ) (U : Fin 3 → Profile3 m → ℚ),
    (∀ j, 1 ≤ m j) ∧ (∀ j b, 0 ≤ U j b ∧ U j b ≤ 1) ∧ s = gameCode m U ∧
    ∃ (w : Fin T → ℚ) (q : Fin T → (j : Fin 3) → Fin (m j) → ℚ),
      IsDist (fun t => (w t : ℝ)) ∧ (∀ t j, IsDist (fun a => (q t j a : ℝ))) ∧
      t = sparseCode m w q ∧
      IsEpsCCE (realUtil U) (mixture (fun t => (w t : ℝ)) (fun t j a => (q t j a : ℝ)))
        (1 / ((p.eval s.length : ℕ) : ℝ))

end SparseCCE.ThreePlayer


