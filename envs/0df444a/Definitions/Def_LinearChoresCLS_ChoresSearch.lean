-- Prove2me | Definitions.Def_LinearChoresCLS_ChoresSearch
-- name    : LinearChoresCLS_ChoresSearch
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T21:46:44.550725+00:00
-- url     : https://prove2.me/theorems/b36a9d11-02e0-4f27-92a8-59c0527fd06b
-- title:
--   The search problem of computing a competitive equilibrium of a rational linear chores market
-- statement:
--   An instance is a chores market with $n_A\ge1$ agents, $n_C\ge1$ chores and strictly positive rational disutilities, earning requirements and supplies, encoded in binary. An answer is the encoding of an **exact rational competitive equilibrium** $(p,z)$, $p\in\mathbb Q^{n_C}$, $z\in\mathbb Q^{n_A\times n_C}$, in the sense of Definition 2.2.
--
--   This is the problem that Theorem 1.1 classifies as CLS-complete.
--
--   **Formalization Note** Agents and chores are `Fin nA`, `Fin nC`; the encoding is self-delimiting (sizes, disutility rows, earning requirements, supplies) using the public encoders of `NetworkEquilibriumCLS.LinearNash`. Every rational competitive equilibrium is an answer; answers have no length bound here.
-- source:
--   Liu–Ma–Tao–Yang–Zheng, Competitive Equilibrium for Linear Chores is CLS-complete, arXiv:2611.06589 (held version, sha256 85d34a9e048d151ecff70a8614b9c2dd44307d5cf60faba74d14b2dd7eedc0b5), Theorem 1.1, p.4; Definition 2.2, p.6; Proposition 4.1, p.11 ("exact rational equilibrium")

import Mathlib
import Definitions.Def_NetworkEquilibriumCLS_LinearNash_Encoding
import Definitions.Def_LinearChoresCLS_ChoresMarket

open NetworkEquilibriumCLS.LinearNash

namespace LinearChoresCLS

/-- A **chores market with rational data** on `nA` agents `Fin nA` and `nC` chores `Fin nC`
(arXiv:2611.06589, held version sha256 85d34a9e…, Definition 2.1, p.6; Proposition 4.1, p.11:
"strictly positive rational data"). -/
structure RatChoresMarket (nA nC : ℕ) where
  disutil : Fin nA → Fin nC → ℚ
  earn : Fin nA → ℚ
  supply : Fin nC → ℚ

/-- The real chores market underlying a rational one (each datum cast to `ℝ`). -/
def RatChoresMarket.toReal {nA nC : ℕ} (F : RatChoresMarket nA nC) :
    ChoresMarket (Fin nA) (Fin nC) where
  disutil a j := (F.disutil a j : ℝ)
  earn a := (F.earn a : ℝ)
  supply j := (F.supply j : ℝ)

/-- Self-delimiting binary encoding of a rational chores market: `nA`, `nC`, the disutility rows,
the earning requirements and the supplies, with the public encoders of
`NetworkEquilibriumCLS.LinearNash`. -/
def encChores {nA nC : ℕ} (F : RatChoresMarket nA nC) : List Bool :=
  encNat nA ++ encNat nC ++
    encList (encList encRat) (List.ofFn fun a => List.ofFn (F.disutil a)) ++
    encVector F.earn ++ encVector F.supply

/-- Encoding of a rational price–allocation pair `(p, z)`: the price vector, then the rows `z_a`. -/
def encCE {nA nC : ℕ} (p : Fin nC → ℚ) (z : Fin nA → Fin nC → ℚ) : List Bool :=
  encVector p ++ encList (fun r : Fin nC → ℚ => encVector r) (List.ofFn z)

/-- **Computing a competitive equilibrium of a linear Fisher market with chores**, as a search
problem (arXiv:2611.06589, Theorem 1.1, p.4; Definition 2.2, p.6; "exact rational equilibrium",
p.11): an instance is the encoding of a market with `nA ≥ 1` agents, `nC ≥ 1` chores and strictly
positive rational data; an answer is the encoding of a rational price–allocation pair `(p, z)` that
is a competitive equilibrium (Definition 2.2) of that market.

**Formalization Note.** Every exact rational competitive equilibrium is an answer. Answers have no
length bound here; `bounded choresCESearch k` adds one. -/
def choresCESearch : SearchProblem where
  valid x := ∃ nA nC, 0 < nA ∧ 0 < nC ∧ ∃ F : RatChoresMarket nA nC, F.toReal.Valid ∧
    encChores F = x
  answer x y := ∃ nA nC, 0 < nA ∧ 0 < nC ∧ ∃ F : RatChoresMarket nA nC, F.toReal.Valid ∧
    encChores F = x ∧ ∃ (p : Fin nC → ℚ) (z : Fin nA → Fin nC → ℚ), encCE p z = y ∧
      F.toReal.IsCE (fun j => (p j : ℝ)) (fun a j => (z a j : ℝ))

end LinearChoresCLS


