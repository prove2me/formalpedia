-- Prove2me | Definitions.Def_BBBV_RandomPermutation_QueryModel
-- name    : BBBV_RandomPermutation_QueryModel
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-06T19:05:48.474707+00:00
-- url     : https://prove2.me/theorems/7f9f3c79-6fcd-4b43-973d-e6b892319255
-- title:
--   §2 and §3.1 — quantum oracle query model and query magnitude
-- statement:
--   A **query algorithm** has a unit initial state, a finite sequence of oracle-independent unitary operators, and a set of accepting basis configurations. Its configurations contain an optional query string, an answer register, and a finite workspace. A query to a function $f$ adds $f(x)$ to the answer register; a configuration without a query is unchanged. At step $i$, the oracle operation precedes the algorithm's unitary operation. The acceptance probability is the sum of squared amplitudes on accepting configurations.
--
--   The **query magnitude** of a string $y$ in a state $\phi$ is
--
--   $$q_y(\phi)=\sum_{z,w}|\phi(\mathrm{some}\ y,z,w)|^2.$$
--
--   A machine decides a proposition with bounded error when its acceptance probability is at least $2/3$ if the proposition holds and at most $1/3$ otherwise. Binary strings of length $n$ are functions from $\{0,\ldots,n-1\}$ to $\mathbb Z/2\mathbb Z$.
--
--   **Formalization Note** This is the finite query model used in the proof, rather than a full quantum Turing machine. Queries at other lengths are fixed and absorbed into the unitaries. The optional query register includes a sector untouched by the oracle. One full-value query can be simulated with $n$ Boolean queries, and one Boolean query with two full-value queries; the latter transfer halves a constant in a Boolean-query lower bound.
-- source:
--   Bennett, Bernstein, Brassard and Vazirani, Strengths and weaknesses of quantum computing, arXiv:quant-ph/9701001v1, pp. 4–7, §2 and Definition 3.2

import Mathlib
import Definitions.Def_BBBV_RandomOracle_QueryModel

namespace BBBV.RandomPermutation

abbrev State (X R W : Type) [Fintype X] [Fintype R] [Fintype W] :=
  EuclideanSpace ℂ (BBBV.RandomOracle.Config X R W)

private def oracleEquiv {X R W : Type} [AddCommGroup R] (f : X → R) :
    BBBV.RandomOracle.Config X R W ≃ BBBV.RandomOracle.Config X R W where
  toFun c := match c with
    | (some x, z, w) => (some x, z + f x, w)
    | (none, z, w) => (none, z, w)
  invFun c := match c with
    | (some x, z, w) => (some x, z - f x, w)
    | (none, z, w) => (none, z, w)
  left_inv := by
    intro c
    rcases c with ⟨x, z, w⟩
    cases x <;> simp
  right_inv := by
    intro c
    rcases c with ⟨x, z, w⟩
    cases x <;> simp

noncomputable def oracleOp {X R W : Type} [Fintype X] [Fintype R] [Fintype W]
    [AddCommGroup R] (f : X → R) : State X R W ≃ₗᵢ[ℂ] State X R W :=
  LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ (oracleEquiv f)

structure QueryAlg (X R W : Type) [Fintype X] [Fintype R] [Fintype W]
    [AddCommGroup R] (T : ℕ) where
  init : State X R W
  init_norm : ‖init‖ = 1
  U : Fin T → (State X R W ≃ₗᵢ[ℂ] State X R W)
  accept : Finset (BBBV.RandomOracle.Config X R W)

noncomputable def state {X R W : Type} [Fintype X] [Fintype R] [Fintype W]
    [AddCommGroup R] {T : ℕ} (M : QueryAlg X R W T) (g : Fin T → X → R) :
    ℕ → State X R W :=
  Nat.rec M.init (fun i φ => if h : i < T then M.U ⟨i, h⟩ (oracleOp (g ⟨i, h⟩) φ) else φ)

noncomputable def final {X R W : Type} [Fintype X] [Fintype R] [Fintype W]
    [AddCommGroup R] {T : ℕ} (M : QueryAlg X R W T) (g : Fin T → X → R) :
    State X R W := state M g T

noncomputable def acceptProb {X R W : Type} [Fintype X] [Fintype R] [Fintype W]
    [AddCommGroup R] {T : ℕ} (M : QueryAlg X R W T) (g : Fin T → X → R) : ℝ :=
  ∑ c ∈ M.accept, ‖(final M g) c‖ ^ 2

noncomputable def queryMag {X R W : Type} [Fintype X] [Fintype R] [Fintype W]
    (y : X) (φ : State X R W) : ℝ :=
  ∑ z : R, ∑ w : W, ‖φ (some y, z, w)‖ ^ 2

def Decides {X R W : Type} [Fintype X] [Fintype R] [Fintype W]
    [AddCommGroup R] {T : ℕ} (M : QueryAlg X R W T) (g : Fin T → X → R)
    (b : Prop) : Prop :=
  (b → (2 / 3 : ℝ) ≤ acceptProb M g) ∧ (¬ b → acceptProb M g ≤ (1 / 3 : ℝ))

end BBBV.RandomPermutation


