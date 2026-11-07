-- Prove2me | Definitions.Def_SoftmaxAttnFD_BiasedProducts
-- name    : SoftmaxAttnFD_BiasedProducts
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T16:03:43.332206+00:00
-- url     : https://prove2.me/theorems/dfefade5-5d82-492d-9d82-817826ba742e
-- title:
--   The problem $\mathrm{BP}_{d-1}$ and the predicate that it is solvable in $\tilde O(F_d(m,n))$
-- statement:
--   An instance consists of rows $(u_i,b_i)\in\mathbb Q^{d-1}\times\mathbb Q$ and columns $(p_j,c_j)\in\mathbb Q^{d-1}\times\mathbb Q$, with nonpositive scores
--   $$x_{ij}=u_i\cdot p_j+b_i+c_j\le0,\qquad S_{ij}=e^{x_{ij}},$$
--   weights $w\in\mathbb Q^n$ and a tolerance $\eta\in\mathbb Q\cap(0,1]$. The task is to approximate $Sw$ to coordinatewise additive error $\eta$. Integers $U,W\ge1$ bound coordinates and biases, and weights, and $b$ bounds all encoding lengths.
--
--   `BPSolvable d` says: there are one program and constants $C>0$, $K$ such that every instance with $d-1$ bilinear coordinates is solved by a Las Vegas run with expected bit cost at most $C\,F_d(m,n)\,(b+\log_2(m+n)+\log_2U+\log_2W)^K$.
--
--   **Formalization Note** The index is $d$, not $d-1$: the budget is $F_d$, as in Propositions 5.5 and 5.6. The promise $x_{ij}\le0$ is a hypothesis on the instance.
-- source:
--   Huang, Chen, Softmax Attention with Any Temperature in Fixed Dimension, arXiv:2611.06055 (sha256 a60f7609…), Definition 5.4, p.21

import Definitions.Def_SoftmaxAttnFD_KernelProducts

namespace SoftmaxAttnFD

/-- The exact score `x_{ij} = u_i · p_j + b_i + c_j` of BP_{d−1} (arXiv:2611.06055, sha256 a60f7609…,
Definition 5.4, p.21). -/
def bpScore {m n e : ℕ} (u : Fin m → Fin e → RatEnc) (bi : Fin m → RatEnc)
    (p : Fin n → Fin e → RatEnc) (c : Fin n → RatEnc) (i : Fin m) (j : Fin n) : ℚ :=
  qdot (u i) (p j) + (bi i).val + (c j).val

/-- The BP_{d−1} input cells: `m, n`, `η`, then the rows `(u_i, b_i)`, the columns `(p_j, c_j)`, and
`w`. Here `e` is the bilinear dimension `d − 1`. -/
def bpInput {m n e : ℕ} (η : RatEnc) (u : Fin m → Fin e → RatEnc) (bi : Fin m → RatEnc)
    (p : Fin n → Fin e → RatEnc) (c : Fin n → RatEnc) (w : Fin n → RatEnc) : List ℕ :=
  [m, n] ++ η.cells ++
    ((List.finRange m).flatMap fun i => vecCells (u i) ++ (bi i).cells) ++
    ((List.finRange n).flatMap fun j => vecCells (p j) ++ (c j).cells) ++
    vecCells w

/-- Correct output of BP_{d−1}: `m` triples after the input, approximating `S w` with
`S_{ij} = e^{x_{ij}}` to coordinatewise additive error `η` (Definition 5.4, p.21). -/
def bpGood {m n e : ℕ} (η : RatEnc) (u : Fin m → Fin e → RatEnc) (bi : Fin m → RatEnc)
    (p : Fin n → Fin e → RatEnc) (c : Fin n → RatEnc) (w : Fin n → RatEnc) : (ℕ → ℕ) → Prop :=
  OutputWithin (bpInput η u bi p c w).length
    (fun i => ∑ j, Real.exp ((bpScore u bi p c i j : ℚ) : ℝ) * (w j).toReal) η.toReal

/-- The bounds of a BP_{d−1} instance (Definition 5.4, p.21): `m, n, U, W ≥ 1`, `η ∈ (0, 1]`, all
scores nonpositive, coordinates and biases at most `U`, weights at most `W`, and `b` bounds every
encoding length. -/
structure BPBounds {m n e : ℕ} (η : RatEnc) (u : Fin m → Fin e → RatEnc) (bi : Fin m → RatEnc)
    (p : Fin n → Fin e → RatEnc) (c : Fin n → RatEnc) (w : Fin n → RatEnc) (U W b : ℕ) : Prop where
  hm : 1 ≤ m
  hn : 1 ≤ n
  hU : 1 ≤ U
  hW : 1 ≤ W
  η_pos : 0 < η.toReal
  η_le : η.toReal ≤ 1
  η_bits : η.bits ≤ b
  hu : MatBounded u U b
  hbi : VecBounded bi U b
  hp : MatBounded p U b
  hc : VecBounded c U b
  hw : VecBounded w W b
  score_nonpos : ∀ i j, bpScore u bi p c i j ≤ 0

/-- BP_{d−1} is solved by a Las Vegas algorithm in expected time `Õ(F_d(m, n))` (arXiv:2611.06055,
Definition 5.4, p.21; the budget is from Propositions 5.5 and 5.6).

**Formalization Note** The index is `d`, with `d − 1` bilinear coordinates: the budget is `F_d`, not
`F_{d−1}`. The promise `x_{ij} ≤ 0` is a hypothesis on the instance and is not checked by the
program. -/
def BPSolvable (d : ℕ) : Prop :=
  ∃ (P : TimeSpaceMA.Program) (C : ℝ) (K : ℕ), 0 < C ∧
    ∀ (m n : ℕ) (η : RatEnc) (u : Fin m → Fin (d - 1) → RatEnc) (bi : Fin m → RatEnc)
      (p : Fin n → Fin (d - 1) → RatEnc) (c : Fin n → RatEnc) (w : Fin n → RatEnc) (U W b : ℕ),
      BPBounds η u bi p c w U W b →
      LasVegasWithin P (memOf (bpInput η u bi p c w)) (bpGood η u bi p c w)
        (C * F d m n * lamKP b m n U W ^ K)

end SoftmaxAttnFD


