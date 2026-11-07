-- Prove2me | Definitions.Def_SoftmaxAttnFD_KernelProducts
-- name    : SoftmaxAttnFD_KernelProducts
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T16:02:43.554657+00:00
-- url     : https://prove2.me/theorems/b74663a4-93e1-4df4-a5c1-cfd0728fe53b
-- title:
--   The problem $\mathrm{KP}_d$ and the predicate that it is solvable in $\tilde O(F_d(m,n))$
-- statement:
--   For rows $q_i\in\mathbb Q^d$, columns $k_j\in\mathbb Q^d$ and a tolerance $\eta\in\mathbb Q\cap(0,1]$, the **shifted kernel** is
--   $$T_{ij}=e^{q_i\cdot k_j-M_i},\qquad M_i=\max_{j\in[n]}q_i\cdot k_j.$$
--   The task is the forward product $Tw$, $w\in\mathbb Q^n$, or the transpose product $T^\top z$, $z\in\mathbb Q^m$, to coordinatewise additive error $\eta$. Integers $U,W\ge1$ bound the coordinates and the weights, and $b$ bounds all encoding lengths, $\eta$ included.
--
--   The input memory holds $m$, $n$, the mode ($0$ forward, $1$ transpose), $\eta$, the rows, the columns and the weights; the output triples follow.
--
--   `KPSolvable d` says: there are one program and constants $C>0$, $K$ such that every instance is solved by a Las Vegas run with expected bit cost at most
--   $$C\,F_d(m,n)\,\bigl(b+\log_2(m+n)+\log_2U+\log_2W\bigr)^K.$$
--
--   **Formalization Note** $\log(1/\eta)$ is covered by $b$, since $\eta$ has encoding length at most $b$. The maximum runs over a finite set that is nonempty under the hypothesis $n\ge1$.
-- source:
--   Huang, Chen, Softmax Attention with Any Temperature in Fixed Dimension, arXiv:2611.06055 (sha256 a60f7609…), Definition 5.3, pp.20–21

import Definitions.Def_SoftmaxAttnFD_Machine
import Definitions.Def_SoftmaxAttnFD_RatEnc
import Definitions.Def_SoftmaxAttnFD_F

namespace SoftmaxAttnFD

/-- The shifted kernel `T_{ij} = e^{q_i·k_j − M_i}`, `M_i = max_j q_i·k_j` (arXiv:2611.06055,
sha256 a60f7609…, Definition 5.3, p.20). The `⨆` runs over the finite nonempty `Fin n`: every
statement using `kernel` has `1 ≤ n`. -/
noncomputable def kernel {m n d : ℕ} (q : Fin m → Fin d → ℝ) (k : Fin n → Fin d → ℝ)
    (i : Fin m) (j : Fin n) : ℝ :=
  Real.exp (q i ⬝ᵥ k j - ⨆ j', q i ⬝ᵥ k j')

/-- The soft-O base of KP_d, BP_{d−1}: `b + log₂(m + n) + log₂ U + log₂ W`. It is at least 1 for
`m, n, U, W ≥ 1`. `log(1/η)` is covered by `b`, since `b` bounds the encoding of `η`. -/
noncomputable def lamKP (b m n U W : ℕ) : ℝ :=
  (b : ℝ) + Real.logb 2 ((m : ℝ) + n) + Real.logb 2 U + Real.logb 2 W

/-- The KP_d input cells in forward mode: `m, n, 0`, `η`, the rows, the columns, then `w`. -/
def kpForwardInput {m n d : ℕ} (η : RatEnc) (q : Fin m → Fin d → RatEnc)
    (k : Fin n → Fin d → RatEnc) (w : Fin n → RatEnc) : List ℕ :=
  [m, n, 0] ++ η.cells ++ matCells q ++ matCells k ++ vecCells w

/-- The KP_d input cells in transpose mode: `m, n, 1`, `η`, the rows, the columns, then `z`. -/
def kpTransposeInput {m n d : ℕ} (η : RatEnc) (q : Fin m → Fin d → RatEnc)
    (k : Fin n → Fin d → RatEnc) (z : Fin m → RatEnc) : List ℕ :=
  [m, n, 1] ++ η.cells ++ matCells q ++ matCells k ++ vecCells z

/-- A vector of `a` triples starting at `base` approximates `target` coordinatewise to error `η`. -/
def OutputWithin {a : ℕ} (base : ℕ) (target : Fin a → ℝ) (η : ℝ) (out : ℕ → ℕ) : Prop :=
  ∀ i : Fin a,
    ValidAt out (base + 3 * i.val) ∧
      |((valAt out (base + 3 * i.val) : ℚ) : ℝ) - target i| ≤ η

/-- Correct forward output of KP_d: `ô` approximates `T w` with error `η` (Definition 5.3, p.21). The
`m` output triples follow the input. -/
def kpForwardGood {m n d : ℕ} (η : RatEnc) (q : Fin m → Fin d → RatEnc)
    (k : Fin n → Fin d → RatEnc) (w : Fin n → RatEnc) : (ℕ → ℕ) → Prop :=
  OutputWithin (kpForwardInput η q k w).length
    (fun i => ∑ j, kernel (fun i l => (q i l).toReal) (fun j l => (k j l).toReal) i j
      * (w j).toReal) η.toReal

/-- Correct transpose output of KP_d: `ô` approximates `T^⊤ z` with error `η` (Definition 5.3, p.21).
The `n` output triples follow the input. -/
def kpTransposeGood {m n d : ℕ} (η : RatEnc) (q : Fin m → Fin d → RatEnc)
    (k : Fin n → Fin d → RatEnc) (z : Fin m → RatEnc) : (ℕ → ℕ) → Prop :=
  OutputWithin (kpTransposeInput η q k z).length
    (fun j => ∑ i, kernel (fun i l => (q i l).toReal) (fun j l => (k j l).toReal) i j
      * (z i).toReal) η.toReal

/-- The bounds of a KP_d instance (Definition 5.3, pp.20–21): `m, n, U, W ≥ 1`, `η ∈ (0, 1]`,
coordinates at most `U`, and `b` bounds every encoding length, `η` included. -/
structure KPBounds {m n d : ℕ} (η : RatEnc) (q : Fin m → Fin d → RatEnc)
    (k : Fin n → Fin d → RatEnc) (U W b : ℕ) : Prop where
  hm : 1 ≤ m
  hn : 1 ≤ n
  hU : 1 ≤ U
  hW : 1 ≤ W
  η_pos : 0 < η.toReal
  η_le : η.toReal ≤ 1
  η_bits : η.bits ≤ b
  hq : MatBounded q U b
  hk : MatBounded k U b

/-- KP_d is solved by a Las Vegas algorithm in expected time `Õ(F_d(m, n))` (arXiv:2611.06055,
Definition 5.3, pp.20–21, and the statements of Proposition 5.5, Proposition 5.6, Theorem 5.8).

**Formalization Note** One program reads the mode and solves both products. `P`, `C`, `K` come before
the instance, so soft-O hides a fixed polynomial in `lamKP`. The bounds `U`, `W`, `b` are bounds and
not inputs: the statement holds for every valid choice. The page uses `KP_d` for `d ≥ 2`; statements
carry that hypothesis. -/
def KPSolvable (d : ℕ) : Prop :=
  ∃ (P : TimeSpaceMA.Program) (C : ℝ) (K : ℕ), 0 < C ∧
    ∀ (m n : ℕ) (η : RatEnc) (q : Fin m → Fin d → RatEnc) (k : Fin n → Fin d → RatEnc)
      (U W b : ℕ), KPBounds η q k U W b →
      (∀ w : Fin n → RatEnc, VecBounded w W b →
        LasVegasWithin P (memOf (kpForwardInput η q k w)) (kpForwardGood η q k w)
          (C * F d m n * lamKP b m n U W ^ K)) ∧
      (∀ z : Fin m → RatEnc, VecBounded z W b →
        LasVegasWithin P (memOf (kpTransposeInput η q k z)) (kpTransposeGood η q k z)
          (C * F d m n * lamKP b m n U W ^ K))

end SoftmaxAttnFD


