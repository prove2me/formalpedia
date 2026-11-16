-- Prove2me | Definitions.Def_CEPolytopeHard_Supplement_fixedSetProblem
-- name    : CEPolytopeHard_Supplement_fixedSetProblem
-- status  : Definition
-- author  : @iris
-- created : 2026-11-15T21:10:56.434811+00:00
-- url     : https://prove2.me/theorems/4ac9cdd5-5bbb-4dba-ab30-54b46323b01f
-- title:
--   Search problem: a $d^{-c}$-fixed set with at most $d^C$ points of an $L$-Lipschitz circuit map
-- statement:
--   Fix reals $L$, $C$, $c$. The search problem $\mathrm{FixedSet}(L,C,c)$ is the following.
--
--   1. **Instance.** The binary code of a dimension $d\ge 1$ and a valid well-behaved arithmetic circuit $F$ (gates $+,-,\times,\min,\max,>$ with rational constants) with $d$ inputs and $d$ outputs, whose map $f:[0,1]^d\to\mathbb R^d$ satisfies the promise that $f([0,1]^d)\subseteq[0,1]^d$ and
--   $$\|f(x)-f(y)\|_2\le L\,\|x-y\|_2\qquad (x,y\in[0,1]^d).$$
--   2. **Answer.** The code of a list of rational vectors of length $d$ whose set $S$ of points satisfies $|S|\le d^C$ and is a $d^{-c}$-fixed set of $f$ (Definition 3.2): there are a Markov chain $P$ on $S$ and a stationary distribution $\mu$ of $P$ with
--   $$\mathbb E_{i\sim\mu}\Big\|x_i-\mathbb E_{j\sim P(i)}f(x_j)\Big\|_2\le d^{-c}.$$
--
--   This is the problem whose PPAD-hardness is Theorem 1.
--
--   **Formalization Note** $\|\cdot\|_2$ is the normalized norm $\big(\tfrac1d\sum_i v_i^2\big)^{1/2}$ of Sections 3–4 (a Lipschitz constant is the same in the unnormalized norm). Circuits are the public `NadlerCLS.Circ`, evaluated exactly; well-behavedness (true-multiplication depth at most $\log_2$ of the size) makes them evaluable in polynomial time. $d^C$ and $d^{-c}$ are real powers; duplicate listed points are merged.
-- source:
--   Anagnostides–Daskalakis–Farina–Golowich–Sandholm–Zhang, The Complexity of Correlated Equilibria Beyond Normal-Form Games, arXiv:2605.17665 (held version of November 2, 2026, sha256 6aec500a…7820), Theorem 1, p.3 and p.15; Definition 3.2, p.13; Section 2.1, p.10

import Mathlib
import Definitions.Def_TetrisHard_Rows_Search
import Definitions.Def_NadlerCLS_Circ
import Definitions.Def_CorrelatedAuctionComplexity_Main_BinaryCodec
import Definitions.Def_CEPolytopeHard_lenList
import Definitions.Def_CEPolytopeHard_nnorm
import Definitions.Def_CEPolytopeHard_IsFixedSet

set_option autoImplicit false

namespace CEPolytopeHard.Supplement

open NetworkEquilibriumCLS.LinearNash CorrelatedAuctionComplexity.Main

/-- the real point of `[0,1]^d`-coordinates of a listed rational vector (missing entries `0`) -/
def ratVec (d : ℕ) (v : List ℚ) : Fin d → ℝ := fun j => ((v.getD j.val 0 : ℚ) : ℝ)

/-- the map `ℝ^d → ℝ^d` computed by a circuit with `d` inputs and `d` outputs (raw values) -/
noncomputable def circMap (d : ℕ) (F : NadlerCLS.Circ) : (Fin d → ℝ) → Fin d → ℝ :=
  fun x j => F.eval (ins := d) (outs := d) x j

/-- The **search problem of computing a `d^{−c}`-fixed set with at most `d^C` points** of an
`L`-Lipschitz map `[0,1]^d → [0,1]^d` given by an arithmetic circuit
(Anagnostides–Daskalakis–Farina–Golowich–Sandholm–Zhang, *The Complexity of Correlated Equilibria
Beyond Normal-Form Games*, arXiv:2605.17665, held version of November 2, 2026, sha256
6aec500a…7820, Theorem 1, p.3 and p.15: "given a Lipschitz function f : [0, 1]^d → [0, 1]^d that
can be evaluated in polynomial time, compute a d^{−c}-fixed set S of f with |S| ≤ d^C"; Section
2.1, p.10: "All numbers are rational numbers encoded in binary. Functions are given as arithmetic
circuits with standard gates").

* An instance is the code `encNat d ++ encCirc F` of a dimension `d ≥ 1` and a valid well-behaved
  circuit `F` with `d` inputs and `d` outputs whose map `f` sends `[0,1]^d` into `[0,1]^d` and is
  `L`-Lipschitz on `[0,1]^d`: `‖f(x) − f(y)‖₂ ≤ L‖x − y‖₂`.
* An answer is the code of a list of rational vectors of length `d`; their set `S` of real points
  has at most `d^C` elements and is a `d^{−c}`-fixed set of `f` (Definition 3.2, p.13).

**Formalization Note** Circuits are the public `NadlerCLS.Circ` (gates `+, −, ×, min, max, >`
with rational constants, true-multiplication depth at most `log₂` of the size, so that they are
evaluable in polynomial time). The norm is the normalized `nnorm` of Sections 3–4; a Lipschitz
constant is the same for the unnormalized norm. `C`, `c` are real and `d^C`, `d^{−c}` are real
powers. Duplicate listed points are merged (`S` is a `Finset`). -/
noncomputable def fixedSetProblem (L C c : ℝ) : TetrisHard.Rows.SearchProblem where
  valid s := ∃ (d : ℕ) (F : NadlerCLS.Circ), encNat d ++ NadlerCLS.encCirc F = s ∧ 0 < d ∧
    F.Valid d d ∧ Set.MapsTo (circMap d F) (Set.Icc 0 1) (Set.Icc 0 1) ∧
    ∀ x ∈ Set.Icc (0 : Fin d → ℝ) 1, ∀ y ∈ Set.Icc (0 : Fin d → ℝ) 1,
      nnorm (circMap d F x - circMap d F y) ≤ L * nnorm (x - y)
  answer s t := ∃ (d : ℕ) (F : NadlerCLS.Circ), encNat d ++ NadlerCLS.encCirc F = s ∧ 0 < d ∧
    F.Valid d d ∧ Set.MapsTo (circMap d F) (Set.Icc 0 1) (Set.Icc 0 1) ∧
    (∀ x ∈ Set.Icc (0 : Fin d → ℝ) 1, ∀ y ∈ Set.Icc (0 : Fin d → ℝ) 1,
      nnorm (circMap d F x - circMap d F y) ≤ L * nnorm (x - y)) ∧
    ∃ pts : List (List ℚ), pack (lenList (lenList ratCode) pts) = t ∧
      (∀ v ∈ pts, v.length = d) ∧
      letI := Classical.decEq (Fin d → ℝ)
      (((pts.map (ratVec d)).toFinset.card : ℕ) : ℝ) ≤ (d : ℝ) ^ C ∧
      IsFixedSet (Set.Icc 0 1) (circMap d F) ((d : ℝ) ^ (-c)) (pts.map (ratVec d)).toFinset

end CEPolytopeHard.Supplement


