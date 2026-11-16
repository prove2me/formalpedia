-- Prove2me | Definitions.Def_ArbLindbladLearn_Supplement_initStateCand
-- name    : ArbLindbladLearn_Supplement_initStateCand
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T03:14:54.739069+00:00
-- url     : https://prove2.me/theorems/41e9ac22-2337-4d5f-9ab3-7fbcacbc6fc5
-- title:
--   Input of the coefficient learner: $(n,\Lambda,\varepsilon,\delta)$ and candidate supports
-- statement:
--   Algorithm 2 takes as input the accuracy $\varepsilon$, the failure probability $\delta$, the dynamical-strength bound $\Lambda$ and candidate supports $\hat{\mathcal S}_H$ and $\hat{\mathcal S}_D$. This definition is the corresponding initial configuration of the learner's machine.
--
--   As in the published input of Corollary 4.7, the real cells $0,1,2$ hold $\Lambda,\varepsilon,\delta$ and integer cell $0$ holds $n$. In addition, integer cells $1$ and $2$ hold the numbers $|S_H|$ and $|S_D|$ of candidates, and from integer cell $3$ on the machine finds the labels of $S_H$ ($n$ cells each, letters $0=I,1=X,2=Y,3=Z$), followed by the pairs of $S_D$ ($2n$ cells each, first label first). All other cells, registers and pointers are $0$; nothing has been output, no experiment has been made and no work has been done.
--
--   The unknown Lindbladian is not part of the input: it is accessed only through experiments.
--
--   **Formalization Note** The candidate supports are passed as lists; Theorem 4.6 requires them to be duplicate-free. The letters are written so that the published `parseLabel` reads the labels back.
-- source:
--   Chen, Yu, Learning Arbitrary Lindbladians from Time Evolution, arXiv:2607.28610 (sha256 46c27db5…), Algorithm 2 (input), p.31; Theorem 4.6, p.32

import Mathlib
import Definitions.Def_ArbLindbladLearn_MState
import Definitions.Def_LindbladTolerant_Testing_lindblad_model

set_option autoImplicit false
open scoped ComplexOrder BigOperators Matrix ENNReal NNReal Kronecker
noncomputable section

namespace ArbLindbladLearn.Supplement

open LindbladTolerant.Testing
open ArbLindbladLearn

/-- The letter (`0 = I, 1 = X, 2 = Y, 3 = Z`) of label `a` at qubit `i`, as an integer; `0` for
`i ≥ n`. -/
def letterVal (n : ℕ) (a : Pauli n) (i : ℕ) : ℤ :=
  if h : i < n then ((a ⟨i, h⟩ : Fin 4) : ℕ) else 0

/-- Integer cell `3 + w` of the candidate input: the `SH` labels (`n` cells each), then the
`SD` pairs (`2n` cells each, first label first), then `0`. -/
def candCell (n : ℕ) (SH : List (Pauli n)) (SD : List (Pauli n × Pauli n)) (w : ℕ) : ℤ :=
  if w < SH.length * n then letterVal n (SH.getD (w / n) 0) (w % n)
  else
    let w' := w - SH.length * n
    if w' < SD.length * (2 * n) then
      let pr := SD.getD (w' / (2 * n)) (0, 0)
      let r := w' % (2 * n)
      if r < n then letterVal n pr.1 r else letterVal n pr.2 (r - n)
    else 0

/-- The input of the coefficient learner of Theorem 4.6 (Chen–Yu, *Learning Arbitrary Lindbladians from Time Evolution*, arXiv:2607.28610 (sha256 46c27db5…), p.32;
Algorithm 2, p.31: "Input: accuracy ε; failure probability δ; dynamical strength bound Λ; candidate
supports Ŝ_H and Ŝ_D"): as the published `initState n Λ ε δ` (real cells `0, 1, 2` hold `Λ, ε, δ`;
integer cell `0` holds `n`), plus the candidate supports given as lists: integer cell `1` holds
`|SH|`, cell `2` holds `|SD|`, and from cell `3` on the `SH` labels (`n` cells each, letters
`0 = I, 1 = X, 2 = Y, 3 = Z` as the published `parseLabel` reads them) followed by the `SD` pairs
(`2n` cells each). Every other cell, register and pointer is `0`; no output, no durations, no work.

**Formalization Note** The unknown Lindbladian is not in the input: it enters only through the
experiments. -/
def initStateCand (n : ℕ) (Λ ε δ : ℝ) (SH : List (Pauli n)) (SD : List (Pauli n × Pauli n)) :
    MState :=
  ⟨⟨0, fun _ => 0, fun _ => 0,
      fun z => if z = 0 then Λ else if z = 1 then ε else if z = 2 then δ else 0⟩,
    fun z => if z = 0 then (n : ℤ) else if z = 1 then (SH.length : ℤ)
      else if z = 2 then (SD.length : ℤ)
      else if 3 ≤ z then candCell n SH SD (z - 3).toNat else 0,
    none, [], 0⟩

end ArbLindbladLearn.Supplement


