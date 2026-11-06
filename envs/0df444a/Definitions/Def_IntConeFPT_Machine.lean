-- Prove2me | Definitions.Def_IntConeFPT_Machine
-- name    : IntConeFPT_Machine
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T00:39:20.99019+00:00
-- url     : https://prove2.me/theorems/7db2f708-7749-4fe0-84d7-8f76d32e5967
-- title:
--   Deterministic Turing machines over $\{0,1,2,3\}$, step-bounded runs, and the time bounds $2^{\tau\log(\tau+1)2^{Cd}}L^C$ and $2^{Cd^2\log(d+1)}L^C$
-- statement:
--   An **algorithm** is a deterministic multi-stack Turing machine $\mathcal M$ (Mathlib's `Turing.TM2ComputableAux`) whose input and output are words over the alphabet $\{0,1,2,3\}$: the symbols $0,1$ are bits, $2$ separates numerator and denominator of a rational number and $3$ separates items.
--
--   For words $w,w'$ and a real $T$, **$\mathcal M$ runs within $T$ steps on $w$ with output $w'$** if, for some natural number $m\le T$, the machine started on $w$ halts after at most $m$ steps with exactly $w'$ on its output stack.
--
--   Two step bounds appear in the paper's results. For a natural number $C$, a number of types $\tau$, an integer dimension $d$ and an input length $L$,
--   $$
--   \mathrm{fpt}_C(\tau,d,L)=2^{\tau\log_2(\tau+1)\,2^{Cd}}\cdot L^{C},\qquad
--   \mathrm{orc}_C(d,L)=2^{C\,d^2\log_2(d+1)}\cdot L^{C}.
--   $$
--   They are the readings of $2^{\tau\log(\tau+1)2^{O(d)}}\cdot|I|^{O(1)}$ (Theorem 1, Lemma 13, Proposition 14) and of $2^{O(d^2\log(d+1))}\cdot(|I|+\mathrm{enc}(\cdot))^{O(1)}$ (Lemmas 5, 6, 12, 29).
--
--   Every algorithmic statement of the mission has the form: there are a constant $C$ and a machine $\mathcal M$ such that for every admissible input there is a correct output which $\mathcal M$ produces within the stated bound.
--
--   **Formalization Note** The paper names no machine model; it measures time against the binary input length $|I|$, so the reading is the deterministic Turing model. Mathlib's `TM2ComputableInTime` is not used because its time bound depends on the input length only, while these bounds also depend on $d$ and $\tau$.
-- source:
--   Jansen–Ohnesorge–Schumacher, A Constructive FPT Algorithm for Integer Cone Optimization with Convex Costs, arXiv:2609.31328 (preprint, sha256 9e28aed8…bc08a), Theorem 1, p.4; Lemmas 5, 6 (p.9), 12 (p.14), 13 (p.15), 29 (p.33), Proposition 14 (p.16), (2.1) (p.6)

import Mathlib
import Definitions.Def_OnlineCRS_Combine_Sym

namespace IntConeFPT

open OnlineCRS.Combine

/-- **Deterministic algorithms: Mathlib's multi-stack Turing machines over `Fin 4`.**
Jansen–Ohnesorge–Schumacher, *A Constructive FPT Algorithm for Integer Cone Optimization with
Convex Costs*, arXiv:2609.31328 (preprint), Theorem 1, p.4 ("can be solved deterministically in
time …") and every algorithmic lemma (Lemmas 5, 6, 12, 13, 29, Proposition 14, (2.1)).

An algorithm is a `Turing.TM2ComputableAux Sym Sym`: a finite multi-stack Turing machine whose
input and output stacks are written over the four-letter alphabet `Sym = Fin 4` (bits `0`, `1`;
`2` separates numerator and denominator of a rational; `3` separates items).

**Formalization Note.** The paper names no machine model; it measures time against the total
binary input length |I| (abstract; p.4), so the reading is Mathlib's deterministic Turing model
(TM2). A polynomial RAM-to-TM overhead is absorbed by the `O(·)` exponents. -/
abbrev Machine : Type 1 := Turing.TM2ComputableAux Sym Sym

/-- **`M` halts on input `inp` with output `out` within `T` steps.**
Jansen–Ohnesorge–Schumacher, arXiv:2609.31328 (preprint), Theorem 1, p.4: "in time
2^{τ log(τ+1) 2^{O(d)}} · |I|^{O(1)}".

`RunsWithin M inp out T` holds iff for some natural number `m ≤ T`, the machine `M`, started on
the encoded input `inp`, halts after at most `m` steps with exactly `out` on its output stack.
This is Mathlib's `Turing.TM2OutputsInTime`, with the alphabets translated as in
`Turing.TM2ComputableInTime.outputsFun`.

**Formalization Note.** Each algorithmic statement of the mission has the shape
`∃ C, ∃ M : Machine, ∀ input, hypotheses → ∃ output, spec ∧ RunsWithin M (enc input) (enc output) bound`:
the constant `C` and the machine come before every input (the `O(·)` constants are absolute), and
correctness and the time bound are required on the inputs the paper speaks about only (a promise
problem). Mathlib's `TM2ComputableInTime` is not used because its time bound is a function of the
input length alone, while the bounds here also depend on `d` and `τ`. The bound `T` is real so that
`log` and real exponents can be written as in the paper. -/
def RunsWithin (M : Machine) (inp out : List Sym) (T : ℝ) : Prop :=
  ∃ m : ℕ, (m : ℝ) ≤ T ∧
    Nonempty (Turing.TM2OutputsInTime M.tm (inp.map M.inputAlphabet.invFun)
      (some (out.map M.outputAlphabet.invFun)) m)

/-- **The FPT time bound `2^{τ log(τ+1) 2^{C d}} · L^C`.**
Jansen–Ohnesorge–Schumacher, arXiv:2609.31328 (preprint), Theorem 1, p.4; Lemma 13, p.15;
Proposition 14, p.16: "2^{τ log(τ+1) 2^{O(d)}} · |I|^{O(1)}".

**Formalization Note.** `O(·)` is read as one absolute constant `C : ℕ` (quantified before the
machine): for `d ≥ 1`, `c₁ d + c₀ ≤ (c₁ + c₀) d`, so `2^{O(d)} ≤ 2^{C d}` and `|I|^{O(1)} ≤ |I|^C`.
The logarithm is to base 2 (`Real.logb 2`); another base only changes `C`. `L` is the length of
the encoded input. -/
noncomputable def fptBound (C τ d L : ℕ) : ℝ :=
  (2 : ℝ) ^ ((τ : ℝ) * Real.logb 2 ((τ : ℝ) + 1) * (2 : ℝ) ^ ((C : ℝ) * d)) * (L : ℝ) ^ C

/-- **The oracle time bound `2^{C d² log(d+1)} · L^C`.**
Jansen–Ohnesorge–Schumacher, arXiv:2609.31328 (preprint), Lemma 5, p.9; Lemma 6, p.9; Lemma 12,
p.14; Lemma 29, p.33: "2^{O(d² log(d+1))} · (|I| + enc(·))^{O(1)}".

**Formalization Note.** As for `fptBound`: one absolute constant `C`, logarithm to base 2, and `L`
the length of the encoded input (instance followed by the query), which is `|I| + enc(query)` up
to the separators. -/
noncomputable def oracleBound (C d L : ℕ) : ℝ :=
  (2 : ℝ) ^ ((C : ℝ) * (d : ℝ) ^ 2 * Real.logb 2 ((d : ℝ) + 1)) * (L : ℝ) ^ C

end IntConeFPT


