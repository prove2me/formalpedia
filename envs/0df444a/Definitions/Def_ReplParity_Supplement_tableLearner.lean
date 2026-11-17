-- Prove2me | Definitions.Def_ReplParity_Supplement_tableLearner
-- name    : ReplParity_Supplement_tableLearner
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T14:58:46.964908+00:00
-- url     : https://prove2.me/theorems/9dd88895-70fc-4585-a57c-dc0048fc0cd0
-- title:
--   Learners for a finite class given as a list, reading the evaluation table
-- statement:
--   Let $H$ be given as a list $h_0,\dots,h_{M-1}$ of functions $X\to\{0,1\}$. For a sample $S=((x_1,y_1),\dots,(x_m,y_m))$, the evaluation table is the $m\times M$ array $(h_j(x_i))$. A table learner applies a map $\Phi$ to the table, the labels $(y_i)$ and the seed $r$, and outputs an index $j$ (the hypothesis $h_j$) or $\bot$.
--
--   For the finite-bit clause of Theorem 7.1, $\Phi$ is given by a machine $F$ that reads $(M,\varepsilon,\rho,\text{table},\text{labels},\text{seed})$ in a fixed binary encoding and outputs $\bot$ or an index; an index $j\ge M$ is read as $\bot$.
--
--   **Formalization Note** Building the table costs $M\cdot m$ evaluations, so a machine polynomial-time in its input gives running time polynomial in $M$, $m$, the evaluation time and the encoding lengths of $\varepsilon,\rho$.
-- source:
--   Shen, Zhong, Replicable Parity Learning: Cubic Sample Complexity and a Geometric Characterization, STOC 2027 submission (manuscript sha256 40424491d00eef39c790dd41b7557e0ffdf9de2d14d95ddcd611aeacb0f77a50), Theorem 7.1, p.28 (PDF p.30), last sentence

import Mathlib
import Definitions.Def_ReplParity_encIn

set_option autoImplicit false

namespace ReplParity

namespace Supplement

/-- The `m × M` evaluation table `(h_j(x_i))` of the list `h₀, …, h_{M−1}` on the sample points. -/
def evalTable {X : Type*} {M m : ℕ} (h : Fin M → X → ZMod 2) (S : Fin m → X × ZMod 2) :
    Fin m → Fin M → ZMod 2 :=
  fun i j => h j (S i).1

/-- The labels `(y_i)` of a sample. -/
def sampleLabels {X : Type*} {m : ℕ} (S : Fin m → X × ZMod 2) : Fin m → ZMod 2 :=
  fun i => (S i).2

/-- **A learner for a finite class given as a list.** Shen, Zhong, *Replicable Parity Learning:
Cubic Sample Complexity and a Geometric Characterization*, STOC 2027 submission (manuscript sha256
40424491…), Theorem 7.1, p.28 (PDF p.30): "If H is given as a list of hypotheses that can be
evaluated, the learner has a finite-bit implementation …"

`tableLearner h Φ` reads the sample `S` only through the evaluation table `(h_j(x_i))` and the labels
`(y_i)`, and outputs `Φ(table, labels, r)`: an index `j` (the hypothesis `h_j`) or `⊥` (`none`).

**Formalization Note.** Outputs are compared as indices in `Option (Fin M)`; for an injective list
this is comparison of the hypotheses themselves. -/
def tableLearner {X Ω : Type*} {M m : ℕ} (h : Fin M → X → ZMod 2)
    (Φ : (Fin m → Fin M → ZMod 2) → (Fin m → ZMod 2) → Ω → Option (Fin M)) :
    (Fin m → X × ZMod 2) → Ω → Option (Fin M) :=
  fun S r => Φ (evalTable h S) (sampleLabels S) r

/-- Machine input for the finite-class learner: `(M, ε, ρ, table rows, labels, seed bits)`. -/
abbrev TInput : Type := ℕ × ℚ × ℚ × List (List Bool) × List Bool × List Bool

/-- The fixed binary encoding of a `TInput` (alphabet `Option Bool`, `none` a separator): `M` in
binary, `ε`, `ρ` (base mission's `encRat`), the table row by row (each row's bits and a separator,
then a separator), the label bits, the seed bits. -/
def encTIn : TInput → List (Option Bool)
  | (M, ε, ρ, rows, ys, r) =>
      encNatSym M ++ [none] ++ encRat ε ++ [none] ++ encRat ρ ++ [none] ++
        (rows.map (fun s => s.map some ++ [none])).flatten ++ [none] ++ ys.map some ++ [none] ++
          r.map some

/-- The machine's output: `[none]` for `⊥`, and `some true` followed by `j` in binary for the index
`j`. -/
def encIdx : Option ℕ → List (Option Bool)
  | none => [none]
  | some j => some true :: encNatSym j

/-- One run of a finite-class learner machine `F` on the table and labels of a sample with seed
`r`. An index `j ≥ M` is read as `⊥`. -/
def runTable (F : TInput → Option ℕ) (M : ℕ) (ε ρ : ℚ) {m R : ℕ}
    (tab : Fin m → Fin M → ZMod 2) (ys : Fin m → ZMod 2) (r : Fin R → Bool) : Option (Fin M) :=
  (F (M, ε, ρ, List.ofFn (fun i => List.ofFn (fun j => decide (tab i j = 1))),
      List.ofFn (fun i => decide (ys i = 1)), List.ofFn r)).bind
    (fun j => if hj : j < M then some ⟨j, hj⟩ else none)

end Supplement

end ReplParity


