-- Prove2me | Definitions.Def_NovyPQZK_Main_OWP
-- name    : NovyPQZK_Main_OWP
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-11T05:35:50.046994+00:00
-- url     : https://prove2.me/theorems/7282b510-1bee-41b7-a410-e486d6e33b1a
-- title:
--   Post-quantum one-way permutations (Definition 13, with computability)
-- statement:
--   A **permutation family** $\pi = \{\pi_n\}$ has $\pi_n$ a permutation of $\{0,1\}^n$. It is a **post-quantum one-way permutation** if $\pi_n$ is computable in deterministic polynomial time and for every QPT algorithm $A = \{A_n\}$ (with quantum advice)
--
--   $$\Pr_{x\in_R\{0,1\}^n}\big[\pi_n(A_n(\pi_n(x))) = \pi_n(x)\big]\le\mathrm{negl}(n).$$
--
--   $A_n$ receives $\pi_n(x)$ as its classical input; its output is the outcome of its measurement, read as an $n$-bit string.
--
--   **Formalization Note** Computability of $\pi$ is not in the printed Definition 13 (finding I1): without it the hypothesis "post-quantum one-way permutations exist" holds unconditionally and novy is not a PPT scheme.
-- source:
--   Dupuis, Ligez, Medhioub, Salvail, Thibodeau, Post-Quantum Perfect Zero-Knowledge Arguments for NP From Any One-Way Permutation, arXiv:2610.33185 (sha256 857d8563…3257f), §3.4 p. 27, Definition 13 (computability: finding I1)

import Mathlib
import Definitions.Def_CompNonlocal_Negligible
import Definitions.Def_NovyPQZK_Main_Quantum

namespace NovyPQZK.Main

/-!
Dupuis, Ligez, Medhioub, Salvail, Thibodeau, arXiv:2610.33185 (sha256 857d8563…3257f), §3.4,
p. 27, Definition 13: post-quantum one-way permutations.

Reading (finding I1): Definition 13 does not say that `π_n` is efficiently computable; the
definition below requires it (one polynomial-time machine computing `π_n` on every input of length
`n`), as the novy scheme (Definition 4: all protocols PPT) and the inverter's use of `π_n` (p. 42)
need. Reading (finding I3): the inverter `A` is QPT in the sense of `IsQPT` (non-uniform, with
quantum advice).
-/

open QAlgorithms

/-- A family of permutations `π_n` of `{0,1}^n`. -/
abbrev PermFamily := (n : ℕ) → Equiv.Perm (Qubits n)

/-- A string read as an `n`-bit string (missing bits read `0`, extra bits ignored). -/
def qubitsOfStr (n : ℕ) (s : Bits) : Qubits n := fun i => s.getD i false

/-- `π_n` applied to a string of length `n`, as a string. -/
def PermFamily.applyStr (π : PermFamily) (s : Bits) : Bits :=
  List.ofFn (π s.length (fun i => s.get i))

/-- `π` is computable in deterministic polynomial time. -/
def PermFamily.IsPolyTime (π : PermFamily) : Prop := PolyTimeFn π.applyStr

/-- `Pr_{x ∈_R {0,1}^n}[π_n(A_n(π_n(x))) = π_n(x)]`: `A_n` receives `π_n(x)` (at its step `0`) and
its output is the outcome of the measurement at that step, read as an `n`-bit string. -/
noncomputable def invertProb (π : PermFamily) (A : QStrategy) (n : ℕ) : ℝ :=
  avgOver (Qubits n) fun x =>
    ∑ o : A.Outs 1,
      let os := QStrategy.outList o
      if π n (qubitsOfStr n (os.getD 0 [])) = π n x then
        (A.run (msgFor (List.ofFn (π n x)) (fun _ => [])) (zeroDM A.inQ) os).trace.re
      else 0

/-- Definition 13 (p. 27), with the computability reading: `π` is a post-quantum one-way
permutation. -/
def IsPQOneWayPermutation (π : PermFamily) : Prop :=
  π.IsPolyTime ∧
    ∀ A : ℕ → QStrategy, IsQPT A →
      ∃ μ : ℕ → ℝ, CompNonlocal.Negligible μ ∧ ∀ n, invertProb π (A n) n ≤ μ n

end NovyPQZK.Main


