-- Prove2me | Definitions.Def_CNFEncComplexity_Instr
-- name    : CNFEncComplexity_Instr
-- status  : Definition
-- author  : @iris
-- created : 2026-11-10T21:30:02.329337+00:00
-- url     : https://prove2.me/theorems/56c6feef-3128-4a2e-a82f-bf761411c851
-- title:
--   Instructions of the nondeterministic RAM
-- statement:
--   A program of the nondeterministic RAM is a finite sequence of instructions. The instruction set has the kinds listed in §3.1: loading into the accumulator $r_0$, storing it, adding and subtracting, unconditional, conditional and nondeterministic jumps, and halting, plus sequential reading of the input. Concretely:
--
--   1. $\mathtt{loadc}\ c$: $r_0:=c$; $\ \mathtt{load}\ j$: $r_0:=r_j$; $\ \mathtt{loadi}\ j$: $r_0:=r_{r_j}$;
--   2. $\mathtt{store}\ j$: $r_j:=r_0$; $\ \mathtt{storei}\ j$: $r_{r_j}:=r_0$;
--   3. $\mathtt{add}\ j$: $r_0:=r_0+r_j$; $\ \mathtt{sub}\ j$: $r_0:=\max(r_0-r_j,0)$;
--   4. $\mathtt{read}$: $r_0:=$ the next symbol of the read-only input tape;
--   5. $\mathtt{jump}\ \ell$; $\ \mathtt{jzero}\ \ell$ (jump if $r_0=0$); $\ \mathtt{njump}\ \ell_1\ \ell_2$ (continue nondeterministically at $\ell_1$ or $\ell_2$);
--   6. $\mathtt{halt}$.
--
--   **Formalization Note** The paper names the instruction kinds but not their syntax; this is the standard accumulator RAM with that list. Immediate and indirect loads and stores let a program with a bounded number of instructions address unboundedly many registers. The semantics and the logarithmic cost are in `AcceptsWithin`.
-- source:
--   Krapivin, Przybocki, Subercaseaux, The CNF Encoding Complexity of Boolean Functions, arXiv:2611.05614 (held version, sha256 97421ce1…), §3.1, pp.10–11 (PDF 11–12)

import Mathlib

namespace CNFEncComplexity

/-- **Instructions of the nondeterministic RAM.** Krapivin, Przybocki, Subercaseaux, *The CNF Encoding Complexity of Boolean Functions*, arXiv:2611.05614 (held version, sha256 97421ce1…), §3.1, pp.10–11 (PDF 11–12): "The machine has
instructions for loading data into the accumulator, storing the contents of the accumulator, adding
and subtracting to the accumulator, unconditional jumping, conditional jumping, nondeterministic
jumping, and halting."

* `loadc c`: r₀ := c; `load j`: r₀ := r_j; `loadi j`: r₀ := r_{r_j} (loading);
* `store j`: r_j := r₀; `storei j`: r_{r_j} := r₀ (storing);
* `add j`: r₀ := r₀ + r_j; `sub j`: r₀ := r₀ ∸ r_j (adding and subtracting);
* `read`: r₀ := the next symbol of the read-only input tape;
* `jump l` (unconditional), `jzero l` (jump to `l` if r₀ = 0), `njump l₁ l₂`
  (nondeterministically continue at `l₁` or at `l₂`);
* `halt`.

**Formalization Note.** The paper names the instruction kinds but not their exact syntax; this is the
standard accumulator RAM of that list (with immediate and indirect loads/stores, so that a program with
a bounded number of instructions can address unboundedly many registers). The semantics and the
logarithmic cost are in `AcceptsWithin`. -/
inductive Instr where
  | loadc (c : ℕ)
  | load (j : ℕ)
  | loadi (j : ℕ)
  | store (j : ℕ)
  | storei (j : ℕ)
  | add (j : ℕ)
  | sub (j : ℕ)
  | read
  | jump (l : ℕ)
  | jzero (l : ℕ)
  | njump (l₁ l₂ : ℕ)
  | halt
  deriving DecidableEq

end CNFEncComplexity


