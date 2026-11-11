-- Prove2me | Definitions.Def_DetSpectralSparsify_Dense_Machine
-- name    : DetSpectralSparsify_Dense_Machine
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-11T03:59:04.508225+00:00
-- url     : https://prove2.me/theorems/29a401b6-f7f1-4610-9585-87c69bcf6efc
-- title:
--   Closed real RAM, input/output layouts, achievable matrix multiplication exponents, the sequence ϕ_n
-- statement:
--   The paper states running times without naming a machine model. They are read on the following **real RAM**.
--
--   1. A **program** is a finite list of instructions fixed before the input. The memory consists of natural-number cells and real cells, both addressed by naturals and zero outside the input. Each instruction costs one step: natural constant, copy, $+$, truncated $-$, indirect load and store, comparison branch; real copy, $+$, $-$, $\times$, $\div$, $\sqrt{\ }$, the cast $\mathbb N\to\mathbb R$, indirect load and store, comparison branch; unconditional jump; `halt`. There is **no** natural multiplication or division, no real-to-natural cast or floor, no real constant (rationals are formed from natural constants), and no graph, matrix, eigenvalue or oracle primitive. Division by zero, the square root of a negative number and running off the program **get stuck**, so a stuck run never halts.
--   2. A run **halts in $T$ steps** if after exactly $T$ successful steps it reaches a `halt` instruction. A run respects the **word bound** with exponent $K$ and base $B$ if during its first $T$ steps every natural cell holds at most $(B+T)^K$, i.e. natural words have $O(\log(B+T))$ bits; $K$ is fixed with the program.
--   3. **Graph input** (`graphInput`): natural cells hold the natural parameters, then $n$, $m$ and the endpoint pairs; real cells hold the real parameters (for instance $\varepsilon$), then the weights. **Graph output** (`decodeGraph`): natural cell $0$ holds the number $k$ of edges, edge $j$ has endpoints in natural cells $1+2j$, $2+2j$ and weight in real cell $j$; an endpoint $\ge n$ makes the output malformed. Analogous layouts encode a regularized graph with its fibers and a polynomial by its coefficients.
--   4. An exponent $\alpha$ is **achievable** if one program multiplies any two real $n\times n$ matrices within $C(n+1)^\alpha$ steps. Schoolbook multiplication shows that $\alpha=3$ is achievable. Bounds stated with $n^\omega$ are read as holding for every achievable $\alpha>2$, as prescribed in the BRIEF.
--   5. The expander-decomposition conductance $\phi_n=\log^{-9-o(1)}n$ is a sequence $\phi:\mathbb N\to(0,1]$ with
--   $$\phi(n)^{-1}=(\log n)^{9+h(n)}\quad(n\ge 3),\qquad h(n)\to0 .$$
--   6. `chebOnInterval a d c` is the polynomial $\sum_{j\le d}c_jT_j\big(\tfrac{c_0-x}{\rho}\big)$ with $c_0=\tfrac{2+a}{2}$, $\rho=\tfrac{2-a}{2}$ (Appendix A). Lemma 8 uses the same closed RAM for node generation and coefficient computation; it has no separate straight-line language with arbitrary real constants.
--
--   **Formalization Note** The instruction set is closed: an algorithm can only be charged for work the machine actually does, and none of the excluded operations (unbounded integer multiplication, real floors, free real constants) is available to hide computation in a single step.
-- source:
--   Trevor Vaughn, Jason Li, Deterministic Spectral Sparsification in Almost-Linear Time for Dense Graphs, STOC 2027 submission #370 (October 2026), source.pdf SHA-256 b88d92728f937730b7e9664f482778048c0b667d4376e0488686c9708e5d8467, p.5 (ω, Definition 2), p.13 (n^ω usage), p.22 (ϕ_n, Theorem 13), p.32 (Appendix A, Chebyshev coefficients); the machine model itself is a declared reading (the paper names none)

import Definitions.Def_DetSpectralSparsify_Dense_Multigraph

set_option autoImplicit false

namespace DetSpectralSparsify.Dense

/-! ## A closed real RAM

The paper names no machine model. Running times are read on the following unit-cost real RAM:
a fixed finite program, natural-number cells and real cells addressed by naturals, all zero
outside the input. Natural arithmetic is `+` and truncated `-` only (no multiplication, division
or bit operations on naturals); real arithmetic is `+ - × ÷ √`, the cast `ℕ → ℝ`, and comparison
branches. There is no real-to-natural cast, no floor, no real constant (rationals are built from
natural constants by the cast and `÷`), and no graph, matrix or oracle primitive. Division by
zero, the square root of a negative number and running off the program get stuck. -/

/-- One instruction of the real RAM. Arguments are cell addresses unless noted. -/
inductive Instr where
  /-- `nat[dst] := k` (the constant `k` is part of the program). -/
  | natConst (dst k : ℕ)
  | natCopy (dst src : ℕ)
  | natAdd (dst a b : ℕ)
  /-- Truncated subtraction. -/
  | natSub (dst a b : ℕ)
  /-- `nat[dst] := nat[nat[addr]]`. -/
  | natLoad (dst addr : ℕ)
  /-- `nat[nat[addr]] := nat[src]`. -/
  | natStore (addr src : ℕ)
  /-- If `nat[a] < nat[b]` jump to instruction `target`, else continue. -/
  | natBranchLt (a b target : ℕ)
  | realCopy (dst src : ℕ)
  | realAdd (dst a b : ℕ)
  | realSub (dst a b : ℕ)
  | realMul (dst a b : ℕ)
  /-- Gets stuck if `real[b] = 0`. -/
  | realDiv (dst a b : ℕ)
  /-- Gets stuck if `real[a] < 0`. -/
  | realSqrt (dst a : ℕ)
  /-- `real[dst] := (nat[a] : ℝ)`. -/
  | realOfNat (dst a : ℕ)
  /-- `real[dst] := real[nat[addr]]`. -/
  | realLoad (dst addr : ℕ)
  /-- `real[nat[addr]] := real[src]`. -/
  | realStore (addr src : ℕ)
  /-- If `real[a] < real[b]` jump to instruction `target`, else continue. -/
  | realBranchLt (a b target : ℕ)
  | jump (target : ℕ)
  | halt

/-- A program: a finite list of instructions, fixed before any input. -/
abbrev Program := List Instr

/-- Machine state: program counter, natural cells, real cells. -/
structure State where
  pc : ℕ
  nat : ℕ → ℕ
  real : ℕ → ℝ

/-- One step. `none` means the machine cannot step: it is at `halt`, has run off the program,
or would divide by zero or take the square root of a negative number. -/
noncomputable def step (P : Program) (s : State) : Option State :=
  match P[s.pc]? with
  | none => none
  | some i =>
    match i with
    | .natConst d k => some { s with pc := s.pc + 1, nat := Function.update s.nat d k }
    | .natCopy d a => some { s with pc := s.pc + 1, nat := Function.update s.nat d (s.nat a) }
    | .natAdd d a b =>
        some { s with pc := s.pc + 1, nat := Function.update s.nat d (s.nat a + s.nat b) }
    | .natSub d a b =>
        some { s with pc := s.pc + 1, nat := Function.update s.nat d (s.nat a - s.nat b) }
    | .natLoad d a =>
        some { s with pc := s.pc + 1, nat := Function.update s.nat d (s.nat (s.nat a)) }
    | .natStore a v =>
        some { s with pc := s.pc + 1, nat := Function.update s.nat (s.nat a) (s.nat v) }
    | .natBranchLt a b t => some { s with pc := if s.nat a < s.nat b then t else s.pc + 1 }
    | .realCopy d a => some { s with pc := s.pc + 1, real := Function.update s.real d (s.real a) }
    | .realAdd d a b =>
        some { s with pc := s.pc + 1, real := Function.update s.real d (s.real a + s.real b) }
    | .realSub d a b =>
        some { s with pc := s.pc + 1, real := Function.update s.real d (s.real a - s.real b) }
    | .realMul d a b =>
        some { s with pc := s.pc + 1, real := Function.update s.real d (s.real a * s.real b) }
    | .realDiv d a b =>
        if s.real b = 0 then none
        else some { s with pc := s.pc + 1, real := Function.update s.real d (s.real a / s.real b) }
    | .realSqrt d a =>
        if s.real a < 0 then none
        else some { s with pc := s.pc + 1, real := Function.update s.real d (Real.sqrt (s.real a)) }
    | .realOfNat d a =>
        some { s with pc := s.pc + 1, real := Function.update s.real d (s.nat a : ℝ) }
    | .realLoad d a =>
        some { s with pc := s.pc + 1, real := Function.update s.real d (s.real (s.nat a)) }
    | .realStore a v =>
        some { s with pc := s.pc + 1, real := Function.update s.real (s.nat a) (s.real v) }
    | .realBranchLt a b t => some { s with pc := if s.real a < s.real b then t else s.pc + 1 }
    | .jump t => some { s with pc := t }
    | .halt => none

/-- `exec P t s`: the state after exactly `t` steps from `s`, if every step succeeds. -/
noncomputable def exec (P : Program) : ℕ → State → Option State
  | 0, s => some s
  | t + 1, s => (step P s).bind (exec P t)

/-- The run from `s` reaches, after exactly `T` steps, the state `s'`, which sits at a `halt`
instruction. (`halt` itself is not counted.) -/
def HaltsIn (P : Program) (s : State) (T : ℕ) (s' : State) : Prop :=
  exec P T s = some s' ∧ P[s'.pc]? = some Instr.halt

/-- Word bound: during the first `T` steps every natural cell holds at most `(base + T)^K`,
i.e. natural words have `O(log (base + T))` bits, with the exponent `K` fixed with the program. -/
def WordBounded (P : Program) (K base : ℕ) (s : State) (T : ℕ) : Prop :=
  ∀ i ≤ T, ∀ s', exec P i s = some s' → ∀ a, s'.nat a ≤ (base + T) ^ K

/-- A halting run of `T` steps from `s` to `s'` that respects the word bound. -/
def RunsWithin (P : Program) (K base : ℕ) (s : State) (T : ℕ) (s' : State) : Prop :=
  HaltsIn P s T s' ∧ WordBounded P K base s T

/-! ## Input and output layouts -/

/-- Initial state holding only parameters: `nat[i] = natParams[i]`, `real[i] = realParams[i]`,
everything else zero. -/
def paramInput (natParams : List ℕ) (realParams : List ℝ) : State where
  pc := 0
  nat := fun a => natParams.getD a 0
  real := fun a => realParams.getD a 0

/-- Initial state for a multigraph `G` on `Fin n` with parameters. With `p` natural and `q` real
parameters: `nat[0..p)` parameters, `nat[p] = n`, `nat[p+1] = m`, `nat[p+2+2e] = src e`,
`nat[p+3+2e] = dst e`; `real[0..q)` parameters, `real[q+e] = w e`. All other cells zero. -/
def graphInput {n : ℕ} (G : Multigraph n) (natParams : List ℕ) (realParams : List ℝ) : State where
  pc := 0
  nat := fun a =>
    if a < natParams.length then natParams.getD a 0
    else
      let b := a - natParams.length
      if b = 0 then n
      else if b = 1 then G.m
      else if h : (b - 2) / 2 < G.m then
        (if (b - 2) % 2 = 0 then (G.src ⟨(b - 2) / 2, h⟩).val else (G.dst ⟨(b - 2) / 2, h⟩).val)
      else 0
  real := fun a =>
    if a < realParams.length then realParams.getD a 0
    else if h : a - realParams.length < G.m then G.w ⟨a - realParams.length, h⟩ else 0

/-- Output graph on `Fin n`: `nat[0] = k` edges; edge `j < k` has endpoints `nat[1+2j]`,
`nat[2+2j]` and weight `real[j]`. A malformed output (an endpoint `≥ n`) decodes to `none`. -/
noncomputable def decodeGraph (n : ℕ) (s : State) : Option (Multigraph n) := by
  classical
  exact if h : ∀ j < s.nat 0, s.nat (1 + 2 * j) < n ∧ s.nat (2 + 2 * j) < n then
    some { m := s.nat 0
           src := fun j => ⟨s.nat (1 + 2 * j.val), (h j.val j.isLt).1⟩
           dst := fun j => ⟨s.nat (2 + 2 * j.val), (h j.val j.isLt).2⟩
           w := fun j => s.real j.val }
  else none

/-- Output of degree regularization (Lemma 10): `nat[0] = k` edges and `nat[1] = N` vertices of
`G°`; the fiber of `x < N` is `nat[2+x]` (a vertex of `G`); edge `j < k` has endpoints
`nat[2+N+2j]`, `nat[3+N+2j]` and weight `real[j]`. Malformed outputs decode to `none`. -/
noncomputable def decodeRegularized (n : ℕ) (s : State) :
    Option (Σ N : ℕ, Multigraph N × (Fin N → Fin n)) := by
  classical
  let N := s.nat 1
  exact if h : (∀ x < N, s.nat (2 + x) < n) ∧
      ∀ j < s.nat 0, s.nat (2 + N + 2 * j) < N ∧ s.nat (3 + N + 2 * j) < N then
    some ⟨N,
      { m := s.nat 0
        src := fun j => ⟨s.nat (2 + N + 2 * j.val), (h.2 j.val j.isLt).1⟩
        dst := fun j => ⟨s.nat (3 + N + 2 * j.val), (h.2 j.val j.isLt).2⟩
        w := fun j => s.real j.val },
      fun x => ⟨s.nat (2 + x.val), h.1 x.val x.isLt⟩⟩
  else none

/-- Polynomial output: `nat[0] = D`, coefficients `real[0], …, real[D]` in the monomial basis. -/
noncomputable def decodePoly (s : State) : Polynomial ℝ :=
  ∑ i ∈ Finset.range (s.nat 0 + 1), Polynomial.C (s.real i) * Polynomial.X ^ i

/-! ## Matrix multiplication exponents -/

/-- Input for multiplying `A B : ℝ^{n×n}`: `nat[0] = n`, `A i j` at `real[i n + j]`,
`B i j` at `real[n² + i n + j]`. -/
def matInput (n : ℕ) (A B : Matrix (Fin n) (Fin n) ℝ) : State where
  pc := 0
  nat := fun a => if a = 0 then n else 0
  real := fun a =>
    if h : a < n * n then A ⟨a / n, Nat.div_lt_of_lt_mul h⟩ ⟨a % n, Nat.mod_lt _ (by
      rcases Nat.eq_zero_or_pos n with hn | hn
      · subst hn; simp at h
      · exact hn)⟩
    else if h' : a - n * n < n * n then
      B ⟨(a - n * n) / n, Nat.div_lt_of_lt_mul h'⟩ ⟨(a - n * n) % n, Nat.mod_lt _ (by
        rcases Nat.eq_zero_or_pos n with hn | hn
        · subst hn; simp at h'
        · exact hn)⟩
    else 0

/-- `α` is an achievable matrix multiplication exponent: one program multiplies any two real
`n × n` matrices (product at `real[2n² + i n + j]`) within `C (n + 1)^α` steps. This spells out
the convention behind `n^ω` (the paper's `ω` is an infimum and need not be attained). -/
def Achievable (α : ℝ) : Prop :=
  ∃ (P : Program) (K : ℕ) (C : ℝ), ∀ (n : ℕ) (A B : Matrix (Fin n) (Fin n) ℝ),
    ∃ T s', RunsWithin P K (2 + n) (matInput n A B) T s' ∧
      (T : ℝ) ≤ C * ((n : ℝ) + 1) ^ α ∧
      ∀ i j : Fin n, s'.real (2 * n * n + i.val * n + j.val) = (A * B) i j

/-! ## The expander-decomposition conductance `ϕ_n = log^{-9-o(1)} n` -/

/-- `ϕ : ℕ → (0, 1]` with `ϕ(n)⁻¹ = (log n)^{9 + h(n)}` for `n ≥ 3`, where `h(n) → 0`. -/
def IsPhiSequence (ϕ h : ℕ → ℝ) : Prop :=
  (∀ n, 0 < ϕ n ∧ ϕ n ≤ 1) ∧ Filter.Tendsto h Filter.atTop (nhds 0) ∧
    ∀ n : ℕ, 3 ≤ n → (ϕ n)⁻¹ = Real.log n ^ (9 + h n)

/-- A function tending to `0` (an `o(1)` exponent). -/
def Vanishing (g : ℕ → ℝ) : Prop := Filter.Tendsto g Filter.atTop (nhds 0)

/-! ## Chebyshev coefficient output (Lemma 8) -/

/-- The polynomial `∑_{j ≤ d} c_j T_j((c₀ - x)/ρ)` with `c₀ = (2+a)/2`, `ρ = (2-a)/2`, i.e. the
polynomial with Chebyshev coefficients `c_0, …, c_d` on the interval `[a, 2]` (Appendix A). -/
noncomputable def chebOnInterval (a : ℝ) (d : ℕ) (c : ℕ → ℝ) : Polynomial ℝ :=
  ∑ j ∈ Finset.range (d + 1), Polynomial.C (c j) *
    (Polynomial.Chebyshev.T ℝ (j : ℤ)).comp
      (Polynomial.C ((2 + a) / (2 - a)) - Polynomial.C (2 / (2 - a)) * Polynomial.X)

end DetSpectralSparsify.Dense


