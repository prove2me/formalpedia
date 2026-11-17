-- Prove2me | Definitions.Def_MinrankTW_Supplement_Circuit
-- name    : MinrankTW_Supplement_Circuit
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T13:03:59.817446+00:00
-- url     : https://prove2.me/theorems/8096d0a0-4240-4eb0-b04a-9d4ea321de85
-- title:
--   Arithmetic circuits sharing $v$ field inputs
-- statement:
--   Let $\mathbb F$ be a field and $v\ge 0$. An **arithmetic circuit** on the shared inputs $x_1,\dots,x_v\in\mathbb F$ is a list of gates, evaluated in order. Each gate computes either
--   $$
--   c=a\,b\qquad\text{or}\qquad c=\lambda a+\mu b+\nu
--   $$
--   with prescribed constants $\lambda,\mu,\nu\in\mathbb F$, where each argument $a,b$ is an input or an earlier gate of the same circuit. The circuit also has a list of **designated outputs**, each an input or a gate of the circuit. An input assignment $x\in\mathbb F^v$ **satisfies** the circuit if every designated output evaluates to $1$.
--
--   Zero coefficients give constant gates and gates with one argument; a circuit may have no, one or several designated outputs.
--
--   **Formalization Note** Arguments are `Arg.input i` or `Arg.gate k`; `Circuit.WellFormed` requires gate arguments of gate $k$ to be gates $j<k$ and gate outputs to be gate indices; outputs are `Arg`s, so an input may be designated directly. The RAM input `circuitsInput e v cs` lists $v$, the number $T$ of circuits and, for each circuit, its gate count, output count, six cells per gate and the output indices.
-- source:
--   Perles–Weinstein, Efficient Algorithms for Minrank and Index Coding for Low-Treewidth Graphs, STOC 2027 submission (manuscript sha256 32a91384…), Theorem 5, p.18

import Mathlib

namespace MinrankTW.Supplement

/-!
# Arithmetic circuits sharing `v` field inputs

Perles–Weinstein, *Efficient Algorithms for Minrank and Index Coding for Low-Treewidth Graphs*,
STOC 2027 submission manuscript (sha256 32a91384…c57991), Theorem 5, p.18: "Let T arithmetic
circuits share v ≥ 1 inputs over F_q. Each circuit has at most g gates of the forms c = ab and
c = λa + µb + ν, with prescribed constants λ, µ, ν ∈ F_q. Arguments are inputs or earlier gates of
that circuit. Designated outputs must equal one."

**Formalization Note**
* An argument is an input `x_i` (`Arg.input i`, `i < v`) or the value of gate `k` of the same
  circuit (`Arg.gate k`). Gates are listed in evaluation order; `WellFormed` requires every gate
  argument of gate `k` to be a gate `j < k`. A designated output is an input or a gate of the
  circuit (`Arg`; a gate output must be a gate index); the proof of Theorem 5 (p.19) tests an
  output `o` through its value row `ρ_o`, which inputs and gates both have.
* `values x` evaluates the gates in order; `Satisfied x` says every designated output has
  value `1`. A circuit may have no, one or several designated outputs (repetitions allowed).
* `circuitsInput e v cs` is the RAM input: `[v, T]` followed, circuit by circuit, by
  `[#gates, #outputs]`, six numbers per gate (`[0, 0, 0, 0, a, b]` for `c = ab`,
  `[1, e λ, e µ, e ν, a, b]` for `c = λa + µb + ν`, an argument coded `2i` for input `i` and
  `2k + 1` for gate `k`), and the codes of the designated outputs (same argument code). Every field is a separate cell, so the
  layout is decodable and its length is linear in the description.
-/

/-- An argument of a gate: an input `x_i` or an earlier gate of the same circuit. -/
inductive Arg (v : ℕ) where
  | input (i : Fin v)
  | gate (k : ℕ)

/-- A gate: `c = a·b` or `c = λa + µb + ν` with prescribed constants. -/
inductive Gate (F : Type*) (v : ℕ) where
  | mul (a b : Arg v)
  | affine (lam mu nu : F) (a b : Arg v)

/-- A circuit: its gates in evaluation order and its designated output gates. -/
structure Circuit (F : Type*) (v : ℕ) where
  gates : List (Gate F v)
  outputs : List (Arg v)

/-- The argument refers to an input or to a gate with index `< k`. -/
def Arg.Earlier {v : ℕ} : Arg v → ℕ → Prop
  | .input _, _ => True
  | .gate j, k => j < k

/-- Both arguments of the gate at position `k` are inputs or earlier gates. -/
def Gate.WellFormedAt {F : Type*} {v : ℕ} : Gate F v → ℕ → Prop
  | .mul a b, k => a.Earlier k ∧ b.Earlier k
  | .affine _ _ _ a b, k => a.Earlier k ∧ b.Earlier k

/-- Arguments are inputs or earlier gates, and designated outputs are inputs or gates of the
circuit. -/
def Circuit.WellFormed {F : Type*} {v : ℕ} (c : Circuit F v) : Prop :=
  (∀ (k : ℕ) (h : k < c.gates.length), (c.gates[k]'h).WellFormedAt k) ∧
    ∀ o ∈ c.outputs, o.Earlier c.gates.length

/-- The value of an argument, given the inputs and the values of the gates computed so far. -/
def Arg.eval {F : Type*} [Zero F] {v : ℕ} (x : Fin v → F) (vals : List F) : Arg v → F
  | .input i => x i
  | .gate k => vals.getD k 0

/-- The value of a gate. -/
def Gate.eval {F : Type*} [Field F] {v : ℕ} (x : Fin v → F) (vals : List F) : Gate F v → F
  | .mul a b => a.eval x vals * b.eval x vals
  | .affine lam mu nu a b => lam * a.eval x vals + mu * b.eval x vals + nu

/-- The gate values of the circuit on input `x`, in gate order. -/
def Circuit.values {F : Type*} [Field F] {v : ℕ} (c : Circuit F v) (x : Fin v → F) : List F :=
  c.gates.foldl (fun vals g => vals ++ [g.eval x vals]) []

/-- The input assignment `x` satisfies the circuit: every designated output equals one. -/
def Circuit.Satisfied {F : Type*} [Field F] {v : ℕ} (c : Circuit F v) (x : Fin v → F) : Prop :=
  ∀ o ∈ c.outputs, o.eval x (c.values x) = 1

/-- The RAM code of an argument. -/
def Arg.code {v : ℕ} : Arg v → ℕ
  | .input i => 2 * (i : ℕ)
  | .gate k => 2 * k + 1

/-- The six RAM cells of a gate. -/
def Gate.code {F : Type*} [Fintype F] (e : F ≃ Fin (Fintype.card F)) {v : ℕ} : Gate F v → List ℕ
  | .mul a b => [0, 0, 0, 0, a.code, b.code]
  | .affine lam mu nu a b => [1, (e lam : ℕ), (e mu : ℕ), (e nu : ℕ), a.code, b.code]

/-- The RAM cells of a circuit. -/
def Circuit.code {F : Type*} [Fintype F] (e : F ≃ Fin (Fintype.card F)) {v : ℕ}
    (c : Circuit F v) : List ℕ :=
  [c.gates.length, c.outputs.length] ++ c.gates.flatMap (Gate.code e) ++ c.outputs.map Arg.code

/-- The RAM input listing `v` and the circuits `cs` (cell `i` holds the `i`-th entry). -/
def circuitsInput {F : Type*} [Fintype F] (e : F ≃ Fin (Fintype.card F)) (v : ℕ)
    (cs : List (Circuit F v)) : List ℕ :=
  [v, cs.length] ++ cs.flatMap (Circuit.code e)

end MinrankTW.Supplement


