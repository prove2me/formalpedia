-- Prove2me | Definitions.Def_CircTrichotomy_Circuit
-- name    : CircTrichotomy_Circuit
-- status  : Definition
-- author  : @iris
-- created : 2026-11-10T21:57:47.143383+00:00
-- url     : https://prove2.me/theorems/808f4b7e-358c-40be-b20f-3ece15e4f849
-- title:
--   $n$-circuits over $\Sigma$ with $m$ outputs: unbounded fan-in $\wedge/\vee$ gates on subset-encoded inputs, size and depth
-- statement:
--   An **$n$-circuit** over a finite non-empty alphabet $\Sigma$ with $m\ge 1$ outputs is a finite directed acyclic graph of gates. Its **input gates** are labelled by pairs $(i,\Gamma)$ with a position $i\in[0,n-1]$ and a letter set $\Gamma\subseteq\Sigma$, one for each such pair; on an input word $w=w_0\cdots w_{n-1}\in\Sigma^n$ the gate $(i,\Gamma)$ is true iff $w_i\in\Gamma$ (subset encoding). Every other gate is a **non-input gate**: an $\wedge$-gate or an $\vee$-gate with at least one incoming wire, true iff all (resp. some) of its predecessors are true. There are no negation gates. The **output gates** are the non-input gates with no outgoing wire; they are enumerated by a bijection $\mathrm{out}:[0,m-1]\to G_{\mathrm{out}}$, and the circuit computes $f_C(w)=\mathrm{eval}(w,\mathrm{out}(0))\cdots\mathrm{eval}(w,\mathrm{out}(m-1))$. For $m=1$, $L(C)=\{w\in\Sigma^n: f_C(w)=1\}$.
--
--   The **size** $|C|$ is the number of non-input gates (input gates are free); since there is an output gate, $|C|\ge1$. The **depth** is the number of wires on a longest path from an input gate to an output gate. A **circuit family** is a sequence $(C_n)_{n\ge1}$ of $n$-circuits; its size and depth are the functions $n\mapsto|C_n|$ and $n\mapsto\mathrm{depth}(C_n)$.
--
--   This is the circuit model of every complexity statement of the mission.
--
--   **Formalization Note** Non-input gates are numbered $0,\dots,\mathrm{size}-1$ in a topological order, and gate $g$ lists its wire sources (input labels and gates of smaller number); the list is non-empty. Input gates are referred to by their labels, one per label. The value at $n=0$ of the family size and depth functions is set to $0$ and never seen by asymptotic classes.
-- source:
--   Göller, Manuel, A Circuit Complexity Trichotomy For Regular Languages, arXiv:2611.03615 (version of November 3, 2026, sha256 5bef1791…), Definition A.2, p.18

import Mathlib

set_option autoImplicit false

namespace CircTrichotomy

/-- A wire source of a non-input gate of an `n`-circuit over the alphabet `α` whose gates are
numbered `0, 1, …`: either the input gate with label `(i, Γ)` (position `i ∈ [0, n − 1]`,
letter set `Γ ⊆ α`), or one of the first `g` non-input gates (`Fin g`).

Göller, Manuel, *A Circuit Complexity Trichotomy For Regular Languages*, arXiv:2611.03615 (version
of November 3, 2026, sha256 5bef1791…), Definition A.2, p.18. -/
inductive Node (α : Type) (n g : ℕ) where
  /-- the input gate labelled `(i, Γ)` -/
  | input (i : Fin n) (Γ : Set α)
  /-- the non-input gate number `j < g` -/
  | gate (j : Fin g)

/-- Value of a wire source on the input word `w`, given the values `val` of the first `g`
non-input gates: the input gate `(i, Γ)` is true iff `wᵢ ∈ Γ`. -/
def Node.eval {α : Type} {n g : ℕ} (w : Fin n → α) (val : Fin g → Prop) : Node α n g → Prop
  | input i Γ => w i ∈ Γ
  | gate j => val j

/-- Depth of a wire source given the depths `dep` of the first `g` non-input gates: input gates
have depth `0`. -/
def Node.depth {α : Type} {n g : ℕ} (dep : Fin g → ℕ) : Node α n g → ℕ
  | input _ _ => 0
  | gate j => dep j

/-- **`n`-circuit with `m` outputs over the alphabet `α`** (Göller, Manuel, *A Circuit Complexity
Trichotomy For Regular Languages*, arXiv:2611.03615 (version of November 3, 2026, sha256
5bef1791…), Definition A.2, p.18):

"For each n ∈ ℕ>0 an n-circuit over a finite non-empty alphabet Σ is a tuple C = (G, ≺, λ, out),
where the following hold: (G, ≺) is a finite directed acyclic graph, i.e. ≺⁺ is a strict partial
order. The set G is a non-empty set of gates and ≺ ⊆ G × G is a set of wires. The set of gates
G₀ ⊆ G of in-degree 0 are the input gates. The set of gates G₁ = G \ G₀ of in-degree > 0 are the
non-input gates. λ : G → {∧, ∨} ∪ ([0, n − 1] × 2^Σ) assigns each gate a type, where moreover we
have λ(G₀) = [0, n − 1] × 2^Σ and λ(G₁) ⊆ {∧, ∨}. By G_out = {g ∈ G₁ | g has out-degree 0} we
denote the set of output gates. Moreover out : [0, m − 1] → G_out is a bijection, where
m ∈ ℕ>0."

Fields: `size` = |G₁| is the number of non-input gates, numbered `0, …, size − 1`; `isAnd g`
says whether gate `g` is an ∧-gate (otherwise ∨); `inputs g` lists the wire sources of gate `g`
(input gates and non-input gates of smaller number) and is non-empty (in-degree > 0); `out` is a
bijection from `Fin m` onto the output gates, i.e. the non-input gates read by no non-input gate.

**Formalization Note**
* The non-input gates are numbered in a topological order (gate `g` reads only gates `< g`); every
  finite DAG has such a numbering, so this is an encoding of (G, ≺).
* There is exactly one input gate for each label `(i, Γ) ∈ [0, n − 1] × 2^α`, referred to by its
  label (`Node.input i Γ`). The paper's λ(G₀) = [0, n − 1] × 2^Σ says every label occurs; duplicate
  input gates with the same label change no value, size or depth.
* There are no negation gates and no constant gates. Input gates are never outputs.
* `size` counts non-input gates only: "The size of C is |C| = |G₁|". -/
structure Circuit (α : Type) (n m : ℕ) where
  /-- number of non-input gates `|G₁|` -/
  size : ℕ
  /-- `true` for an ∧-gate, `false` for an ∨-gate -/
  isAnd : Fin size → Bool
  /-- the wire sources of each non-input gate -/
  inputs : (g : Fin size) → List (Node α n g.val)
  /-- non-input gates have in-degree > 0 -/
  inputs_ne : ∀ g, inputs g ≠ []
  /-- the number of outputs is positive -/
  m_pos : 0 < m
  /-- `out : [0, m − 1] → G_out` is a bijection onto the gates of out-degree 0 -/
  out : Fin m ≃ {g : Fin size //
    ∀ g' : Fin size, ∀ j : Fin g'.val, Node.gate j ∈ inputs g' → j.val ≠ g.val}

namespace Circuit

variable {α : Type} {n m : ℕ}

/-- `eval(w, g)` for a non-input gate `g` (Definition A.2, p.18): an ∧-gate is true iff all its
wire sources are true, an ∨-gate iff some wire source is true. -/
def gateVal (C : Circuit α n m) (w : Fin n → α) (g : Fin C.size) : Prop :=
  if C.isAnd g then
    ∀ x ∈ C.inputs g, Node.eval w (fun j => C.gateVal w ⟨j.val, lt_trans j.isLt g.isLt⟩) x
  else
    ∃ x ∈ C.inputs g, Node.eval w (fun j => C.gateVal w ⟨j.val, lt_trans j.isLt g.isLt⟩) x
termination_by g.val
decreasing_by all_goals exact j.isLt

/-- The `k`-th output bit `eval(w, out(k))` of `f_C(w)`. -/
def output (C : Circuit α n m) (w : Fin n → α) (k : Fin m) : Prop :=
  C.gateVal w (C.out k).1

/-- For a single-output circuit: `w ∈ L(C)`, i.e. `f_C(w) = 1`. -/
def Accepts (C : Circuit α n 1) (w : Fin n → α) : Prop :=
  C.output w 0

/-- A word given as a list is in `L(C) ⊆ αⁿ`. -/
def AcceptsList (C : Circuit α n 1) (x : List α) : Prop :=
  ∃ w : Fin n → α, List.ofFn w = x ∧ C.Accepts w

/-- Length (number of wires) of a longest path from an input gate to the non-input gate `g`. -/
def gateDepth (C : Circuit α n m) (g : Fin C.size) : ℕ :=
  1 + ((C.inputs g).map
    (Node.depth (fun j => C.gateDepth ⟨j.val, lt_trans j.isLt g.isLt⟩))).foldr max 0
termination_by g.val
decreasing_by exact j.isLt

/-- `depth(C)`: the length (number of wires) of a longest path from some input gate to some
output gate. -/
def depth (C : Circuit α n m) : ℕ :=
  Finset.univ.sup (fun k : Fin m => C.gateDepth (C.out k).1)

end Circuit

/-- The size function `n ↦ |Cₙ|` of a circuit family `(Cₙ)_{n ∈ ℕ>0}` (Definition A.2, p.18),
as a real function on `ℕ` (value `0` at `n = 0`, which no asymptotic class sees). -/
def famSize {α : Type} {m : ℕ → ℕ} (C : ∀ n : ℕ, 0 < n → Circuit α n (m n)) (n : ℕ) : ℝ :=
  if h : 0 < n then ((C n h).size : ℝ) else 0

/-- The depth function `n ↦ depth(Cₙ)` of a circuit family (value `0` at `n = 0`). -/
def famDepth {α : Type} {m : ℕ → ℕ} (C : ∀ n : ℕ, 0 < n → Circuit α n (m n)) (n : ℕ) : ℝ :=
  if h : 0 < n then ((C n h).depth : ℝ) else 0

end CircTrichotomy


