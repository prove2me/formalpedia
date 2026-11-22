-- Prove2me | Definitions.Def_RandPurIso_Completion_StatefulCirc
-- name    : RandPurIso_Completion_StatefulCirc
-- status  : Definition
-- author  : @iris
-- created : 2026-11-10T21:28:28.082413+00:00
-- url     : https://prove2.me/theorems/b1550a46-455c-42de-96b4-c4b48852b59d
-- title:
--   Stateful oracle circuit and the oracle it realizes
-- statement:
--   A **stateful oracle circuit** acts on $k$ data qubits (the query register), $s$ private-state qubits and $a$ ancilla qubits. Each invocation encodes the query input on the data qubits, appends fresh ancillas $|0^a\rangle$, runs the circuit, traces out the ancillas and decodes the data qubits (a string $e_{\mathrm{Out}}(o)$ gives $o$, every other string gives $\perp$), keeping the private qubits. The private register starts in $|0^s\rangle$. This realizes an oracle $\mathsf{In}\to\mathsf{Out}_\perp$ with private register $\{0,1\}^s$, and is the model of the paper's "stateful simulator that makes at most one query to its oracle per invocation". `width` is $k+s+a$.
-- source:
--   Goldin, On Random Purifications of Isometries and Channels, arXiv:2611.04573, Theorems 4.1, 5.4 and Corollary 4.2, pp. 26–29

import Mathlib
import Definitions.Def_RandPurIso_Completion_QInstr
import Definitions.Def_RandPurIso_Completion_Oracle
open Matrix

namespace RandPurIso.Completion

open ShiShallow

/-- **Stateful oracle circuit** (the simulators of Goldin, *On Random Purifications of Isometries and Channels*, arXiv:2611.04573, Theorems 4.1 and 5.4 and Corollary 4.2:
"stateful simulator … makes at most one query to its oracle per invocation").

A circuit over `k` data qubits (the query register), `s` private-state qubits (kept between
invocations, initially `|0^s⟩`) and `a` fresh ancilla qubits (initialized to `|0^a⟩` and traced
out after each invocation), made of Clifford+T gates and queries to `q` oracles. -/
structure StatefulCirc (q : ℕ) (w : Fin q → ℕ) (k : ℕ) where
  /-- number of private-state qubits -/
  s : ℕ
  /-- number of ancilla qubits -/
  a : ℕ
  /-- the instruction list, on `k + s + a` qubits -/
  circ : List (QInstr q w (k + s + a))

/-- The number of qubits the circuit uses. -/
def StatefulCirc.width {q : ℕ} {w : Fin q → ℕ} {k : ℕ} (S : StatefulCirc q w k) : ℕ :=
  k + S.s + S.a

/-- Concatenate data, private-state and ancilla strings. -/
def joinBits {k s a : ℕ} (u : Bits k) (σ : Bits s) (α : Bits a) : Bits (k + s + a) :=
  Fin.append (Fin.append u σ) α

open Classical in
/-- **The oracle realized by a stateful circuit**, given the oracles' channels `Ψ` and encodings of
the query input and output registers into the `k` data qubits.

On input `ρ` on `In ⊗ St` (`St = {0,1}^s`): encode `In` by `eIn`, append `|0^a⟩`, run the circuit,
trace out the ancillas, and read the data qubits back: a string `eOut o` gives `o`, every other
string gives `⊥` (Definition 3.4's "|⊥⟩ ∈ B"); the private qubits are kept. The initial state is
`|0^s⟩`. -/
noncomputable def StatefulCirc.realize {q : ℕ} {w : Fin q → ℕ} {k : ℕ} {In Out : Type}
    [Fintype In] [Fintype Out] (S : StatefulCirc q w k)
    (Ψ : (j : Fin q) → Matrix (Bits (w j)) (Bits (w j)) ℂ → Matrix (Bits (w j)) (Bits (w j)) ℂ)
    (eIn : In → Bits k) (eOut : Out → Bits k) : Oracle In (Option Out) (Bits S.s) where
  map ρ :=
    let E : Matrix (Bits (k + S.s + S.a)) (In × Bits S.s) ℂ :=
      fun z p => if z = joinBits (eIn p.1) p.2 (fun _ => false) then 1 else 0
    let σ := QInstr.evalList Ψ S.circ (E * ρ * Eᴴ)
    fun p q => match p.1, q.1 with
      | some o, some o' => ∑ α : Bits S.a, σ (joinBits (eOut o) p.2 α) (joinBits (eOut o') q.2 α)
      | none, none => ∑ α : Bits S.a, ∑ u : Bits k,
          if ∃ o, eOut o = u then 0 else σ (joinBits u p.2 α) (joinBits u q.2 α)
      | _, _ => 0
  init σ := if σ = (fun _ => false) then 1 else 0

end RandPurIso.Completion


