-- Prove2me | Definitions.Def_PrivPCP_Circuit
-- name    : PrivPCP_Circuit
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T21:42:49.754044+00:00
-- url     : https://prove2.me/theorems/2ffb3dbe-a75b-4ce7-b943-88162af823c1
-- title:
--   Boolean circuits, their size and code; Circuit-SAT
-- statement:
--   A **Boolean circuit** $\Phi:\{0,1\}^m\to\{0,1\}$ is a number $m$ of inputs together with a fan-in-two circuit over the full binary basis on those inputs: gates listed in topological order, each applying one of the sixteen operations $\{0,1\}^2\to\{0,1\}$ to two sources (a constant, an input, or an earlier gate), and an output that is a constant or a literal of an input or a gate. The circuit model is the published $B_2$-circuit, with $\{0,1\}$ identified with $\mathbb F_2$.
--
--   1. The **size** of $\Phi$ is $n=m+(\text{number of gates})$.
--   2. $\Phi(w)\in\{0,1\}$ is the value of the circuit on an assignment $w\in\{0,1\}^m$.
--   3. The **code** of $\Phi$ is a bit string listing $m$ in unary and then the published word list of the circuit (gate count, truth tables and sources); its length is polynomial in $n$.
--
--   **Circuit-SAT** is the set
--   $$\mathrm{CircuitSAT}=\{\Phi:\ \exists\, w\in\{0,1\}^m,\ \Phi(w)=1\}.$$
--
--   These are the instances of the private PCPs of Corollary 8.3; the prover sampler and the verifier read a circuit through its code.
--
--   **Formalization Note** The paper does not fix a gate basis; fan-in-two circuits over the full binary basis contain the $\{\wedge,\vee,\neg\}$ circuits, and counting wires instead of gates changes $n$ by a constant factor.
-- source:
--   Bafna, Vyas, Private PCPs from Product Expansion, STOC 2027 submission manuscript (sha256 c2cac1e07fc4af8721f673867373fc5bd417aa65f45cf170c543568abcf1e47e), Definition 8.2, p.46 (PDF p.48)

import Mathlib
import Definitions.Def_AffDisp4n_Circuit
import Definitions.Def_AffDisp4n_Acyclic_eval
import Definitions.Def_AffDisp4n_Acyclic_tokens
import Definitions.Def_QAdvFew_PoQOracle_tup

open QAlgorithms.Complexity QAdvFew.PoQOracle

namespace PrivPCP

/-- A **Boolean circuit** `Φ : {0,1}^m → {0,1}` as an instance of Circuit-SAT (Bafna, Vyas, *Private PCPs
from Product Expansion*, STOC 2027 submission manuscript (sha256 c2cac1e0…), Definition 8.2, p.46): the number
`m` of inputs together with a fan-in-two B₂-circuit on `m` inputs (the published `AffDisp4n.Circuit m`: gates
in topological order, each applying one of the sixteen operations `𝔽₂ × 𝔽₂ → 𝔽₂` to two earlier sources,
constants free, output a constant or a literal).

**Formalization Note** The paper does not fix a basis. Fan-in-two circuits over the full binary basis contain
the `{AND, OR, NOT}` circuits; `{0,1}` is `𝔽₂ = ZMod 2`. -/
abbrev Circuit : Type := Σ m : ℕ, AffDisp4n.Circuit m

namespace Circuit

/-- The **size** `n` of a circuit: inputs plus gates. -/
def size (Φ : Circuit) : ℕ := Φ.1 + Φ.2.size

/-- The value `Φ(w)` of the circuit on an assignment `w ∈ {0,1}^m`. -/
def eval (Φ : Circuit) (w : Fin Φ.1 → ZMod 2) : ZMod 2 := Φ.2.eval w

/-- The **code** of a circuit as a bit string, read by the prover sampler and the verifier: the number of
inputs in unary, then the published word list of the circuit (gate count, truth tables, sources). Its length
is polynomial in `size Φ`. -/
def code (Φ : Circuit) : Str :=
  tup (AffDisp4n.natWord Φ.1 :: Φ.2.tokens (fun i => AffDisp4n.natWord i.val))

end Circuit

/-- **Circuit-SAT** (Definition 8.2, p.46): `CircuitSAT = {Φ : ∃ w ∈ {0,1}^m, Φ(w) = 1}`. -/
def CircuitSAT : Set Circuit := {Φ | ∃ w : Fin Φ.1 → ZMod 2, Φ.eval w = 1}

end PrivPCP


