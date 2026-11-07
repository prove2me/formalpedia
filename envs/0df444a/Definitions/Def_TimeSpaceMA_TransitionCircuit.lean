-- Prove2me | Definitions.Def_TimeSpaceMA_TransitionCircuit
-- name    : TimeSpaceMA_TransitionCircuit
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T10:56:07.099848+00:00
-- url     : https://prove2.me/theorems/257dc20b-0fc2-4ef3-9373-ae83b8eac0e9
-- title:
--   NAND transition circuit and its run
-- statement:
--   A **transition circuit** has $S+1$ inputs (a configuration of $S$ bits and a read bit), $g$ NAND gates listed in topological order, an output gate $\mathrm{out}(i)$ for each configuration bit, and $\log H$ configuration positions for each of the row and column parts of the address register, where $H = 2^{\log H}$.
--
--   It maps $(c,\beta)$ to the next configuration $\mathcal C(c,\beta)$. The **run** from $c$ on an $H\times H$ bit matrix $X$ is $C^0=c$, $C^k=\mathcal C(C^{k-1},X_{a_kb_k})$, where $(a_k,b_k)$ is the address stored in $C^{k-1}$.
--
--   **Formalization Note** Definition by the page's properties, not by a particular machine: any such circuit is allowed.
-- source:
--   Williams, Xi, Short Non-Interactive Proofs for Time-Space Computations, STOC 2027 submission (manuscript sha256 184c2f95…), §3.1, pp.7–8

import Mathlib

namespace TimeSpaceMA

/-- An input of a gate: a configuration bit, the read bit, or an earlier gate. -/
inductive Wire (S g : ℕ)
  | config (i : Fin S)
  | read
  | gate (j : Fin g)

/-- A NAND transition circuit (Williams, Xi, STOC 2027 submission, manuscript sha256 184c2f95…, §3.1,
pp.7–8): `S + 1` input wires (a configuration and the read bit), `g` NAND gates listed in topological
order, an output gate `out i` per configuration bit, and `log H = lg` configuration positions holding
each of the row and the column parts of the address register.

**Formalization Note** The machine's own transition circuit is one instance; Lemma 3.8 holds for each
such circuit (`paper.md`, decision 11). Bits are read in the order of `Nat.testBit`. -/
structure TransitionCircuit (S g lg : ℕ) where
  in₁ : Fin g → Wire S g
  in₂ : Fin g → Wire S g
  in₁_lt : ∀ j j', in₁ j = .gate j' → j' < j
  in₂_lt : ∀ j j', in₂ j = .gate j' → j' < j
  out : Fin S → Fin g
  rowWire : Fin lg → Fin S
  colWire : Fin lg → Fin S

namespace TransitionCircuit

variable {S g lg : ℕ}

/-- The value of a wire given the configuration, the read bit and the gate values. -/
def wireBit (c : Fin S → Bool) (β : Bool) (z : Fin g → Bool) : Wire S g → Bool
  | .config i => c i
  | .read => β
  | .gate j => z j

/-- One pass of NAND evaluation over all gates. -/
def gateStep (C : TransitionCircuit S g lg) (c : Fin S → Bool) (β : Bool) (z : Fin g → Bool) :
    Fin g → Bool :=
  fun j => !(wireBit c β z (C.in₁ j) && wireBit c β z (C.in₂ j))

/-- The gate values on `(c, β)`: `g` passes reach the fixed point, since the gates are in topological
order. -/
def gateValues (C : TransitionCircuit S g lg) (c : Fin S → Bool) (β : Bool) : Fin g → Bool :=
  (C.gateStep c β)^[g] fun _ => false

/-- The next configuration `C(c, β)`. -/
def next (C : TransitionCircuit S g lg) (c : Fin S → Bool) (β : Bool) : Fin S → Bool :=
  fun i => C.gateValues c β (C.out i)

/-- The number in `[2^lg]` with the given bits. -/
def addrOfBits (f : Fin lg → Bool) : Fin (2 ^ lg) :=
  ⟨(∑ i : Fin lg, (f i).toNat * 2 ^ i.val) % 2 ^ lg, Nat.mod_lt _ (by positivity)⟩

/-- The address `(a, b)` stored in a configuration. -/
def readAddress (C : TransitionCircuit S g lg) (c : Fin S → Bool) :
    Fin (2 ^ lg) × Fin (2 ^ lg) :=
  (addrOfBits fun i => c (C.rowWire i), addrOfBits fun i => c (C.colWire i))

/-- The run from `c` on the input matrix `X`: `C⁰ = c`, `Cᵏ = C(Cᵏ⁻¹, X_{a_k b_k})`, where
`(a_k, b_k)` is the address stored in `Cᵏ⁻¹`; p.8. -/
def runConfig (C : TransitionCircuit S g lg) (X : Fin (2 ^ lg) → Fin (2 ^ lg) → Bool)
    (c : Fin S → Bool) : ℕ → Fin S → Bool
  | 0 => c
  | k + 1 =>
      let prev := C.runConfig X c k
      C.next prev (X (C.readAddress prev).1 (C.readAddress prev).2)

end TransitionCircuit

end TimeSpaceMA


