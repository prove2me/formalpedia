-- Prove2me | Definitions.Def_TargetedSamplers_Supplement_OracleCircuit
-- name    : TargetedSamplers_Supplement_OracleCircuit
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T02:13:54.301213+00:00
-- url     : https://prove2.me/theorems/0d5307a1-3b6d-4e22-8870-2ae58d57c73e
-- title:
--   Randomized oracle circuits with $\mathbf{NP}^{\mathcal L}$ / $\Sigma_2^{\mathcal L}$ gates, list oracles and message oracles (§8)
-- statement:
--   A **randomized oracle circuit** has input bits, random bits and a sequence of gates: fan-in-2 AND/OR, NOT, **oracle-language gates** and **direct list gates**. An oracle-language gate on the bits $s$ of some earlier wires outputs whether $s$ belongs to a language defined by a verifier $V$ with oracle access to the input lists $\mathcal L$:
--
--   * for an $\mathbf{NP}^{\mathcal L}$ gate, $s$ is in the language iff some witness $w$ makes $V^{\mathcal L}(s,w)$ accept;
--   * for a $\Sigma_2^{\mathcal L}$ gate, iff some $w_1$ makes $V^{\mathcal L}(s,w_1,w_2)$ accept for every $w_2$.
--
--   A direct list gate returns the answer of one query to the lists. Its **size** is its number of gates, oracle gates included.
--
--   For a message $f\in\Sigma_0^n$, $\Sigma_0=[q]$, the quantity $\Pr_{x\in[n],C}[C(x)=f(x)]$ is the probability over a uniform position $x\in[n]$ and the random bits that $C$ outputs $f(x)$. Lists of tuples $L_r\subseteq\Sigma_0^b$ are accessed by queries $(r,j,p)$ (the $p$-th $\Sigma_0$-symbol of the $j$-th element of $L_r$); lists of symbols $L_z\subseteq[\sigma]$ by queries $(z,j)$; a message $f$ by queries $i$ (the symbol $f(i)$). $\Delta(g,h)$ is the relative Hamming distance of two tuples, and $\Pr_{r\in[N]}$ the uniform probability on $[N]$.
--
--   These objects state the doubly-local list-recovery decoders of Theorems 8.3 and 8.6.
--
--   **Formalization Note** Wires are numbered: inputs, random bits, then the gates' outputs; a missing wire reads $0$. Positions and symbols are written in binary with $\lceil\log_2 n\rceil$ and $\lceil\log_2 q\rceil$ bits. Queries are self-delimiting number codes; an absent entry is answered $0$, an entry $a$ by $a+1$. The parameters of the uniform programs are $(n,\ell,q,\lceil1/\epsilon\rceil,\lceil1/\delta\rceil)$. Also defined: the accounting of a run's list accesses (distinct elements $(r,j)$, and distinct symbols read of each).
-- source:
--   Chen, Doron, Ebtehaj, Tell, Targeted Samplers, STOC 2027 submission (manuscript sha256 599d0a59…), Definition 8.1, p.64 (pdf p.66); Theorems 8.3, 8.6, pp.66, 74–75 (pdf pp.68, 76–77)

import Mathlib
import Definitions.Def_TargetedSamplers_Machine
import Definitions.Def_TargetedSamplers_encInput
import Definitions.Def_TargetedSamplers_coinProb

namespace TargetedSamplers.Supplement

/-- Decode one self-delimiting number (`encNat`) from the front of a bit string; returns the number
and the rest of the string. -/
def decNat : List Bool → ℕ × List Bool
  | true :: b :: rest => (b.toNat + 2 * (decNat rest).1, (decNat rest).2)
  | _ :: rest => (0, rest)
  | [] => (0, [])

/-- Decode `k` self-delimiting numbers from the front of a bit string. -/
def decNats : ℕ → List Bool → List ℕ
  | 0, _ => []
  | k + 1, s => (decNat s).1 :: decNats k (decNat s).2

/-- A gate of an oracle circuit. Wires are numbered: first the circuit's input bits, then its random
bits, then one or more wires per gate in order. `and`, `or`, `not` read two or one earlier wires and
add one wire; `oracle args` is a gate of the oracle language (NP^L or Σ₂^L) on the bits of the wires
`args`, adding one wire; `listQ args` is a direct oracle gate to the input lists on the query
`args`, adding the wires of its answer. A wire that does not exist reads `0`. -/
inductive OGate
  | and (a b : ℕ)
  | or (a b : ℕ)
  | not (a : ℕ)
  | oracle (args : List ℕ)
  | listQ (args : List ℕ)

/-- A randomized oracle circuit: `inLen` input bits, `coins` random bits, gates in order, and the
list of output wires. -/
structure OCircuit where
  inLen : ℕ
  coins : ℕ
  gates : List OGate
  outs : List ℕ

namespace OCircuit

/-- The outputs of the circuit on the wire values `inp` (input bits followed by random bits), when
the oracle gates answer membership in `lang` and the list gates answer `lq`. -/
def eval (C : OCircuit) (lang : List Bool → Bool) (lq : List Bool → List Bool) (inp : List Bool) :
    List Bool :=
  let wires := C.gates.foldl (fun vs g => vs ++ match g with
    | .and a b => [vs.getD a false && vs.getD b false]
    | .or a b => [vs.getD a false || vs.getD b false]
    | .not a => [!(vs.getD a false)]
    | .oracle args => [lang (args.map fun a => vs.getD a false)]
    | .listQ args => lq (args.map fun a => vs.getD a false)) inp
  C.outs.map fun a => wires.getD a false

/-- The size of the circuit: its number of gates, oracle gates included. -/
def size (C : OCircuit) : ℕ := C.gates.length

/-- The number of oracle-language gates. -/
def numOracle (C : OCircuit) : ℕ := C.gates.countP fun g => match g with
  | .oracle _ => true
  | _ => false

/-- The number of direct list-oracle gates. -/
def numListQ (C : OCircuit) : ℕ := C.gates.countP fun g => match g with
  | .listQ _ => true
  | _ => false

/-- The description of the circuit as a bit string. -/
def encode (C : OCircuit) : List Bool :=
  encNat C.inLen ++ encNat C.coins ++ encNat C.gates.length ++
    C.gates.flatMap (fun g => match g with
      | .and a b => [false, false, false] ++ encNat a ++ encNat b
      | .or a b => [false, false, true] ++ encNat a ++ encNat b
      | .not a => [false, true, false] ++ encNat a
      | .oracle args => [false, true, true] ++ encNat args.length ++ args.flatMap encNat
      | .listQ args => [true, false, false] ++ encNat args.length ++ args.flatMap encNat) ++
    encNat C.outs.length ++ C.outs.flatMap encNat

end OCircuit

/-- The description of a list of circuits. -/
def encodeCircuits (cs : List OCircuit) : List Bool := encNat cs.length ++ cs.flatMap OCircuit.encode

/-- `Pr_{x ∈ [n], C}[C(x) = f(x)]`: the probability, over a uniform position `x ∈ [n]` and the
circuit's random bits, that the randomized oracle circuit `C` outputs the symbol `f(x) ∈ Σ₀ = [q]`.
The position `x` is given in `⌈log₂ n⌉` bits and the output symbol is read in `⌈log₂ q⌉` bits (both
least significant first). -/
noncomputable def circSuccess {n q : ℕ} (C : OCircuit) (lang : List Bool → Bool)
    (lq : List Bool → List Bool) (f : Fin n → Fin q) : ℝ :=
  (∑ x : Fin n, coinProb C.coins (fun ρ =>
      C.eval lang lq (bitsFixed (Nat.clog 2 n) x ++ ρ) = bitsFixed (Nat.clog 2 q) (f x))) / n

/-- The fraction of `r ∈ [N]` with `P r` (`Pr_{r ∈ [N]}[P(r)]`; `0` for `N = 0`). -/
noncomputable def fracFin (N : ℕ) (P : Fin N → Prop) : ℝ :=
  open Classical in ((Finset.univ.filter P).card : ℝ) / N

/-- The relative Hamming distance `∆(g, h)` between two tuples of `b` symbols. -/
noncomputable def relHamming {b q : ℕ} (g h : Fin b → Fin q) : ℝ :=
  open Classical in ((Finset.univ.filter fun u => g u ≠ h u).card : ℝ) / b

/-- Oracle access to input lists of tuple-symbols `L_r ⊆ Σ = Σ₀^b` (Theorem 8.3): the query
encoding `(r, j, p)` is answered by `1 +` the `p`-th `Σ₀`-symbol of the `j`-th element of `L_r`, and
by `0` if there is no such entry. -/
def tupleListOracle {N b q : ℕ} (L : Fin N → List (Fin b → Fin q)) : List Bool → ℕ := fun s =>
  match decNats 3 s with
  | [r, j, p] =>
      if h : r < N then
        if h' : j < (L ⟨r, h⟩).length then
          if hp : p < b then (((L ⟨r, h⟩)[j]'h') ⟨p, hp⟩).val + 1 else 0
        else 0
      else 0
  | _ => 0

/-- Oracle access to input lists of symbols `L_z ⊆ Σ = [σ]` (Theorem 8.6): the query encoding
`(z, j)` is answered by `1 +` the `j`-th element of `L_z`, and by `0` if there is none. -/
def symListOracle {N σ : ℕ} (L : Fin N → List (Fin σ)) : List Bool → ℕ := fun s =>
  match decNats 2 s with
  | [z, j] =>
      if h : z < N then
        if h' : j < (L ⟨z, h⟩).length then ((L ⟨z, h⟩)[j]'h').val + 1 else 0
      else 0
  | _ => 0

/-- Oracle access to a message `f ∈ Σ₀ⁿ`, `Σ₀ = [q]`: the query encoding `i` is answered by
`1 + f(i)`, and by `0` if `i ≥ n`. -/
def msgOracle {n q : ℕ} (f : Fin n → Fin q) : List Bool → ℕ := fun s =>
  match decNats 1 s with
  | [i] => if h : i < n then (f ⟨i, h⟩).val + 1 else 0
  | _ => 0

/-- The answer bits of a direct list-oracle gate: the oracle's answer in `⌈log₂ (q + 1)⌉` bits. -/
def listGateAnswer (O : List Bool → ℕ) (q : ℕ) : List Bool → List Bool :=
  fun s => bitsFixed (Nat.clog 2 (q + 1)) (O s)

open Classical in
/-- The NP^L language of the verifier `V` with parameters `ps`: a query string `s` is in it iff some
witness `w` makes `V^L(ps, s, w)` output `1`, where `V` has oracle access `O` to the lists. -/
noncomputable def npLang (V : Program) (ps : List ℕ) (O : List Bool → ℕ) : List Bool → Bool :=
  fun s => decide (∃ w : List Bool, V.Outputs ⟨encInput ps [s, w], [], [], O⟩ (some [true]))

open Classical in
/-- The Σ₂^L language of the verifier `V` with parameters `ps`: `s` is in it iff some `w₁` makes
`V^L(ps, s, w₁, w₂)` output `1` for every `w₂`. -/
noncomputable def sigma2Lang (V : Program) (ps : List ℕ) (O : List Bool → ℕ) : List Bool → Bool :=
  fun s => decide (∃ w₁ : List Bool, ∀ w₂ : List Bool,
    V.Outputs ⟨encInput ps [s, w₁, w₂], [], [], O⟩ (some [true]))

/-- The parameters `(n, ℓ, |Σ₀|, ϵ, δ)` of a code of §8 as the input of a uniform program:
`n, ℓ, q = |Σ₀|` and the integers `⌈1/ϵ⌉, ⌈1/δ⌉`. -/
noncomputable def codeParams (n ℓ q : ℕ) (ϵ δ : ℝ) : List ℕ := [n, ℓ, q, ⌈1 / ϵ⌉₊, ⌈1 / δ⌉₊]

/-- The list elements `(r, j)` accessed by a run that asked the queries `qs` of `tupleListOracle`:
the distinct pairs `(r, j)` among the decoded queries `(r, j, p)`. -/
def tupleQueryElems (qs : List (List Bool)) : List (List ℕ) :=
  (qs.map fun s => (decNats 3 s).take 2).dedup

/-- The number of distinct `Σ₀`-symbols read of the list element `π = (r, j)`: the distinct queries
`(r, j, p)` among `qs`. -/
def tupleQueryReads (qs : List (List Bool)) (π : List ℕ) : ℕ :=
  ((qs.filter fun s => decide ((decNats 3 s).take 2 = π)).map (decNats 3)).dedup.length

end TargetedSamplers.Supplement


