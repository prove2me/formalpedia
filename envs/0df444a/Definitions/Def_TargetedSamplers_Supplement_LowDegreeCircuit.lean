-- Prove2me | Definitions.Def_TargetedSamplers_Supplement_LowDegreeCircuit
-- name    : TargetedSamplers_Supplement_LowDegreeCircuit
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T02:13:24.026948+00:00
-- url     : https://prove2.me/theorems/0787ec0a-09f7-4dc0-85a2-e4c6c8011860
-- title:
--   Highly uniform $(d\times w)$-circuits with $(\Delta,T)$-low-degree universal gates (Definition 6.1)
-- statement:
--   Let $\iota,d,w,k,T:\mathbb N\to\mathbb N$ and $\Delta:\mathbb N\to\mathbb R$. A family $\{C_N:\{0,1\}^{\iota(N)}\to\{0,1\}^{w(N)}\}$ is **computable by a highly uniform family of $(d\times w)$-circuits with $(\Delta,T)$-low-degree universal gates of fan-in $k$** if for every $N$ there are an arithmetic circuit $G_N$ over $\mathbb F_2$ and a wiring such that:
--
--   1. **Circuit structure.** $C_N(x)$ is the output of a circuit with $d(N)$ layers of $w(N)$ gates; every gate of layer $i$ computes the same arithmetic circuit $G_N$ on its children, which are gates of layer $i-1$ (input bits for $i=1$) or constants. $G_N$ has $\iota(N)$ inputs, size at most $T(N)$ and degree at most $\Delta(N)$, and one program prints it from $1^N$ in time $\widetilde O(T(N))$. Gates of layers $2,\dots,d$ have fan-in at most $k(N)$; first-layer gates have unbounded fan-in.
--   2. **Uniformity.** The map $(i,g,j)\mapsto$ ($j$-th child of gate $g$ in layer $i$) is computed by Boolean formulas of depth $O(\log\log w(N))$ that one program prints from $1^N$ in polynomial time.
--
--   A function is **computable in linear time** if one program outputs $f(N)$ in binary from $1^N$ in time $O(N)$.
--
--   These circuits are the hard functions of Theorems 6.3 and 6.9: small circuits whose gates are, each, a low-degree $\mathbb F_2$-polynomial computed by a circuit of size about $T$.
--
--   **Formalization Note** The degree is the total degree of the polynomial over $\mathbb F_2$ that $G_N$ computes. The constants hidden in the definition (of $\widetilde O(T)$, of $O(\log\log w)$ and of the polynomial time) form a structure `UnifConsts` that the theorems quantify. Layers are $1,\dots,d$, gates $0,\dots,w-1$, children $0,\dots,\iota(N)-1$, in fixed-width binary; the formula output is a tag bit and an index or a constant; a wire past the width of its layer reads $0$. Fan-in counts distinct children. The family is indexed by $N$ with input length $\iota(N)$ ($\iota=\mathrm{id}$ in Theorem 6.3, $\iota(n)=n+r(n)$ in Theorem 6.9), and the programs receive $1^N$ for the index. $\widetilde O(T)$ and $O(N)$ are the base mission's `budget`.
-- source:
--   Chen, Doron, Ebtehaj, Tell, Targeted Samplers, STOC 2027 submission (manuscript sha256 599d0a59…), Definition 6.1, footnote 32, Remark 6.2, p.47 (pdf p.49)

import Mathlib
import Definitions.Def_TargetedSamplers_Machine
import Definitions.Def_TargetedSamplers_encInput

namespace TargetedSamplers.Supplement

/-- A gate of an arithmetic circuit over `F₂`: a variable `x_i`, a constant, or the sum or product of
two earlier gates (referenced by position). -/
inductive AGate
  | var (i : ℕ)
  | const (b : Bool)
  | add (a b : ℕ)
  | mul (a b : ℕ)

/-- An arithmetic circuit over `F₂`: a list of gates in order; the output is the last gate. Its size
is the number of gates. A reference to a gate that is not earlier reads the polynomial `0`. -/
structure ArithCircuit where
  gates : List AGate

namespace ArithCircuit

/-- The polynomials over `F₂` computed by the gates, in order. -/
noncomputable def polys (G : ArithCircuit) : List (MvPolynomial ℕ (ZMod 2)) :=
  G.gates.foldl (fun ps g => ps ++ [match g with
    | .var i => MvPolynomial.X i
    | .const b => if b then 1 else 0
    | .add a b => ps.getD a 0 + ps.getD b 0
    | .mul a b => ps.getD a 0 * ps.getD b 0]) []

/-- The polynomial computed by the circuit (that of its last gate; `0` without gates). -/
noncomputable def poly (G : ArithCircuit) : MvPolynomial ℕ (ZMod 2) := G.polys.getLastD 0

/-- The size of the circuit: its number of gates. -/
def size (G : ArithCircuit) : ℕ := G.gates.length

/-- The degree of the circuit: the total degree of the polynomial it computes. -/
noncomputable def degree (G : ArithCircuit) : ℕ := G.poly.totalDegree

/-- All variables of the circuit are among `x₀, …, x_{N−1}`. -/
def VarsBelow (G : ArithCircuit) (N : ℕ) : Prop := ∀ i : ℕ, AGate.var i ∈ G.gates → i < N

/-- The value of the circuit on a Boolean assignment `x` (`true = 1`). -/
noncomputable def evalBool (G : ArithCircuit) (x : ℕ → Bool) : Bool :=
  decide (MvPolynomial.eval (fun i => if x i then (1 : ZMod 2) else 0) G.poly = 1)

/-- The description of the circuit as a bit string (number of gates, then each gate with a 2-bit
tag and its arguments in `encNat`). -/
def encode (G : ArithCircuit) : List Bool :=
  encNat G.gates.length ++ G.gates.flatMap fun g => match g with
    | .var i => [false, false] ++ encNat i
    | .const b => [false, true, b]
    | .add a b => [true, false] ++ encNat a ++ encNat b
    | .mul a b => [true, true] ++ encNat a ++ encNat b

end ArithCircuit

/-- A Boolean formula (fan-in-2 AND/OR, NOT, constants) over the input bits `x₀, x₁, …`. -/
inductive BFormula
  | var (i : ℕ)
  | const (b : Bool)
  | not (f : BFormula)
  | and (f g : BFormula)
  | or (f g : BFormula)

namespace BFormula

/-- The value of the formula on the bit string `x` (bits past the end read `0`). -/
def eval (x : List Bool) : BFormula → Bool
  | .var i => x.getD i false
  | .const b => b
  | .not f => !(f.eval x)
  | .and f g => f.eval x && g.eval x
  | .or f g => f.eval x || g.eval x

/-- The depth of the formula. -/
def depth : BFormula → ℕ
  | .var _ => 0
  | .const _ => 0
  | .not f => f.depth + 1
  | .and f g => max f.depth g.depth + 1
  | .or f g => max f.depth g.depth + 1

/-- The description of the formula as a bit string (prefix code). -/
def encode : BFormula → List Bool
  | .var i => [false, false] ++ encNat i
  | .const b => [false, true, b]
  | .not f => [true, false] ++ f.encode
  | .and f g => [true, true, false] ++ f.encode ++ g.encode
  | .or f g => [true, true, true] ++ f.encode ++ g.encode

end BFormula

/-- The description of a multi-output formula (one formula per output bit). -/
def encodeFormulas (F : List BFormula) : List Bool :=
  encNat F.length ++ F.flatMap BFormula.encode

/-- The input of the wiring formula for the query `(i, g, j)`: layer `i`, gate `g`, child number `j`,
in fixed-width binary (`Nat.size d`, `log₂ w`, `Nat.size N` bits). -/
def wireQuery (d w N i g j : ℕ) : List Bool :=
  bitsFixed (Nat.size d) i ++ bitsFixed (Nat.log 2 w) g ++ bitsFixed (Nat.size N) j

/-- A child of a gate, read off the output bits of the wiring formula: `1` followed by the binary
index `a` of a gate of the previous layer (an input bit for layer 1) is the wire from `a`; `0`
followed by a bit `b` is the constant `b`. -/
def decodeChild : List Bool → ℕ ⊕ Bool
  | true :: rest => .inl (ofBitsLE rest)
  | false :: b :: _ => .inr b
  | _ => .inr false

/-- The child `(i, g, j)` given by the wiring formula `F`. -/
def child (F : List BFormula) (d w N i g j : ℕ) : ℕ ⊕ Bool :=
  decodeChild (F.map fun f => f.eval (wireQuery d w N i g j))

/-- The values of the layers of the `(d × w)`-circuit with universal gate `G`, wiring `F` and `N`
input bits on input `x`: layer `0` is the input; gate `g` of layer `i + 1` computes `G` on the `N`
values given by its children `(i + 1, g, j)`, `j < N` (a wire to a gate of layer `i`, or a
constant); a wire to a gate past the width of its layer reads `0`. -/
noncomputable def layerVal (G : ArithCircuit) (F : List BFormula) (d w N : ℕ) (x : List Bool) :
    ℕ → ℕ → Bool
  | 0 => fun a => x.getD a false
  | i + 1 => fun g => G.evalBool fun j =>
      if j < N then
        match child F d w N (i + 1) g j with
        | .inl a => if a < (if i = 0 then N else w) then layerVal G F d w N x i a else false
        | .inr b => b
      else false

/-- The output `C_N(x) ∈ {0,1}^w`: the values of the `w` gates of the last layer `d`. -/
noncomputable def circOut (G : ArithCircuit) (F : List BFormula) (d w N : ℕ) (x : List Bool) :
    List Bool :=
  (List.range w).map (layerVal G F d w N x d)

/-- The fan-in of gate `g` of layer `i`: the number of distinct gates of the previous layer that
are children of `g`. -/
noncomputable def fanIn (F : List BFormula) (d w N i g : ℕ) : ℕ :=
  ((List.range N).filterMap fun j => match child F d w N i g j with
    | .inl a => some a
    | .inr _ => none).dedup.length

/-- The constants hidden in Definition 6.1 of a highly uniform family: `Kp, kp` of the `Õ(T)` time
for printing `G`, `Kd` of the depth `O(log log w)` of the wiring formulas, and `Ku, ku` of the
polynomial time that prints the wiring formulas (P-uniformity). -/
structure UnifConsts where
  Kp : ℕ
  kp : ℕ
  Kd : ℕ
  Ku : ℕ
  ku : ℕ

/-- `{C_N : {0,1}^{ι(N)} → {0,1}^{w(N)}}` is computable by a highly uniform family of
`(d × w)`-circuits with `(∆, T)`-low-degree universal gates of fan-in `k`, with hidden constants `H`
(Chen, Doron, Ebtehaj, Tell, Targeted Samplers, STOC 2027 submission, manuscript sha256 599d0a59…,
Definition 6.1, footnote 32 and Remark 6.2, p.47). There are, for every index `N`, an arithmetic
circuit `G_N` over `F₂` and a multi-output wiring formula `F_N` such that:

1. *Circuit structure.* `C_N(x)` is the output of the circuit with `d(N)` layers of `w(N)` gates,
   each gate of layer `i` computing `G_N` on its children in layer `i − 1` (the input for `i = 1`)
   (`circOut`). `G_N` has `ι(N)` inputs (footnote 32: the wiring may fix some to constants), size at
   most `T(N)` and degree at most `∆(N)`, and one program prints its description on input `1^N` in
   time `Õ(T(N))`. Gates of layers `2, …, d` have fan-in at most `k(N)`; first-layer gates have
   unbounded fan-in.
2. *Uniformity.* The wiring `(i, g, j) ↦` the `j`-th child of gate `g` in layer `i` is computed by
   the formulas `F_N` of depth `O(log log w(N))`, which one program prints from `1^N` in polynomial
   time (P-uniform).

**Formalization Note** The family is indexed by `N` with input length `ι(N)` (`ι = id` in
Theorem 6.3; in Theorem 6.9 the index is `n` and the input length `n + r(n)`), and the uniform
programs receive `1^N` for the index. The degree is the total degree of the polynomial over `F₂`
that `G_N` computes; "size `T`" and "degree `∆`" are upper bounds. Layers are numbered `1, …, d`,
gates `0, …, w − 1`, children `0, …, ι(N) − 1`, written in fixed-width binary; a child is a gate of
the previous layer or a constant (`decodeChild`). The fan-in counts distinct children. `Õ(T)` is the
base `budget`; `O(log log w)` is `Kd · (⌊log₂ ⌊log₂ w⌋⌋ + 1)`; polynomial time is
`Ku · (N + 1)^{ku}`. -/
def IsHighlyUniformLDFamily (H : UnifConsts) (ι : ℕ → ℕ) (C : List Bool → List Bool)
    (d w k : ℕ → ℕ) (Δ : ℕ → ℝ) (T : ℕ → ℕ) : Prop :=
  ∃ (G : ℕ → ArithCircuit) (F : ℕ → List BFormula),
    (∀ N : ℕ, (G N).size ≤ T N ∧ ((G N).degree : ℝ) ≤ Δ N ∧ (G N).VarsBelow (ι N)) ∧
    (∃ P : Program, ∀ N : ℕ,
      P.RunsIn (Tapes.ofInput (List.replicate N true)) (budget H.Kp H.kp (T N) N)
        (some (G N).encode)) ∧
    (∀ N : ℕ, ∀ f ∈ F N, f.depth ≤ H.Kd * (Nat.log 2 (Nat.log 2 (w N)) + 1)) ∧
    (∃ P : Program, ∀ N : ℕ,
      P.RunsIn (Tapes.ofInput (List.replicate N true)) (H.Ku * (N + 1) ^ H.ku)
        (some (encodeFormulas (F N)))) ∧
    (∀ N i g : ℕ, 2 ≤ i → i ≤ d N → g < w N → fanIn (F N) (d N) (w N) (ι N) i g ≤ k N) ∧
    (∀ N : ℕ, ∀ x : List Bool, x.length = ι N →
      C x = circOut (G N) (F N) (d N) (w N) (ι N) x)

/-- `f : ℕ → ℕ` is computable in linear time: one program, on input `1^N`, outputs the binary
expansion of `f(N)` within time `O(N)` (Theorem 6.3, p.47).

**Formalization Note** Time is the base `budget` with `t = N` (linear up to constant and
polylogarithmic factors, the gap between the log-cost RAM and a word RAM). -/
def LinTimeComputable (f : ℕ → ℕ) : Prop :=
  ∃ (P : Program) (K k : ℕ), ∀ N : ℕ,
    P.RunsIn (Tapes.ofInput (List.replicate N true)) (budget K k N N) (some (Nat.bits (f N)))

end TargetedSamplers.Supplement


