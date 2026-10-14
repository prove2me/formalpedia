-- Prove2me | Definitions.Def_QAlgorithms_LearningSurvey_Ch05_Model
-- name    : QAlgorithms_LearningSurvey_Ch05_Model
-- status  : Definition
-- author  : @Goku
-- created : 2026-10-13T17:53:31.870694+00:00
-- url     : https://prove2.me/theorems/96cc5713-b846-48bb-a3fc-777c49a95395
-- title:
--   LearningSurvey Ch05: supporting definitions
-- statement:
--   A survey of quantum learning theory, §5: Time complexity
--
--   ## QAlgorithms.LearningSurvey.IsJunta
--
--   For any natural numbers $n,k$ and Boolean function $f$ on $n$-bit strings, this means there exists a finite set $S\subseteq\{0,\ldots,n-1\}$ of cardinality at most $k$ such that, for every pair of $n$-bit strings $x,y$, agreement $x_i=y_i$ at every $i\in S$ implies $f(x)=f(y)$. The selected set may be empty; $k=0$ therefore requires a constant function, every function satisfies the condition for $k\geq n$, and at $n=0$ every function satisfies it for every $k$.
--
--   ## QAlgorithms.LearningSurvey.regBit
--
--   For any natural number $N$, Boolean string $z$ of length $N$, and natural number $p$, this returns $z_p$ if $p<N$ and false otherwise. Thus every out-of-range index, including every index when $N=0$, returns false.
--
--   ## QAlgorithms.LearningSurvey.exInput
--
--   For any natural numbers $N,n,j$ and Boolean string $z$ of length $N$, this returns the Boolean string of length $n$ whose coordinate $i<n$ reads position $j(n+1)+i$ of $z$ when that position is below $N$, and is false otherwise. No restriction requires the entire example block to fit within $z$, and $n=0$ returns the unique empty string.
--
--   ## QAlgorithms.LearningSurvey.exLabel
--
--   For any natural numbers $N,n,j$ and Boolean string $z$ of length $N$, this is the bit at position $j(n+1)+n$ if that position is below $N$, and false otherwise. No condition requires $j$ to index an existing complete example block; when $n=0$ it reads position $j$ with the same false default.
--
--   ## QAlgorithms.LearningSurvey.juntaExamplesState
--
--   For arbitrary natural numbers $n,T,w$ and any Boolean function $f$ on $n$-bit strings, this defines a complex vector indexed by strings $z$ of length $T(n+1)+w$. Its amplitude is $((\sqrt 2)^n)^{-T}$ if all the last $w$ bits are false and, for each $0\leq j<T$, the bit at $j(n+1)+n$ equals $f$ applied to the $n$ bits at positions $j(n+1),\ldots,j(n+1)+n-1$; its amplitude is $0$ otherwise. No junta condition is imposed on $f$. If $T=0$, the vector is the basis vector with all $w$ bits false; if $n=0$, each example consists only of the label $f$ of the empty input and the nonzero amplitude is $1$; $w=0$ makes the final-bit condition vacuous.
--
--   ## QAlgorithms.LearningSurvey.tableHypothesis
--
--   For arbitrary natural numbers $n,T$, a Boolean mask $V$ on the $n$ coordinates, an indexed family of $T$ Boolean strings $x_j$ of length $n$, and any Boolean function $f$ on such strings, this defines a Boolean function $h$. On input $x$, search the indices $j=0,\ldots,T-1$ in increasing order for the first one satisfying $x_{j,i}=x_i$ at every coordinate $i$ for which $V_i$ is true; if found, return $h(x)=f(x_j)$, and otherwise return false. No equality on unselected coordinates or consistency of competing labels is required. For $T=0$ it always returns false; with no selected coordinates and $T>0$ it always returns $f(x_0)$, including when $n=0$.
--
--   ## QAlgorithms.LearningSurvey.JuntaHybridLearner
--
--   For each natural number $n$, this is the structure consisting of natural numbers $T_Q$, $\mathrm{anc}$, and $T_C$, a quantum circuit on $M=T_Q(n+1)+\mathrm{anc}$ wires using only Hadamard, T, and CNOT gates placed by injections of their one or two input wires into the $M$ wires, a Boolean circuit with $M$ input bits and $n$ outputs, and a proof that this Boolean circuit is well formed. The Boolean circuit consists of an ordered list of AND, OR, or NOT gates with natural-number input-wire indices and a natural-number output-wire index for each of the $n$ outputs; for gate index $k$, its first input is less than $M+k$, its second input is less than $M+k$ unless the gate is NOT, and every output index is less than $M$ plus the number of gates. There is no success or learning requirement among the fields, and all natural parameters may be $0$.
--
--   ## QAlgorithms.LearningSurvey.JuntaHybridLearner.cost
--
--   For any natural number $n$ and learner $L$ consisting of $T_Q,\mathrm{anc},T_C$, a Hadamard/T/CNOT circuit $c$ on $M=T_Q(n+1)+\mathrm{anc}$ wires, and a well-formed Boolean circuit $B$ with $M$ inputs and $n$ outputs, this is the natural number $|c|+M+|B|+T_C+\max_{z\in\{0,1\}^M}2^{|\{i<n:B(z)_i=\mathrm{true}\}|}$. Here $|c|$ is its number of gate applications, $|B|$ its number of Boolean gates, and $B(z)$ is obtained by starting with the input bits, evaluating the listed AND/OR/NOT gates in order and appending each result, then reading its output-wire indices; any unavailable wire would read as false. The maximum is over all bit strings, regardless of whether they occur as quantum outcomes; the indexing set has one element when $M=0$, and for $n=0$ the final maximum is $1$.
--
--   ## QAlgorithms.LearningSurvey.JuntaHybridLearner.successProb
--
--   For any natural number $n$, learner $L$ with natural $T_Q,\mathrm{anc},T_C$, Hadamard/T/CNOT circuit $c$ on $M=T_Q(n+1)+\mathrm{anc}$ wires and well-formed Boolean postprocessing circuit $B$ with $n$ outputs, any Boolean function $f$ on $n$-bit strings, and any real $\varepsilon$, this is $\sum_{z\in\{0,1\}^M}|(Uv)_z|^2(2^{nT_C})^{-1}\sum_{(x_j)\in(\{0,1\}^n)^{T_C}}\mathbf1\{2^{-n}|\{x:h_{z,(x_j)}(x)\ne f(x)\}|\leq\varepsilon\}$. The input vector $v$ has amplitude $2^{-nT_Q/2}$ precisely on strings with the last $\mathrm{anc}$ bits false and each of the $T_Q$ labels equal to $f$ on that block's $n$ input bits, and amplitude zero otherwise. $U$ applies the circuit's listed embedded gates in their listed temporal order, with the empty circuit giving identity. $B(z)$ is computed by sequential AND/OR/NOT evaluation with unavailable wires defaulting to false, and $h_{z,(x_j)}$ returns $f(x_j)$ for the first increasing sample index $j$ matching the input on all coordinates selected true by $B(z)$, or false if none matches. The inner sum counts all ordered sample families, including repeated strings. No junta hypothesis or restriction on $\varepsilon$ is imposed; $T_C=0$ gives one empty family and the constant-false hypothesis, $T_Q=0$ gives the all-false input basis vector, and $n=0$ is included.
-- source:
--   https://github.com/shiy1022/lean-quantum-complexity/blob/main/algorithms/QAlgorithms/LearningSurvey/Ch05.lean . Exact primary-source page locators are preserved in the declaration docstrings.

import Definitions.Def_QAlgorithms_Defs_Learning
/-!
# A survey of quantum learning theory, §5: Time complexity

S. Arunachalam, R. de Wolf, *A survey of quantum learning theory* (2017), cited "survey p.N"
(PDF pages).

This chunk's only node is Theorem 5.4 (Atıcı–Servedio, survey p.19: learning `k`-juntas under the
uniform distribution with `O(k log(k)/ε)` uniform quantum examples, `O(2^k)` uniform classical
examples and `O(nk log(k)/ε + 2^k log(1/ε))` time). As printed it cannot be stated: the time bound
has no cost model, the confidence is never given, and the classical-example count contradicts the
proof sketch. It is stated here as a corrected theorem, in the explicit cost model of the proof
sketch (the chunk-local definitions below); see the theorem's docstring.

Register layout of the quantum stage (chunk-local): `T` uniform quantum examples of `n + 1` qubits
each, followed by `w` ancillas in `|0⟩`. Example `j` occupies wires `j(n+1), …, j(n+1)+n`: wires
`j(n+1)+i` (`i < n`) hold `x_i`, wire `j(n+1)+n` holds the label `f(x)`.
-/

namespace QAlgorithms.LearningSurvey

/-- A Boolean function on `{0,1}^n` is a `k`-junta if it depends on at most `k` of its `n` input
bits (survey p.19: "functions that depend (possibly non-linearly) on at most `k` of the `n` input
bits"). -/
def IsJunta {n : ℕ} (f : Qubits n → Bool) (k : ℕ) : Prop :=
  ∃ S : Finset (Fin n), S.card ≤ k ∧ ∀ x y : Qubits n, (∀ i ∈ S, x i = y i) → f x = f y

/-- Bit `p` of a computational-basis string, `false` past its end (an index helper). -/
def regBit {N : ℕ} (z : Qubits N) (p : ℕ) : Bool :=
  if h : p < N then z ⟨p, h⟩ else false

/-- The input part `x` of the `j`-th example register (wires `j(n+1), …, j(n+1)+n−1`). -/
def exInput {N : ℕ} (n : ℕ) (z : Qubits N) (j : ℕ) : Qubits n :=
  fun i => regBit z (j * (n + 1) + (i : ℕ))

/-- The label qubit of the `j`-th example register (wire `j(n+1)+n`). -/
def exLabel {N : ℕ} (n : ℕ) (z : Qubits N) (j : ℕ) : Bool :=
  regBit z (j * (n + 1) + n)

/-- `T` uniform quantum examples of `f` followed by `w` ancillas in `|0⟩`: the state
`(∑_x 2^{-n/2} |x, f(x)⟩)^{⊗T} ⊗ |0^w⟩` (survey §3.2, pp.6–7, uniform `D`), in the register
layout of the module docstring. Its amplitude on a basis string is `2^{-nT/2}` if every label
qubit equals `f` of its input part and every ancilla is `0`, and `0` otherwise. -/
noncomputable def juntaExamplesState (n T w : ℕ) (f : Qubits n → Bool) :
    EuclideanSpace ℂ (Qubits (T * (n + 1) + w)) :=
  WithLp.toLp 2 fun z =>
    if (∀ p : Fin (T * (n + 1) + w), T * (n + 1) ≤ (p : ℕ) → z p = false) ∧
        (∀ j : Fin T, exLabel n z j = f (exInput n z j))
    then ((((Real.sqrt 2) ^ n)⁻¹ ^ T : ℝ) : ℂ) else 0

/-- The truth-table hypothesis of the proof sketch (survey p.19): given the variable set `V`
(as an indicator) and classical examples `(x_j, f(x_j))`, the hypothesis on `x` is the label of the
first example agreeing with `x` on `V`, and `false` if no example does. (The source fills unseen
and inconsistent cells "say with random values"; the first-seen label and the fixed value `false`
are such a choice.) -/
def tableHypothesis {n T : ℕ} (V : Fin n → Bool) (xs : Fin T → Qubits n) (f : Qubits n → Bool) :
    Qubits n → Bool :=
  fun x =>
    match (List.finRange T).find? (fun j => decide (∀ i, V i = true → xs j i = x i)) with
    | some j => f (xs j)
    | none => false

/-- A hybrid junta learner in the cost model of the proof sketch of Theorem 5.4 (survey p.19),
fixed here because the source states none:

1. a quantum stage: a circuit `circ` over the gate set `{H, T, CNOT}` acting on `TQ` uniform
   quantum examples and `anc` ancillas, after which every qubit is measured in the computational
   basis;
2. a classical bit-level stage: a well-formed Boolean circuit `post` (AND/OR/NOT gates) mapping the
   measurement outcome to the indicator of a variable set `V ⊆ [n]`;
3. a table stage: `TC` uniform classical examples are read and the hypothesis is
   `tableHypothesis V`.

The time is `cost`: one unit per quantum gate, per measured qubit, per Boolean gate, per classical
example (reading it and writing its label into the table cell indexed by its `V`-bits, a
unit-cost step), and per table cell (`2^{|V|}`, worst case over the outcomes). -/
structure JuntaHybridLearner (n : ℕ) where
  TQ : ℕ
  anc : ℕ
  circ : Circuit htcxGateSet (TQ * (n + 1) + anc)
  post : BoolCircuit (TQ * (n + 1) + anc) n
  post_wf : post.WellFormed
  TC : ℕ

/-- The time of a hybrid junta learner in the cost model of `JuntaHybridLearner`. -/
def JuntaHybridLearner.cost {n : ℕ} (L : JuntaHybridLearner n) : ℕ :=
  L.circ.size + (L.TQ * (n + 1) + L.anc) + L.post.size + L.TC +
    Finset.univ.sup fun z : Qubits (L.TQ * (n + 1) + L.anc) => 2 ^ hammingWeight (L.post.eval z)

/-- The probability that the learner outputs a hypothesis of error at most `ε` under the uniform
distribution on `{0,1}^n`: the quantum stage's outcome `z` has probability
`|⟨z| circ |examples⟩|²`, and the `TC` classical examples are independent and uniform. -/
noncomputable def JuntaHybridLearner.successProb {n : ℕ} (L : JuntaHybridLearner n)
    (f : Qubits n → Bool) (ε : ℝ) : ℝ :=
  ∑ z : Qubits (L.TQ * (n + 1) + L.anc),
    prob (act L.circ.unitary (juntaExamplesState n L.TQ L.anc f)) z *
      ((((2 : ℝ) ^ n) ^ L.TC)⁻¹ * ∑ xs : Fin L.TC → Qubits n,
        if Learning.pacError (Learning.uniformDist (Qubits n)) f
            (tableHypothesis (L.post.eval z) xs f) ≤ ε then (1 : ℝ) else 0)


end QAlgorithms.LearningSurvey


