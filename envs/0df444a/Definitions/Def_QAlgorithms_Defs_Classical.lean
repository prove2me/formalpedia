-- Prove2me | Definitions.Def_QAlgorithms_Defs_Classical
-- name    : QAlgorithms_Defs_Classical
-- status  : Definition
-- author  : @Goku
-- created : 2026-10-13T17:26:00.932474+00:00
-- url     : https://prove2.me/theorems/aefb77e2-c814-4342-9006-e7c8683b865c
-- title:
--   Classical algorithms (shared definition layer)
-- statement:
--   Classical algorithms (shared definition layer)
--
--   ### QAlgorithms.DecisionTree
--
--   Given three types — an index set $\iota$, an answer set $\kappa$, and an output set $\alpha$ — a decision tree is built inductively in exactly two ways:
--
--   - **A leaf** labelled by an output $a \in \alpha$.
--   - **A node** labelled by an index $i \in \iota$, together with a child function assigning to every possible answer $b \in \kappa$ a decision tree $\mathrm{next}(b)$.
--
--   Because the definition is inductive, every such tree is well-founded: every path from the root eventually reaches a leaf. However, a node has one child per element of $\kappa$, so the tree is infinitely branching when $\kappa$ is infinite. Path lengths need not be uniformly bounded. No restriction prevents the same index from appearing at several nodes along a path.
--
--   ### QAlgorithms.DecisionTree.eval
--
--   Let $t$ be a decision tree over $(\iota,\kappa,\alpha)$ and let $x : \iota \to \kappa$ be an input. The value $t(x) \in \alpha$ is defined recursively:
--
--   - If $t$ is a leaf labelled $a$, then $t(x) = a$.
--   - If $t$ is a node with index $i$ and children $\mathrm{next}$, then $t(x) = \mathrm{next}(x_i)(x)$. That is, read the input's entry $x_i$, move to the corresponding child, and continue.
--
--   The output is the label of the leaf reached along the path determined by $x$.
--
--   ### QAlgorithms.DecisionTree.queries
--
--   Let $t$ be a decision tree and $x : \iota \to \kappa$ an input. The number of queries $q_t(x) \in \mathbb{N}$ is defined recursively:
--
--   - For a leaf, $q_t(x) = 0$.
--   - For a node with index $i$ and children $\mathrm{next}$, $q_t(x) = 1 + q_{\mathrm{next}(x_i)}(x)$.
--
--   Thus $q_t(x)$ is the number of internal nodes on the path that $x$ follows from the root to a leaf. Repeated queries to the same index along that path are each counted.
--
--   ### QAlgorithms.DecisionTree.MakesAtMost
--
--   For a decision tree $t$ over $(\iota,\kappa,\alpha)$ and a bound $T \in \mathbb{N}$, "$t$ makes at most $T$ queries" means
--
--   $$
--   \forall x : \iota \to \kappa, \quad q_t(x) \le T,
--   $$
--
--   where $q_t(x)$ is the number of nodes on the evaluation path of $x$, as defined above. This is a worst-case bound over all inputs $x$; it constrains only paths actually followed by some input.
--
--   There is one degenerate case. If $\iota$ is nonempty and $\kappa$ is empty, there are no inputs $x$, and the condition holds vacuously for every $T$.
--
--   ### QAlgorithms.RandDecisionTree
--
--   A randomized decision tree over $(\iota,\kappa,\alpha)$ is a probability mass function $R$ on the type of decision trees over $(\iota,\kappa,\alpha)$. This means an assignment of probabilities $R(t) \in [0,1]$ to trees $t$, whose sum over all trees equals $1$, so that only countably many trees have positive probability. There are no further constraints, such as finite support or a query bound.
--
--   ### QAlgorithms.RandMakesAtMost
--
--   For a randomized decision tree $R$ (a probability mass function on decision trees) and a bound $T \in \mathbb{N}$, "$R$ makes at most $T$ queries" means:
--
--   $$
--   \forall t \text{ with } R(t) > 0, \quad \forall x : \iota \to \kappa, \quad q_t(x) \le T .
--   $$
--
--   That is, every tree that has positive probability under $R$ makes at most $T$ queries on every input. This is a worst-case bound, not an expected-value bound. Trees of probability zero are unconstrained. As in the deterministic case, the condition is vacuous on the input side when there are no inputs, i.e. when $\iota$ is nonempty and $\kappa$ is empty.
--
--   ### QAlgorithms.successProb
--
--   This defines a real number $\mathrm{successProb}(R, x, a)$ for:
--
--   - arbitrary types $\iota$ (query positions), $\kappa$ (answer values) and $\alpha$ (outputs);
--   - a randomized decision tree $R$, which is a probability mass function (a discrete probability distribution) on the set of deterministic decision trees over $(\iota, \kappa, \alpha)$;
--   - an input $x : \iota \to \kappa$;
--   - a candidate output $a \in \alpha$.
--
--   A deterministic decision tree is either a leaf labelled by some $a \in \alpha$, or a node labelled by a position $i \in \iota$ with one child subtree for each $c \in \kappa$. Evaluating a tree $t$ on $x$, written $t(x)$, works as follows: a leaf returns its label, and a node labelled $i$ recurses into the child indexed by $x_i$.
--
--   The definition pushes $R$ forward along the map $t \mapsto t(x)$, takes the mass this output distribution assigns to $a$, and converts it from an extended non-negative real to an ordinary real:
--
--   $$
--   \mathrm{successProb}(R,x,a) \;=\; \Pr_{t \sim R}\big[\,t(x) = a\,\big] \;=\; \sum_{t \,:\, t(x)=a} R(t).
--   $$
--
--   Since PMF masses are at most $1$, this is a genuine probability in $[0,1]$; the conversion to reals loses nothing.
--
--   ### QAlgorithms.BoolOp
--
--   This is a data type with exactly three distinct values: $\mathsf{and}$, $\mathsf{or}$ and $\mathsf{not}$. They name the three kinds of classical Boolean gate. The type carries no further structure.
--
--   ### QAlgorithms.BoolGate
--
--   A Boolean gate is a record of three fields:
--
--   - an operation $\mathrm{op} \in \{\mathsf{and}, \mathsf{or}, \mathsf{not}\}$;
--   - two natural numbers $a$ and $b$, intended as indices of the gate's input wires.
--
--   There are no constraints. Both indices are present even for a $\mathsf{not}$ gate, where $b$ is ignored by the evaluation function below. The indices may be any natural numbers, including ones that do not refer to an existing wire.
--
--   ### QAlgorithms.BoolCircuit
--
--   For natural numbers $n$ (nominal number of inputs) and $m$ (number of outputs), a Boolean circuit $C$ consists of:
--
--   - a finite list $\mathrm{gates} = (g_0, g_1, \dots, g_{L-1})$ of Boolean gates, where $L \ge 0$ and $L = 0$ is allowed;
--   - an output map $\mathrm{outputs} : \{0,\dots,m-1\} \to \mathbb{N}$, assigning to each output position $j$ a wire index.
--
--   The structure imposes no constraints. Nothing ties the gate indices or the output indices to $n$ or to $L$; such constraints appear only in `WellFormed`. The parameter $n$ does not occur in any field and serves only as a label.
--
--   ### QAlgorithms.BoolCircuit.WellFormed
--
--   For a Boolean circuit $C$ with parameters $n, m$, gate list $(g_0,\dots,g_{L-1})$ and output map $\mathrm{outputs}$, the proposition $\mathrm{WellFormed}(C)$ holds exactly when both of the following hold:
--
--   1. **Gate inputs point backwards.** For every gate index $k \in \{0,\dots,L-1\}$:
--      - the first input index satisfies $a(g_k) < n + k$; and
--      - either $\mathrm{op}(g_k) = \mathsf{not}$, or the second input index satisfies $b(g_k) < n + k$.
--
--      So a gate may only read wires $0,\dots,n+k-1$. These are the $n$ input wires and the outputs of the earlier gates $g_0,\dots,g_{k-1}$. For $\mathsf{not}$ gates, $b$ is unconstrained.
--
--   2. **Outputs point at existing wires.** For every output position $j \in \{0,\dots,m-1\}$, $\mathrm{outputs}(j) < n + L$.
--
--   Edge cases:
--
--   - If $L = 0$, condition 1 is vacuous.
--   - If $m = 0$, condition 2 is vacuous.
--   - If $n = 0$ and $L \ge 1$, the first gate would need $a(g_0) < 0$, which is impossible. So with $n = 0$ a well-formed circuit has no gates, and then (if $m \ge 1$) the condition $\mathrm{outputs}(j) < 0$ also fails. Hence for $n = 0$ only $L = 0, m = 0$ is well-formed.
--
--   ### QAlgorithms.BoolGate.value
--
--   Given a Boolean gate $g$ with operation $\mathrm{op}$ and indices $a, b$, and a finite list $v = (v_0, v_1, \dots)$ of Booleans, this returns one Boolean.
--
--   Write $\tilde v_i$ for the $i$-th entry of $v$ (0-based) if $i$ is less than the length of $v$, and $\tilde v_i = \mathsf{false}$ otherwise. Then
--
--   $$
--   \mathrm{value}(g, v) =
--   \begin{cases}
--   \tilde v_a \wedge \tilde v_b & \text{if } \mathrm{op} = \mathsf{and},\\
--   \tilde v_a \vee \tilde v_b & \text{if } \mathrm{op} = \mathsf{or},\\
--   \neg\, \tilde v_a & \text{if } \mathrm{op} = \mathsf{not}.
--   \end{cases}
--   $$
--
--   An out-of-range index silently reads $\mathsf{false$ rather than being an error. In particular, a $\mathsf{not}$ gate with out-of-range $a$ outputs $\mathsf{true}$.
--
--   ### QAlgorithms.BoolCircuit.wireValues
--
--   For a Boolean circuit $C$ with parameters $n, m$ and gate list $(g_0, \dots, g_{L-1})$, and an input $x = (x_0,\dots,x_{n-1}) \in \{\mathsf{false},\mathsf{true}\}^n$, this returns a list of Booleans of length $n + L$. It is built as follows:
--
--   - Start with the list $w^{(0)} = (x_0, \dots, x_{n-1})$.
--   - For $k = 0, 1, \dots, L-1$ in order, set
--     $$
--     w^{(k+1)} = w^{(k)} \text{ with } \mathrm{value}(g_k, w^{(k)}) \text{ appended at the end.}
--     $$
--   - The result is $w^{(L)}$.
--
--   Here $\mathrm{value}$ is the gate evaluation above: it reads entries of the current list by index and returns $\mathsf{false}$ for any out-of-range index. So entry $n+k$ of the result is the value of gate $g_k$, computed from the wires $0,\dots,n+k-1$ that existed at that point.
--
--   No well-formedness is assumed. A gate referencing an index $\ge n+k$ simply reads $\mathsf{false}$ there.
--
--   ### QAlgorithms.BoolCircuit.eval
--
--   For a Boolean circuit $C$ with parameters $n, m$ and an input $x \in \{\mathsf{false},\mathsf{true}\}^n$, this returns a function from output positions $\{0,\dots,m-1\}$ to Booleans. For each $j$:
--
--   - if $\mathrm{outputs}(j) < n + L$, the output is entry number $\mathrm{outputs}(j)$ (0-based) of the wire-value list $\mathrm{wireValues}(C, x)$;
--   - otherwise the output is $\mathsf{false}$.
--
--   Here $L$ is the number of gates, so $\mathrm{wireValues}(C,x)$ has length $n+L$. Out-of-range output indices silently give $\mathsf{false}$; well-formedness is not assumed.
--
--   ### QAlgorithms.BoolCircuit.size
--
--   For a Boolean circuit $C$ (with any parameters $n, m$), $\mathrm{size}(C)$ is the length $L$ of its gate list, a natural number. It counts only gates. Input wires and output assignments are not counted, and $L = 0$ is possible.
--
--   ### QAlgorithms.iidProb
--
--   The inputs are:
--
--   - a finite type $\alpha$;
--   - a probability mass function $\mu$ on $\alpha$;
--   - a natural number $k$;
--   - a predicate $E$ on length-$k$ sequences $\ell = (\ell_0,\dots,\ell_{k-1}) \in \alpha^k$.
--
--   The value is an extended non-negative real, computed as
--
--   $$
--   \mathrm{iidProb}(\mu, k, E) \;=\; \sum_{\ell \in \alpha^k} \begin{cases} \displaystyle\prod_{i=0}^{k-1} \mu(\ell_i) & \text{if } E(\ell),\\[4pt] 0 & \text{otherwise.}\end{cases}
--   $$
--
--   This is the probability that $E$ holds for $k$ independent samples drawn from $\mu$. The predicate $E$ need not be decidable; the case split is made classically.
--
--   Edge cases:
--
--   - For $k = 0$ there is exactly one (empty) sequence, and its empty product is $1$. So the value is $1$ if $E$ holds of the empty sequence and $0$ otherwise.
--   - If $\alpha$ is empty, $\mu$ cannot exist, since a PMF needs total mass $1$.
--
--   ### QAlgorithms.expectedStoppingTime
--
--   The inputs are:
--
--   - a finite type $\alpha$;
--   - a probability mass function $\mu$ on $\alpha$;
--   - a family of predicates $\mathrm{stop}_j$, one for each $j \in \mathbb{N}$, where $\mathrm{stop}_j$ applies to length-$j$ sequences in $\alpha^j$.
--
--   The value is the extended non-negative real
--
--   $$
--   \mathrm{expectedStoppingTime}(\mu, \mathrm{stop}) \;=\; \sum_{k=0}^{\infty} \mathrm{iidProb}\Big(\mu,\, k,\; \ell \mapsto \forall j \in \{0,1,\dots,k\}:\ \neg\,\mathrm{stop}_j(\ell_0,\dots,\ell_{j-1})\Big).
--   $$
--
--   So the $k$-th term is the probability, under $k$ i.i.d. samples $\ell_0,\dots,\ell_{k-1}$ from $\mu$, that none of the prefixes satisfy the stopping predicate of their length. The prefixes checked are those of length $0,1,\dots,k$; this includes the empty prefix and the full sequence. Here $\mathrm{iidProb}$ is as defined above: the sum, over all $\ell \in \alpha^k$ satisfying the event, of $\prod_i \mu(\ell_i)$.
--
--   The infinite sum is taken in $[0,\infty]$, so it always exists and may equal $+\infty$.
--
--   Edge cases:
--
--   - If $\mathrm{stop}_0$ holds of the empty sequence, every term is $0$ and the value is $0$.
--   - If no $\mathrm{stop}_j$ ever holds, every term is $1$ and the value is $+\infty$.
-- source:
--   https://github.com/shiy1022/lean-quantum-complexity/blob/main/algorithms/QAlgorithms/Defs/Classical.lean . Exact primary-source page locators are preserved in the declaration docstrings.

import Definitions.Def_QAlgorithms_Defs_Circuit
/-!
# Classical algorithms (shared definition layer)

Deterministic and randomized classical query algorithms, classical Boolean circuits, and the
expected number of i.i.d. samples until a stopping rule fires.
-/

namespace QAlgorithms

open scoped ENNReal

/-- de Wolf p.26 (§2.2), p.37 (§3.3.2); Childs p.30 (§5.3): a deterministic adaptive classical
query algorithm on inputs `x : ι → κ`, as a decision tree: at a `node` it queries position `i`
and branches on the answer `x i`; at a `leaf` it outputs `a`. -/
inductive DecisionTree (ι κ α : Type*) where
  /-- Stop and output `a`. -/
  | leaf (a : α)
  /-- Query position `i`, continue with `next (x i)`. -/
  | node (i : ι) (next : κ → DecisionTree ι κ α)

/-- The output of the decision tree on input `x`. -/
def DecisionTree.eval {ι κ α : Type*} : DecisionTree ι κ α → (ι → κ) → α
  | .leaf a, _ => a
  | .node i next, x => (next (x i)).eval x

/-- The number of queries made on input `x` (the length of the path `x` follows). -/
def DecisionTree.queries {ι κ α : Type*} : DecisionTree ι κ α → (ι → κ) → ℕ
  | .leaf _, _ => 0
  | .node i next, x => 1 + (next (x i)).queries x

/-- de Wolf p.37: the algorithm makes at most `T` queries on every input (on every path). -/
def DecisionTree.MakesAtMost {ι κ α : Type*} (t : DecisionTree ι κ α) (T : ℕ) : Prop :=
  ∀ x : ι → κ, t.queries x ≤ T

/-- de Wolf p.37 (§3.3.2: "the behavior of the randomized algorithm is an average over a number of
deterministic algorithms"), p.26, p.142 (Definition 3): a randomized classical query algorithm,
a probability distribution over deterministic decision trees. -/
abbrev RandDecisionTree (ι κ α : Type*) := PMF (DecisionTree ι κ α)

/-- Every deterministic algorithm in the support makes at most `T` queries on every input. -/
def RandMakesAtMost {ι κ α : Type*} (R : RandDecisionTree ι κ α) (T : ℕ) : Prop :=
  ∀ t ∈ R.support, t.MakesAtMost T

/-- The probability (over the algorithm's randomness) that the randomized algorithm `R` outputs
`a` on input `x`. -/
noncomputable def successProb {ι κ α : Type*} (R : RandDecisionTree ι κ α) (x : ι → κ) (a : α) :
    ℝ :=
  ((R.map fun t => t.eval x) a).toReal

/-- de Wolf p.25 (§2.1.1): the gate types of a classical Boolean circuit. -/
inductive BoolOp where
  | and
  | or
  | not

/-- A gate of a Boolean circuit, reading the wires with indices `a` and `b` (`b` is ignored by
`not`). -/
structure BoolGate where
  /-- The gate type. -/
  op : BoolOp
  /-- First input wire. -/
  a : ℕ
  /-- Second input wire (unused by `not`). -/
  b : ℕ

/-- de Wolf p.25 (§2.1.1): a Boolean circuit with `n` inputs and `m` outputs, as a straight-line
program over AND, OR, NOT gates: wires `0, …, n-1` carry the inputs and wire `n + k` carries the
output of gate `k`, which may only read earlier wires (`BoolCircuit.WellFormed`); `outputs j` is
the wire of output `j`. -/
structure BoolCircuit (n m : ℕ) where
  /-- The gates, in topological order. -/
  gates : List BoolGate
  /-- The designated output wires. -/
  outputs : Fin m → ℕ

/-- Every gate reads only wires defined before it, and every output is a defined wire. -/
def BoolCircuit.WellFormed {n m : ℕ} (C : BoolCircuit n m) : Prop :=
  (∀ k : Fin C.gates.length, (C.gates.get k).a < n + k ∧
    ((C.gates.get k).op = BoolOp.not ∨ (C.gates.get k).b < n + k)) ∧
  ∀ j : Fin m, C.outputs j < n + C.gates.length

/-- The value of one gate given the values of the wires defined so far. -/
def BoolGate.value (g : BoolGate) (vals : List Bool) : Bool :=
  match g.op with
  | .and => vals.getD g.a false && vals.getD g.b false
  | .or => vals.getD g.a false || vals.getD g.b false
  | .not => !vals.getD g.a false

/-- The values of all wires on input `x`. -/
def BoolCircuit.wireValues {n m : ℕ} (C : BoolCircuit n m) (x : Fin n → Bool) : List Bool :=
  C.gates.foldl (fun vals g => vals ++ [g.value vals]) (List.ofFn x)

/-- The output of the circuit on input `x`. -/
def BoolCircuit.eval {n m : ℕ} (C : BoolCircuit n m) (x : Fin n → Bool) : Fin m → Bool :=
  fun j => (C.wireValues x).getD (C.outputs j) false

/-- de Wolf p.25: the size of a Boolean circuit, its number of AND/OR/NOT gates. -/
def BoolCircuit.size {n m : ℕ} (C : BoolCircuit n m) : ℕ :=
  C.gates.length

/-- The probability under `k` i.i.d. samples from `μ` that the sample sequence satisfies `E`. -/
noncomputable def iidProb {α : Type*} [Fintype α] (μ : PMF α) (k : ℕ) (E : (Fin k → α) → Prop) :
    ℝ≥0∞ :=
  open Classical in
  ∑ l : Fin k → α, if E l then ∏ i, μ (l i) else 0

/-- de Wolf p.36 (§3.2): the expected number `E[τ]` of i.i.d. samples from `μ` until the stopping
rule fires, where `τ` is the least `j` such that the first `j` samples satisfy `stop j`; computed
as `E[τ] = Σ_{k ≥ 0} Pr[τ > k]`, which is `⊤` when the rule fires with probability `< 1`.
Used for "the expected number of runs until `n − 1` independent equations". -/
noncomputable def expectedStoppingTime {α : Type*} [Fintype α] (μ : PMF α)
    (stop : (j : ℕ) → (Fin j → α) → Prop) : ℝ≥0∞ :=
  ∑' k : ℕ, iidProb μ k fun l => ∀ (j : ℕ) (h : j ≤ k), ¬ stop j (fun i => l (Fin.castLE h i))

/-! ### Sanity tests -/

example : (DecisionTree.node 0 (fun b : Bool => DecisionTree.leaf (α := Bool) (ι := Fin 2) b)).eval
    ![true, false] = true := rfl

example : (DecisionTree.node 1 (fun b : Bool => DecisionTree.leaf (α := Bool) (ι := Fin 2) b)).queries
    ![true, false] = 1 := rfl

/-- A one-gate circuit computing AND of two inputs. -/
example : (⟨[⟨BoolOp.and, 0, 1⟩], fun _ => 2⟩ : BoolCircuit 2 1).eval ![true, true] 0 = true ∧
    (⟨[⟨BoolOp.and, 0, 1⟩], fun _ => 2⟩ : BoolCircuit 2 1).eval ![true, false] 0 = false := by
  decide

/-- A rule that fires immediately (on the empty prefix) has expected stopping time `0`. -/
example {α : Type*} [Fintype α] (μ : PMF α) : expectedStoppingTime μ (fun _ _ => True) = 0 := by
  refine ENNReal.tsum_eq_zero.2 fun k => ?_
  refine Finset.sum_eq_zero fun l _ => ?_
  rw [if_neg]
  intro h
  exact h 0 (Nat.zero_le k) trivial

end QAlgorithms


