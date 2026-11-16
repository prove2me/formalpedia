-- Prove2me | Definitions.Def_MetricMSO_Supplement_NSO
-- name    : MetricMSO_Supplement_NSO
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T01:58:42.880245+00:00
-- url     : https://prove2.me/theorems/9d91b9d9-09a8-4ed9-a0d9-de4dc584df5c
-- title:
--   Nearest-Set Optimization: instances, feasibility, objective, representations
-- statement:
--   An instance of **Nearest-Set Optimization** (§6.3) consists of a connected nonempty unweighted graph $G$ on $n$ vertices, a candidate set $F\subseteq V(G)$, a rational opening cost $o_s$ for each $s\in F$, a cost table $h_v:\{0,\dots,n-1\}\to\mathbb Q\cup\{+\infty\}$ for each vertex $v$, and optionally a constraint $|S|=p$ or $|S|\le p$ with $p$ in binary.
--
--   A set $S$ is **feasible** if $S\ne\emptyset$, $S\subseteq F$, $h_v(d_G(v,S))<+\infty$ for every $v$ (infinite costs are forbidden distances), the cardinality constraint holds, and, when a condition $\psi(S)\in\mathrm{CMSO}_2[\mathrm{SP},\mathrm{EqGC}]$ is imposed, $G\models\psi(S)$. The objective is
--
--   $$\sum_{s\in S}o_s+\sum_{v\in V(G)}h_v\big(d_G(v,S)\big),$$
--
--   minimized, or maximized in the maximization variant.
--
--   The tables may be given "in any fixed representation from which all table entries can be computed in time polynomial in the input length": a representation is a fixed machine $E$ and exponent $k$ such that $E$ computes every entry $h_v(d)$ from the description $\tau$ within $(N+1)^k$ steps, $N$ the input length. Explicit tables are one representation. Correct answers: optimum value and an optimal set (or "infeasible"), the number of feasible sets, and the number of optimum sets.
-- source:
--   Chakraborty, Ordyniak, Siebertz, Model Checking for Metric Extensions of MSO (arXiv:2610.41974, sha256 ad3c5863…), §6.3, p.42 (PDF 44)

import Mathlib
import Definitions.Def_ExponomialAssortment_FPTAS_Machine
import Definitions.Def_HMBinPacking_OutputsWithin
import Definitions.Def_MetricMSO_encodeInput
import Definitions.Def_MetricMSO_Supplement_XSat

set_option autoImplicit false

namespace MetricMSO.Supplement

open MetricMSO
open ExponomialAssortment.FPTAS (encodeNat encodeInt encodeRat)
open HMBinPacking (OutputsWithin)

/-- The optional cardinality constraint of Nearest-Set Optimization: none, `|S| = p`, or
`|S| ≤ p`, with `p` a nonnegative integer given with the input. -/
inductive CardBound : Type
  | none
  | eq (p : ℕ)
  | le (p : ℕ)

/-- The cardinality constraint holds for a set of size `k`. -/
def CardBound.Holds : CardBound → ℕ → Prop
  | .none, _ => True
  | .eq p, k => k = p
  | .le p, k => k ≤ p

/-- **An instance of Nearest-Set Optimization** (§6.3, p.42 (PDF 44)): "a connected nonempty
unweighted graph G, a candidate set F ⊆ V(G), a rational opening cost o_s for each s ∈ F, and a
cost table h_v : {0, . . . , n − 1} → Q ∪ {+∞} for each vertex v, where n := |V(G)|", and optionally
"|S| = p or |S| ≤ p for a nonnegative integer p given with the input".

* `G` on `Fin n`; `F` the candidate set; `o s` the opening cost (used for `s ∈ F` only);
* `h v d ∈ ℚ ∪ {+∞}` (`WithTop ℚ`) the cost table (only the entries `d < n` are used);
* `τ` the binary description of the cost tables in the chosen representation ("Instead of explicit
  tables, we may use any fixed representation from which all table entries can be computed in time
  polynomial in the input length"); the link between `τ` and `h` is `Represents` below;
* `card` the optional cardinality constraint. -/
structure NSOInstance where
  n : ℕ
  G : SimpleGraph (Fin n)
  F : Finset (Fin n)
  o : Fin n → ℚ
  h : Fin n → ℕ → WithTop ℚ
  τ : List Bool
  card : CardBound

namespace NSOInstance

/-- The instance seen as a plain graph (no input predicate), on which the condition `ψ(S)` is
evaluated. -/
def graphInst (J : NSOInstance) : Instance :=
  ⟨J.n, J.G, 0, fun j => j.elim0, 0, fun j => j.elim0, fun j => j.elim0⟩

/-- The distance `d_G(v, S)` as a natural number (finite for a nonempty `S` in a connected graph). -/
noncomputable def d (J : NSOInstance) (v : Fin J.n) (S : Finset (Fin J.n)) : ℕ :=
  (distSet J.G v S).toNat

/-- **Feasible sets** (§6.3, p.42): "We seek a nonempty set S ⊆ F … We treat +∞ as a forbidden
distance in both the minimization and maximization variants, and we may also require |S| = p or
|S| ≤ p"; with a condition `ψ = some φ`, also `G ⊨ φ(S)` ("We may also impose a CMSO2[SP, EqGC]
condition ψ(S)"). -/
def Feasible (J : NSOInstance) (ψ : Option Formula) (S : Finset (Fin J.n)) : Prop :=
  S.Nonempty ∧ S ⊆ J.F ∧ (∀ v, J.h v (J.d v S) ≠ ⊤) ∧ J.card.Holds S.card ∧
    ∀ φ, ψ = some φ → Sat J.graphInst ⟨[], [], [S], []⟩ φ

/-- **The objective** `Σ_{s∈S} o_s + Σ_{v∈V(G)} h_v(d_G(v, S))` (§6.3, p.42); every table entry used
is finite on a feasible set. -/
noncomputable def cost (J : NSOInstance) (S : Finset (Fin J.n)) : ℚ :=
  ∑ s ∈ S, J.o s + ∑ v, (J.h v (J.d v S)).untopD 0

/-- The feasible sets of minimum objective. -/
def MinFeas (J : NSOInstance) (ψ : Option Formula) : Set (Finset (Fin J.n)) :=
  {S | J.Feasible ψ S ∧ ∀ S', J.Feasible ψ S' → J.cost S ≤ J.cost S'}

/-- The feasible sets of maximum objective (the maximization variant). -/
def MaxFeas (J : NSOInstance) (ψ : Option Formula) : Set (Finset (Fin J.n)) :=
  {S | J.Feasible ψ S ∧ ∀ S', J.Feasible ψ S' → J.cost S' ≤ J.cost S}

end NSOInstance

/-- Code of a cost in `ℚ ∪ {+∞}`: `[false]` for `+∞`, `true` followed by the published binary code
of the rational number otherwise. -/
def encodeCost : WithTop ℚ → List Bool
  | ⊤ => [false]
  | (q : ℚ) => true :: encodeRat q

/-- Code of the cardinality constraint. -/
def CardBound.encode : CardBound → List Bool
  | .none => encodeNat 0
  | .eq p => encodeNat 1 ++ encodeNat p
  | .le p => encodeNat 2 ++ encodeNat p

open Classical in
/-- **The binary input of a Nearest-Set Optimization task** (the total input length `N` "includes
the opening costs and the cost tables, or their chosen representation"): the task index, the graph
(published `encodeGraph`), the `n` membership bits of `F`, the binary opening costs of the
candidates (by increasing vertex), the length of `τ` and `τ` itself, the cardinality constraint,
and the code of the condition (`[false]` for none, `true` and the formula code otherwise). -/
noncomputable def nsoInput (task : Task) (J : NSOInstance) (ψ : Option Formula) : List Bool :=
  encodeNat task.index ++ encodeGraph J.G ++
  (List.ofFn fun v : Fin J.n => decide (v ∈ J.F)) ++
  (List.ofFn fun v : Fin J.n => if v ∈ J.F then encodeRat (J.o v) else []).flatten ++
  encodeNat J.τ.length ++ J.τ ++ J.card.encode ++
  (match ψ with
    | none => [false]
    | some φ => true :: φ.encode)

/-- **A representation of the cost tables computable in polynomial time** ("any fixed
representation from which all table entries can be computed in time polynomial in the input
length", §6.3, p.42): the fixed machine `E`, started on `bin(v) ++ bin(d) ++ τ`, outputs the code of
the entry `h_v(d)` within `(N + 1)^k` steps for every vertex `v` and every `d < n`, where `N` is
the length of the instance's input. Explicit tables are one such representation. -/
def Represents (E : Turing.TM2ComputableAux Bool Bool) (k : ℕ) (J : NSOInstance) (N : ℕ) : Prop :=
  ∀ (v : Fin J.n) (d : ℕ), d < J.n →
    OutputsWithin E (encodeNat v ++ encodeNat d ++ J.τ) (encodeCost (J.h v d)) ((N + 1) ^ k)

open Classical in
/-- Binary code of a selected set: its `n` membership bits. -/
noncomputable def encodeSet {n : ℕ} (S : Finset (Fin n)) : List Bool :=
  List.ofFn fun v : Fin n => decide (v ∈ S)

open Classical in
/-- **Correct answers of Nearest-Set Optimization** (§6.3, p.42; same conventions as
`MetricMSO.CorrectAnswer`):
* `minimize` (`maximize`): `[false]` if no set is feasible; otherwise `true`, the binary optimum
  value and the code of an optimal set;
* `count`: the number of feasible sets; `countMin` (`countMax`): the number of optimum sets of the
  minimization (maximization) variant, `0` when no set is feasible;
* `decide` (not used by Theorem 6.5): whether a feasible set exists. -/
noncomputable def NSOCorrect (task : Task) (J : NSOInstance) (ψ : Option Formula)
    (out : List Bool) : Prop :=
  match task with
  | .decide => out = [decide (∃ S, J.Feasible ψ S)]
  | .minimize =>
      ((∀ S, ¬ J.Feasible ψ S) ∧ out = [false]) ∨
      ∃ S ∈ J.MinFeas ψ, out = true :: (encodeRat (J.cost S) ++ encodeSet S)
  | .maximize =>
      ((∀ S, ¬ J.Feasible ψ S) ∧ out = [false]) ∨
      ∃ S ∈ J.MaxFeas ψ, out = true :: (encodeRat (J.cost S) ++ encodeSet S)
  | .count => out = encodeNat {S | J.Feasible ψ S}.ncard
  | .countMin => out = encodeNat (J.MinFeas ψ).ncard
  | .countMax => out = encodeNat (J.MaxFeas ψ).ncard

end MetricMSO.Supplement


