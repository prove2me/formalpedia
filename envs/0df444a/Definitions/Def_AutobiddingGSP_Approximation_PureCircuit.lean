-- Prove2me | Definitions.Def_AutobiddingGSP_Approximation_PureCircuit
-- name    : AutobiddingGSP_Approximation_PureCircuit
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-10T06:26:50.366071+00:00
-- url     : https://prove2.me/theorems/df9bb644-f387-4e4b-bcde-b3282756a175
-- title:
--   Pure-Circuit gates and instances, forward span, and Bounded-Forward-Span Pure-Circuit(d)
-- statement:
--   Values $\{0,1,\bot\}$. Gates: $\mathrm{NOT}(u;w)$: $x[u]\in\{0,1\}\Rightarrow x[w]=\neg x[u]$. $\mathrm{NOR}(u,v;w)$: $x[u]=1\lor x[v]=1\Rightarrow x[w]=0$; $x[u]=x[v]=0\Rightarrow x[w]=1$ ($u=v$ allowed). $\mathrm{NPURIFY}(u;v,w)$, $v\ne w$: $\{x[v],x[w]\}\cap\{0,1\}\ne\emptyset$, and $x[u]\in\{0,1\}\Rightarrow x[v]=x[w]=\neg x[u]$.
--
--   An instance has vertices $0,\dots,n-1$ and an ordered gate list $g_1,\dots,g_m$. Well formed: vertices in range, every vertex is the output of exactly one gate, and a gate's outputs are distinct from its inputs (the convention of §§7.2, 8.2). Forward span at most $d$: every wire from an output of $g_I$ to an input of $g_J$ with $J>I$ has $J-I\le d$; backward wires unrestricted.
--
--   `BFSPC d`: instances are codes of well-formed instances whose order has forward span at most $d$; answers are codes of assignments $V\to\{0,1,\bot\}$ satisfying every gate.
-- source:
--   Hansen, Li and Nie (2026), Complexity of Autobidding Equilibria in GSP Sponsored Shopping, arXiv:2610.13716 [arXiv version unverified; supplied PDF revision created 2026-11-03, SHA256 40ce53fb39e7897580c44ffab04f7611388d8afc4c26ee7118de76bd21b73c8f], Definitions 6.2–6.4, pp. 26–27 (PDF 26–27); §7.2 p. 33; §8.2 p. 39

import Mathlib
import Definitions.Def_TetrisHard_Rows_Search
import Definitions.Def_QAlgorithms_ClassicalBinaryEncoding

namespace AutobiddingGSP.Approximation

open QAlgorithms.LocalHamiltonian

/-- The three values `{0, 1, ⊥}` of a Pure-Circuit assignment (Definition 6.2, p. 26). -/
inductive Tri where
  | zero
  | one
  | bot
  deriving DecidableEq

/-- Negation on `{0, 1, ⊥}`: `¬0 = 1`, `¬1 = 0` (and `⊥` is left as `⊥`; it is only applied to pure
values in the gate constraints). -/
def Tri.neg : Tri → Tri
  | Tri.zero => Tri.one
  | Tri.one => Tri.zero
  | Tri.bot => Tri.bot

/-- **A Pure-Circuit gate** (Definition 6.2, p. 26): `not u w` is `NOT(u; w)`, `nor u v w` is
`NOR(u, v; w)` (the inputs `u, v` may coincide), and `npurify u v w` is `NPURIFY(u; v, w)`.
Vertices are numbered `0, …, n − 1`. -/
inductive PCGate where
  | not (u w : ℕ)
  | nor (u v w : ℕ)
  | npurify (u v w : ℕ)

/-- The input vertices of a gate (with repetition). -/
def PCGate.inputs : PCGate → List ℕ
  | PCGate.not u _ => [u]
  | PCGate.nor u v _ => [u, v]
  | PCGate.npurify u _ _ => [u]

/-- The output vertices of a gate. -/
def PCGate.outputs : PCGate → List ℕ
  | PCGate.not _ w => [w]
  | PCGate.nor _ _ w => [w]
  | PCGate.npurify _ v w => [v, w]

/-- **The gate constraints** of Definition 6.2 (p. 26) on an assignment `x : V → {0, 1, ⊥}`:

* `NOT(u; w)`: `x[u] ∈ {0, 1} ⟹ x[w] = ¬x[u]`;
* `NOR(u, v; w)`: `x[u] = 1 ∨ x[v] = 1 ⟹ x[w] = 0`, and `x[u] = 0 ∧ x[v] = 0 ⟹ x[w] = 1`;
* `NPURIFY(u; v, w)`: `{x[v], x[w]} ∩ {0, 1} ≠ ∅`, and `x[u] ∈ {0, 1} ⟹ x[v] = x[w] = ¬x[u]`. -/
def PCGate.Sat (x : ℕ → Tri) : PCGate → Prop
  | PCGate.not u w => x u ≠ Tri.bot → x w = (x u).neg
  | PCGate.nor u v w => (x u = Tri.one ∨ x v = Tri.one → x w = Tri.zero) ∧
      (x u = Tri.zero ∧ x v = Tri.zero → x w = Tri.one)
  | PCGate.npurify u v w => (x v ≠ Tri.bot ∨ x w ≠ Tri.bot) ∧
      (x u ≠ Tri.bot → x v = (x u).neg ∧ x w = (x u).neg)

/-- A Pure-Circuit instance: `n` vertices `0, …, n − 1` and the gates `g_1, …, g_m` in the given
order (the order is the gate ordering of Definitions 6.3–6.4). -/
structure PCInstance where
  nV : ℕ
  gates : List PCGate

/-- **Well-formed Pure-Circuit instance** (Definition 6.2, p. 26): every gate mentions only
vertices of `V`; the two outputs of an `NPURIFY` gate are distinct; every vertex is an output of
exactly one gate; and the outputs of every gate are distinct from its inputs, the convention used
explicitly in §7.2 (p. 33) and §8.2 (p. 39) ("a gate's outputs are distinct from its inputs"). -/
def PCInstance.WF (C : PCInstance) : Prop :=
  (∀ g ∈ C.gates, (∀ u ∈ g.inputs, u < C.nV) ∧ (∀ w ∈ g.outputs, w < C.nV) ∧ g.outputs.Nodup ∧
      ∀ w ∈ g.outputs, w ∉ g.inputs) ∧
    ∀ v, v < C.nV → (C.gates.filter (fun g => decide (v ∈ g.outputs))).length = 1

/-- **Forward span at most `d`** (Definition 6.3, p. 27): for the ordering `g_1, …, g_m`, every wire
from an output of `g_I` to an input of `g_J` with `J > I` has `J − I ≤ d`; backward wires are
unrestricted. (Lean positions are 0-based.) -/
def PCInstance.FwdSpanLE (C : PCInstance) (d : ℕ) : Prop :=
  ∀ (I J : ℕ) (hI : I < C.gates.length) (hJ : J < C.gates.length), I < J →
    (∃ w ∈ (C.gates[I]).outputs, w ∈ (C.gates[J]).inputs) → J - I ≤ d

/-- Binary code of a gate: a two-bit tag, then its vertices in self-delimiting binary. -/
def encPCGate : PCGate → List Bool
  | PCGate.not u w => [false, false] ++ encBin u ++ encBin w
  | PCGate.nor u v w => [false, true] ++ encBin u ++ encBin v ++ encBin w
  | PCGate.npurify u v w => [true, false] ++ encBin u ++ encBin v ++ encBin w

/-- Binary code of an instance: `n`, `m`, then the gates in order. -/
def encPC (C : PCInstance) : List Bool :=
  encBin C.nV ++ encBin C.gates.length ++ C.gates.flatMap encPCGate

/-- Binary code of a value in `{0, 1, ⊥}`. -/
def encTri : Tri → List Bool
  | Tri.zero => [false, false]
  | Tri.one => [false, true]
  | Tri.bot => [true, false]

/-- An assignment `Fin n → {0, 1, ⊥}` extended by `⊥` to all natural numbers. -/
def extendTri {k : ℕ} (x : Fin k → Tri) : ℕ → Tri :=
  fun v => if h : v < k then x ⟨v, h⟩ else Tri.bot

/-- **Bounded-Forward-Span Pure-Circuit(d)** (Definition 6.4, p. 27), as a finite-string search
problem: an instance is a well-formed Pure-Circuit instance together with (the order of its gate
list) an ordering of forward span at most `d`; an answer is an assignment `V → {0, 1, ⊥}` (two bits
per vertex) satisfying every gate. -/
def BFSPC (d : ℕ) : TetrisHard.Rows.SearchProblem where
  valid s := ∃ C : PCInstance, C.WF ∧ C.FwdSpanLE d ∧ s = encPC C
  answer s t := ∃ C : PCInstance, C.WF ∧ C.FwdSpanLE d ∧ s = encPC C ∧
    ∃ x : Fin C.nV → Tri, t = (List.ofFn x).flatMap encTri ∧ ∀ g ∈ C.gates, g.Sat (extendTri x)

end AutobiddingGSP.Approximation


