-- Prove2me | Definitions.Def_LocalLLL_Main_Supplement_Corollaries
-- name    : LocalLLL_Main_Supplement_Corollaries
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-15T01:42:51.238103+00:00
-- url     : https://prove2.me/theorems/61ab21a1-3544-41bb-80a6-0ed076e82144
-- title:
--   Local checkers, k-vertex splittings, k-domatic partitions and log log(n/ε)
-- statement:
--   This file adds the objects used by the corollaries of §4.4 on top of the published LOCAL model (programs $\mathcal A$, executions $\mathrm{run}$, fair-coin tapes) and graph notation (open neighbourhood $N(v)$, degree $\deg(v)=|N(v)|$).
--
--   1. **Local checker.** A checker is a LOCAL program $\mathcal C$ whose local input at $v$ is the pair (input of $v$, output of $v$) and whose output is a verdict in $\{\mathrm{true},\mathrm{false}\}$. Run for $R$ rounds on the all-false tape, its verdict at $v$ is a deterministic function of the graph, the identifiers and the labels within distance $R$ of $v$. Node $v$ is *correct* when the verdict at $v$ is true; the labelling is *correct* when every node is correct.
--   2. **k-vertex splitting of discrepancy $\delta$.** A map $c:V\to\{0,\dots,k-1\}$ (the parts $V_i=c^{-1}(i)$, possibly empty) such that for every vertex $v$ and every part $i$,
--   $$\Bigl|\,|N(v)\cap V_i| - \frac{\deg(v)}{k}\Bigr| \le \delta .$$
--   3. **k-domatic partition.** A map $c:V\to\{0,\dots,k-1\}$ such that every part $V_i$ dominates $G$: for every vertex $v$ and every $i$, either $v\in V_i$ or $N(v)\cap V_i\neq\emptyset$.
--   4. **Padded iterated logarithm.** $\ell(n,\varepsilon)=\log\log(n/\varepsilon+16)$, with natural logarithms, padded as the published $\log\log(n+16)$.
--
--   These are the success conditions and the round-bound expression of Theorems 4.1, 4.2, 4.4 and 4.5.
--
--   **Formalization Note** A deterministic checker is represented as a randomized program run on one fixed tape; every deterministic R-round LOCAL algorithm arises this way by ignoring its tape.
-- source:
--   Maxime Flin, Mohsen Ghaffari, Magnus M. Halldorsson, Yannic Maus, Alexandre Nolin, STOC 2027 submission #475 (October 2026), §4.4: local checking (Theorems 4.1, 4.2), k-vertex splitting (definition before Theorem 4.4), k-domatic partition (definition before Theorem 4.5), pp. 10-12 (PDF 11-13); source.pdf, SHA-256 3dde5fa7cf9bc55426bf80a9dd9632c790e2ea3d0fe4a19b924d1802d48000a2.

import Mathlib
import Definitions.Def_LocalLLL_Main_GraphModel
import Definitions.Def_LocalLLL_Main_LocalAlgorithm

noncomputable section

namespace LocalLLL.Main.Supplement

open LocalLLL.Main

/-- The verdicts of an `R`-round local checker on the labelling `(input, out)`. The checker is
run on the all-`false` tape, so its verdict is a deterministic function of the identifiers, the
labels and the graph; every deterministic `R`-round LOCAL checker arises this way. -/
def checkAt {I O V : Type} (chk : LocalAlg (I × O) Bool) (R : ℕ) (G : SimpleGraph V)
    (id : V → ℕ) (input : V → I) (out : V → O) : V → Bool :=
  run chk R G id (fun v => (input v, out v)) (fun _ _ => false)

/-- Every node accepts its output: the checker reports `true` at every vertex. -/
def allCorrect {I O V : Type} (chk : LocalAlg (I × O) Bool) (R : ℕ) (G : SimpleGraph V)
    (id : V → ℕ) (input : V → I) (out : V → O) : Prop :=
  ∀ v, checkAt chk R G id input out v = true

/-- `c` is a k-vertex splitting of discrepancy `δ`: for every vertex `v` and part `i`,
`| |N(v) ∩ V_i| - deg(v)/k | ≤ δ`, with `N(v)` the open neighbourhood. Parts may be empty. -/
def IsVertexSplitting {V : Type} (G : SimpleGraph V) (k : ℕ) (δ : ℝ) (c : V → Fin k) : Prop :=
  ∀ v (i : Fin k),
    |(Nat.card {u // G.Adj v u ∧ c u = i} : ℝ) - (degree G v : ℝ) / (k : ℝ)| ≤ δ

/-- `c` is a k-domatic partition: every part `V_i = c⁻¹(i)` is a dominating set, i.e. every
vertex lies in `V_i` or has a neighbour in `V_i`. -/
def IsDomaticPartition {V : Type} (G : SimpleGraph V) (k : ℕ) (c : V → Fin k) : Prop :=
  ∀ v (i : Fin k), c v = i ∨ ∃ u, G.Adj v u ∧ c u = i

/-- `log log (n/ε + 16)`, padded as `LocalLLL.Main.loglog`. -/
def loglogRatio (n : ℕ) (ε : ℝ) : ℝ := Real.log (Real.log ((n : ℝ) / ε + 16))

end LocalLLL.Main.Supplement


