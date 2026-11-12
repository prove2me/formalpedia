-- Prove2me | Definitions.Def_MultStretchAPASP_Weighted_Encoding
-- name    : MultStretchAPASP_Weighted_Encoding
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-11T07:09:34.502558+00:00
-- url     : https://prove2.me/theorems/d234a89e-2444-4736-9879-282f2efc4bea
-- title:
--   Input and output encodings, explicit Õ, and 2-APASP programs with a w.h.p. time bound
-- statement:
--   A graph input on vertices $0,\dots,n-1$ is a list of edge records $(u,v,c)$, an edge $\{u,v\}$ of weight $c\in\mathbb N$. It is **simple** if no record is a loop and no two records name the same unordered pair; it is **valid for $W_{\max}$** if moreover every weight lies in $\{1,\dots,W_{\max}\}$. The 2-APASP input is the word list $n, W_{\max}, m$ followed by the $m$ triples. A value in $\mathbb N\cup\{\infty\}$ is written as two words, $(0,k)$ for $k$ and $(1,0)$ for $\infty$; a table is written row by row.
--
--   A correct **2-APASP** output for the graph $G$ is the code of a symmetric table $d$ with
--   $$\delta(u,v)\le d[u,v]\le 2\,\delta(u,v)\qquad\text{for all }u,v,$$
--   so $d[u,v]=\infty$ exactly for disconnected pairs. A correct $(1+\varepsilon)$-MSASP output for sources $S$ lists, for $s\in S$ in increasing order, the row $\bar\delta(s,\cdot)$ with $\delta(s,v)\le\bar\delta(s,v)\le(1+\varepsilon)\delta(s,v)$. Approximate (min, +)-product inputs are $r,s,t,W_{\max},\mathrm{off}_1,\mathrm{off}_2$ followed by the two matrices.
--
--   Asymptotic notation is explicit: $\tilde O(f)$ means at most $C(\log_2(n+2))^C f+C$ for a constant $C$ fixed before the instance, and $\log W_{\max}$ is read as $L=\log_2(W_{\max}+1)+1$. **`TwoAPASPWithin P C c bound`** says: for every $n\ge1$, $W_{\max}\ge1$ and valid simple graph, with $T=C(\log_2(n+2))^C\,\mathrm{bound}(n,W_{\max})+C$ and the corresponding word size, (i) on every random tape the program halts and outputs a correct 2-APASP table, and (ii) the set of random tapes on which it does not halt within $T$ steps has measure at most $n^{-c}$.
--
--   **Formalization Note.** The paper fixes no encoding; this is the mission's reading. The two-word code makes $\infty$ unambiguous. `ofEdges es` is the weight matrix of the records ($\infty$ off the edges and on the diagonal).
-- source:
--   Saggi, Sapir, Smallest Multiplicative Stretch for an α-APASP Below Õ(n^ω) Runtime, arXiv:2611.04736 (version of November 3, 2026, sha256 7cbb8123…), pp. 1, 4–5, 7, 19, 21

import Mathlib
import Definitions.Def_DynConnWC_Program
import Definitions.Def_MinKCutII_Main_Runs
import Definitions.Def_MultStretchAPASP_Weighted_Graph
import Definitions.Def_MultStretchAPASP_Weighted_MinPlus

set_option autoImplicit false

open scoped ENNReal
open DynConnWC MinKCutII.Main MeasureTheory

namespace MultStretchAPASP.Weighted

/-!
# Input and output encodings, explicit `Õ`, and 2-APASP programs

Saggi, Sapir, *Smallest Multiplicative Stretch for an α-APASP Below Õ(n^ω) Runtime*,
arXiv:2611.04736 (version of November 3, 2026, sha256 7cbb8123…), pp. 1, 4–5, 7, 19, 21, 31. The
paper fixes no machine and no encoding; this module is the mission's reading.

* **Graphs.** A graph on `Fin n` is a list `es` of edge records `(u, v, c)`: an edge `{u, v}` of
  weight `c`. `SimpleEdges es`: no loop (`u ≠ v`) and no two records for the same unordered pair
  (a simple undirected graph). `ValidEdges Wmax es`: moreover every weight lies in
  `[Wmax] = {1, …, Wmax}` (§5, p. 19). `ofEdges es` is its weight matrix (`⊤` off the edges).
  `edgeWords es = u₀, v₀, c₀, u₁, v₁, c₁, …` (vertex indices as numbers).
* **Values with `∞`.** A value in `ℕ∞` is written as two words: `[0, k]` for a finite `k`, `[1, 0]`
  for `∞` (`entryWords`). A matrix `D` with rows listed in `rows` is written row by row
  (`rowsWords`).
* **2-APASP.** The input is `[n, Wmax, m] ++ edgeWords es` (`apaspInput`). A correct output is
  `rowsWords [0, …, n−1] D` for a symmetric table `D : Fin n → Fin n → ℕ∞` with
  `δ(u, v) ≤ D[u, v] ≤ 2·δ(u, v)` for all `u, v` (`IsTwoAPASPOutput`); since `2·∞ = ∞`, `D[u, v] = ∞`
  exactly for disconnected pairs.
* **MSASP** (Theorem 2.14). The input is `[n, m] ++ edgeWords es ++ [|S|]` followed by the
  sources in increasing order (`msaspInput`); a correct output lists, for the sources in
  increasing order, the row `δ̄(s, ·)` with `δ(s, v) ≤ δ̄(s, v) ≤ (1 + ε)·δ(s, v)`
  (`IsMSASPOutput`).
* **Approximate (min, +)-products** (Theorem 2.15, Lemma 5.8). The input is
  `[r, s, t, Wmax, off₁, off₂]` followed by the entries of `A` (`r × s`) and of `B` (`s × t`) in
  the two-word code (`minPlusInput`; Theorem 2.15 uses `off₁ = off₂ = 0`).
* **Explicit `Õ`.** `polylog n C = (log₂(n + 2))^C`; a bound `Õ(f)` is `C·(log₂(n + 2))^C·f + C`
  with a constant `C` fixed before the instance. `logW Wmax = log₂(Wmax + 1) + 1` stands for
  `log Wmax` (it does not vanish at `Wmax = 1`).
* **`TwoAPASPWithin P C c bound`**: the program `P` solves 2-APASP with running time
  `Õ(bound)` with probability `≥ 1 − n^{−c}`: for every `n ≥ 1`, `Wmax ≥ 1` and every simple graph
  with weights in `[Wmax]` (no connectivity assumption), with `T = C·(log₂(n+2))^C·bound n Wmax + C`
  and word size `wordSize C inp T`, (i) on every random tape the run halts and its output is a
  correct 2-APASP table, and (ii) the random tapes on which it does not halt within `T` steps have
  measure at most `n^{−c}` under `tapeLaw`.
-/

/-- No loops and at most one record per unordered pair. -/
def SimpleEdges {n : ℕ} (es : List (Fin n × Fin n × ℕ)) : Prop :=
  (∀ e ∈ es, e.1 ≠ e.2.1) ∧ (es.map fun e => s(e.1, e.2.1)).Nodup

/-- A simple undirected graph with weights in `[Wmax]`. -/
def ValidEdges {n : ℕ} (Wmax : ℕ) (es : List (Fin n × Fin n × ℕ)) : Prop :=
  SimpleEdges es ∧ ∀ e ∈ es, 1 ≤ e.2.2 ∧ e.2.2 ≤ Wmax

/-- The weight matrix of the edge records (`⊤` off the edges and on the diagonal). -/
noncomputable def ofEdges {n : ℕ} (es : List (Fin n × Fin n × ℕ)) : WMat n :=
  fun x y => if x = y then ⊤ else
    ⨅ e ∈ es, if s(e.1, e.2.1) = s(x, y) then ((e.2.2 : ℕ) : ℝ≥0∞) else ⊤

/-- The words of the edge records. -/
def edgeWords {n : ℕ} (es : List (Fin n × Fin n × ℕ)) : List ℕ :=
  es.flatMap fun e => [(e.1 : ℕ), (e.2.1 : ℕ), e.2.2]

/-- The 2-APASP input `[n, Wmax, m] ++ edgeWords es`. -/
def apaspInput (n Wmax : ℕ) (es : List (Fin n × Fin n × ℕ)) : List ℕ :=
  [n, Wmax, es.length] ++ edgeWords es

/-- The two-word code of a value in `ℕ∞`: `[0, k]` for `k`, `[1, 0]` for `∞`. -/
noncomputable def entryWords (x : ℕ∞) : List ℕ :=
  if x = ⊤ then [1, 0] else [0, x.toNat]

/-- The rows `rows` of the matrix `D`, each row in increasing column order, in the two-word code. -/
noncomputable def rowsWords {r t : ℕ} (rows : List (Fin r)) (D : Fin r → Fin t → ℕ∞) : List ℕ :=
  rows.flatMap fun i => (List.finRange t).flatMap fun j => entryWords (D i j)

/-- A correct 2-APASP output for the graph `w`. -/
def IsTwoAPASPOutput {n : ℕ} (w : WMat n) (out : List ℕ) : Prop :=
  ∃ D : Fin n → Fin n → ℕ∞, out = rowsWords (List.finRange n) D ∧
    (∀ u v, D u v = D v u) ∧
    ∀ u v, dist w u v ≤ (D u v : ℝ≥0∞) ∧ (D u v : ℝ≥0∞) ≤ 2 * dist w u v

/-- The MSASP input: the graph, then `|S|` and the sources in increasing order. -/
def msaspInput {n : ℕ} (es : List (Fin n × Fin n × ℕ)) (S : Finset (Fin n)) : List ℕ :=
  [n, es.length] ++ edgeWords es ++ [S.card] ++ (S.sort (· ≤ ·)).map fun s => (s : ℕ)

/-- A correct `(1 + ε)`-MSASP output for the graph `w` and the sources `S`. -/
def IsMSASPOutput {n : ℕ} (w : WMat n) (S : Finset (Fin n)) (ε : ℝ) (out : List ℕ) : Prop :=
  ∃ D : Fin n → Fin n → ℕ∞, out = rowsWords (S.sort (· ≤ ·)) D ∧
    ∀ s ∈ S, ∀ v, dist w s v ≤ (D s v : ℝ≥0∞) ∧
      (D s v : ℝ≥0∞) ≤ ENNReal.ofReal (1 + ε) * dist w s v

/-- The input of an (offset-shifted) approximate (min, +)-product. -/
noncomputable def minPlusInput {r s t : ℕ} (Wmax off₁ off₂ : ℕ) (A : Fin r → Fin s → ℕ∞)
    (B : Fin s → Fin t → ℕ∞) : List ℕ :=
  [r, s, t, Wmax, off₁, off₂] ++ rowsWords (List.finRange r) A ++ rowsWords (List.finRange s) B

/-- `(log₂(n + 2))^C`. -/
noncomputable def polylog (n C : ℕ) : ℝ :=
  Real.logb 2 ((n : ℝ) + 2) ^ C

/-- `log₂(Wmax + 1) + 1`, standing for `log Wmax`. -/
noncomputable def logW (Wmax : ℕ) : ℝ :=
  Real.logb 2 ((Wmax : ℝ) + 1) + 1

/-- `P` is a 2-APASP program running in time `Õ(bound n Wmax)` with probability `≥ 1 − n^{−c}`,
with the explicit constant `C`. -/
def TwoAPASPWithin (P : Program) (C : ℕ) (c : ℝ) (bound : ℕ → ℕ → ℝ) : Prop :=
  ∀ (n Wmax : ℕ) (es : List (Fin n × Fin n × ℕ)), 1 ≤ n → 1 ≤ Wmax → ValidEdges Wmax es →
    let T : ℝ := (C : ℝ) * polylog n C * bound n Wmax + C
    let inp := apaspInput n Wmax es
    let W := wordSize C inp T
    (∀ ω : ℕ → Fin (2 ^ W),
      (∃ t : ℕ, Halted P (conf W P inp ω t)) ∧ IsTwoAPASPOutput (ofEdges es) (finalOutput W P inp ω)) ∧
    tapeLaw W {ω | ¬ HaltsWithin W P inp ω T} ≤ ENNReal.ofReal ((n : ℝ) ^ (-c))

end MultStretchAPASP.Weighted


