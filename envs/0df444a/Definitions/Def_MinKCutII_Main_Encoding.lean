-- Prove2me | Definitions.Def_MinKCutII_Main_Encoding
-- name    : MinKCutII_Main_Encoding
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-11T03:39:04.81809+00:00
-- url     : https://prove2.me/theorems/ccde8590-8720-4b7d-9c2c-d642104f8b22
-- title:
--   Input encodings of weighted multigraphs and cut families, and output decodings (k-cut labels, the flag)
-- statement:
--   A graph input is $n$ vertices $\{0,\dots,n-1\}$ (the paper's $[n]$ shifted by one) and $m$ edge records $(u_i,v_i,c_i)$ with $c_i\in\mathbb N$; parallel records and loops are allowed. Its capacitated multigraph has ends $\{u_i,v_i\}$ and capacity $c_i$, and $c(E)=\sum_ic_i$. Input word lists:
--
--   - $[n,m,k]$ followed by $u_0,v_0,c_0,u_1,\dots$ (Theorems 1, 47, 65); $[n,m]$ followed by the records (Theorems 34, 53, 58);
--   - $[n,m,k,p,q,r,N]$, the records, then the incidence vectors of $N$ cuts (word $1$ or $0$ for each vertex), for Lemmas 36, 39, 41 and Corollary 42; the threshold is $U=p/q$ and $r$ is the root;
--   - $[n,m,k,p,q,t]$, the $t$ incidence vectors, then the records (Lemma 40).
--
--   A labelling $f$ is output as the words $0,f(0),\dots,f(n-1)$; the single word $1$ is the **flag**: "infeasible" ($\lambda_k=+\infty$) for the $k$-cut problems, "size certificate" for the certificate lemmas. An output **answers Minimum $k$-Cut** if it is a minimum $k$-cut when $k\le n$ and the flag when $n<k$.
--
--   **Formalization Note.** The encodings are the mission's reading; the paper fixes none. Lemma 40's layout puts the cuts first so that its space bound concerns working memory.
-- source:
--   Vaughn, Faster Minimum k-Cut II: Improved Randomized and Deterministic Algorithms for Weighted Graphs, arXiv:2609.27797 (version of November 1, 2026, sha256 b01b5a6f…), pp. 5–6 (§2 conventions); input/output layout is the mission's reading

import Mathlib
import Definitions.Def_MinKCutII_Main_KCut

set_option autoImplicit false

open CombOpt.MinCut

namespace MinKCutII.Main

/-!
# Input encodings of graphs and cut families, and output decodings

Vaughn, *Faster Minimum k-Cut II*, arXiv:2609.27797 (version of November 1, 2026, sha256
b01b5a6f…). The paper fixes no encoding; this module is the mission's reading.

* A graph input is `n` vertices `Fin n = {0, …, n − 1}` (the paper's `[n]`, shifted by one) and `m`
  edge records `(u_i, v_i, c_i)`, `u_i, v_i : Fin n`, `c_i : ℕ` (`EdgeRecs n m`). Parallel records
  and loops are allowed. `toGraph ed` is the `CapGraph (Fin n) (Fin m)` with ends `{u_i, v_i}` and
  capacity `c_i`; `capSum ed = c(E)`.
* `edgeWords ed = u_0, v_0, c_0, u_1, v_1, c_1, …` (vertex indices as numbers).
* A cut family `S_0, …, S_{N−1}` (`S : ℕ → Finset (Fin n)`, first `N` used) is given by incidence
  vectors: `cutWords n N S` lists, for `j < N` and `v = 0, …, n − 1`, the word `1` if `v ∈ S_j`
  and `0` otherwise.
* Inputs: `kGraphInput n m k ed = [n, m, k] ++ edgeWords ed` (Theorems 1, 47, 65);
  `graphInput n m ed = [n, m] ++ edgeWords ed` (Theorems 34, 53, 58);
  `familyInput n m k p q r N ed S = [n, m, k, p, q, r, N] ++ edgeWords ed ++ cutWords n N S`
  (Lemmas 36, 39, 41, Corollary 42; the threshold is `U = p/q`, the root is vertex `r`); and
  `vennInput n m k p q t ed S = [n, m, k, p, q, t] ++ cutWords n t S ++ edgeWords ed` (Lemma 40,
  cuts before edges, so that the edges can be scanned once without being stored).
* Outputs (the list of written words): a labelling `f : Fin n → Fin k` is output as
  `labelsOut f = [0, f(0), …, f(n − 1)]`; the flag `[1]` (`flagOut`) means "infeasible" (no k-cut,
  `λ_k = +∞`) for the k-cut problems and "size certificate" for the certificate lemmas.
* `IsMinKCutOutput G k out`: if `k ≤ n`, `out` is a minimum k-cut of `G`; if `n < k`, `out` is the
  flag. `IsKCutAtMostOutput G k U out`: `out` is a k-cut of `G` of value at most `U`.
-/

/-- `m` edge records `(u_i, v_i, c_i)` on the vertex set `Fin n`. -/
abbrev EdgeRecs (n m : ℕ) := Fin m → Fin n × Fin n × ℕ

/-- The capacitated multigraph of the edge records. -/
noncomputable def toGraph {n m : ℕ} (ed : EdgeRecs n m) : CapGraph (Fin n) (Fin m) :=
  ⟨fun i => s((ed i).1, (ed i).2.1), fun i => ((ed i).2.2 : ℝ)⟩

/-- The total capacity `c(E)`. -/
def capSum {n m : ℕ} (ed : EdgeRecs n m) : ℕ :=
  ∑ i, (ed i).2.2

/-- The input words of the edge records. -/
def edgeWords {n m : ℕ} (ed : EdgeRecs n m) : List ℕ :=
  (List.ofFn fun i : Fin m => [((ed i).1 : ℕ), ((ed i).2.1 : ℕ), (ed i).2.2]).flatten

/-- The incidence vectors of `S_0, …, S_{N−1}`. -/
def cutWords (n N : ℕ) (S : ℕ → Finset (Fin n)) : List ℕ :=
  (List.ofFn fun j : Fin N => List.ofFn fun v : Fin n => if v ∈ S j then 1 else 0).flatten

/-- Graph input with a parameter `k`: `[n, m, k] ++ edgeWords ed`. -/
def kGraphInput {n m : ℕ} (k : ℕ) (ed : EdgeRecs n m) : List ℕ :=
  [n, m, k] ++ edgeWords ed

/-- Graph input: `[n, m] ++ edgeWords ed`. -/
def graphInput {n m : ℕ} (ed : EdgeRecs n m) : List ℕ :=
  [n, m] ++ edgeWords ed

/-- Graph, `k`, threshold `U = p/q`, root `r`, and a family of `N` cuts (edges first). -/
def familyInput {n m : ℕ} (k p q : ℕ) (r : Fin n) (N : ℕ) (ed : EdgeRecs n m)
    (S : ℕ → Finset (Fin n)) : List ℕ :=
  [n, m, k, p, q, (r : ℕ), N] ++ edgeWords ed ++ cutWords n N S

/-- Graph, `k`, threshold `U = p/q` and `t` cuts (cuts first, then edges). -/
def vennInput {n m : ℕ} (k p q t : ℕ) (ed : EdgeRecs n m) (S : ℕ → Finset (Fin n)) :
    List ℕ :=
  [n, m, k, p, q, t] ++ cutWords n t S ++ edgeWords ed

/-- The output words of a labelling: `0` followed by the labels. -/
def labelsOut {n k : ℕ} (f : Fin n → Fin k) : List ℕ :=
  0 :: List.ofFn (fun v => ((f v : Fin k) : ℕ))

/-- The flag output `[1]`. -/
def flagOut : List ℕ := [1]

/-- `out` answers Minimum k-Cut on `G`: a minimum k-cut if `k ≤ n`, the flag if `n < k`. -/
def IsMinKCutOutput {n m : ℕ} (G : CapGraph (Fin n) (Fin m)) (k : ℕ) (out : List ℕ) : Prop :=
  (k ≤ n ∧ ∃ f : Fin n → Fin k, IsMinKCut G k f ∧ out = labelsOut f) ∨ (n < k ∧ out = flagOut)

/-- `out` is a k-cut of `G` of value at most `U`. -/
def IsKCutAtMostOutput {n m : ℕ} (G : CapGraph (Fin n) (Fin m)) (k : ℕ) (U : ℝ)
    (out : List ℕ) : Prop :=
  ∃ f : Fin n → Fin k, Function.Surjective f ∧ partVal G f ≤ U ∧ out = labelsOut f

end MinKCutII.Main


