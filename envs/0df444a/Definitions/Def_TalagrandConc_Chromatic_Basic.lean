-- Prove2me | Definitions.Def_TalagrandConc_Chromatic_Basic
-- name    : TalagrandConc_Chromatic_Basic
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-06T15:40:15.791566+00:00
-- url     : https://prove2.me/theorems/947f2713-0fc2-46b9-b2a9-93cd59643e95
-- title:
--   The random graph $G(n,p)$, $\chi(G,A)$, $\chi(G,m)$, the vertex-exposure space $\Omega'$, the sets $A$, $B$ and $N(G,e)$ of Chapter 9
-- statement:
--   This module fixes the objects of Chapter 9 of Talagrand's paper (chromatic number of random graphs).
--
--   1. **Graphs.** The vertex set is $V=\{1,\dots,n\}$ and a graph $G$ is a subset of $E_0=\{(i,j);\ i<j\}$; $i,j$ are *linked* when $(i,j)\in G$. A set $I\subseteq V$ is *independent* if no two of its points are linked.
--
--   2. **Chromatic numbers.** For $A\subseteq V$, $\chi(G,A)$ is the smallest number of independent sets covering $A$, i.e. the chromatic number of the subgraph of $G$ induced on $A$ (so $\chi(G,\emptyset)=0$). For an integer $m$,
--   $$\chi(G,m)=\inf\{\chi(G,A);\ \operatorname{card}A=m\},$$
--   which is $+\infty$ when $m>n$. We also write $\sup\{\chi(G,F);\ F\subset V,\ \operatorname{card}F\le s\}$ for a real $s$.
--
--   3. **The random graph $G(n,p)$.** On $\Omega=\{0,1\}$ put the probability giving weight $p$ to $1$ and $1-p$ to $0$; $P$ is the product probability on $\Omega^{E_0}$. For $x=(x_e)_{e\in E_0}$ the graph $G(x)$ contains $(i,j)$ iff $x_{(i,j)}=1$. Under $P$, $G(x)$ is the random graph $G(n,p)$: every possible edge is present with probability $p$, independently.
--
--   4. **Vertex exposure.** $\Omega'=\prod_{j}\Omega_j$ with $\Omega_j=\{0,1\}^{j-1}$: the coordinate $\omega_j=(\omega_{i,j})_{i<j}$ records the edges from $j$ to earlier vertices, and $(i,j)\in G(\omega)$ iff $\omega_{i,j}=1$.
--
--   5. **The sets of the proof of Theorem 9.1.** For integers $m,k$, a real $t$ and an integer $a$, $A\subseteq\Omega'$ is the set of $\omega$ with $\chi(G(\omega),m)\ge a$ and $\sup\{\chi(G(\omega),F);\ \operatorname{card}F\le t\sqrt m\}\le k$; and, for a set $A\subseteq\Omega'$, Eq. (9.3) defines
--   $$B=\Big\{\omega;\ \forall(\alpha_j)\ge0,\ \exists\omega'\in A;\ \sum_j\alpha_j1_{\{\omega_j\ne\omega'_j\}}\le t\sqrt{\textstyle\sum_j\alpha_j^2}\Big\}.$$
--
--   6. **Independent-set counts.** For an integer $r$ and $e=(i,j)\in E_0$, $N(G,e)$ is the number of independent sets of $G$ of size $r$ that contain $i$ and $j$.
--
--   These objects are shared by every statement of the chapter: Theorem 9.1 is stated on $G(n,p)$ through the edge product, its proof works on $\Omega'$ through $A$ and $B$, and Proposition 9.2 is stated through $N(G,e)$.
--
--   **Formalization Note** Vertices are `Fin n` (0-based), so $\Omega_j=\{0,1\}^{j}$ for the 0-based vertex $j$; vertex $0$ carries the one-point coordinate $\{0,1\}^0$, which the paper also includes when it writes $\prod_{j\le n}\Omega_j$. Chromatic numbers are Mathlib's `chromaticNumber` of the induced subgraph, valued in `ℕ∞`, and $\chi(G,m)$ is an infimum in `ℕ∞` ($+\infty$ on the empty family, never a junk $0$); `chiMZ` is the same value in `WithTop ℤ` for comparisons with integers. The weights $\alpha_j$ in $B$ are nonnegative, the setting of Lemma 4.1.2 (on $\{0,1\}$-vectors only nonnegative weights make (4.1.4) imply (4.1.5)). The Bernoulli law is $p\,\delta_1+(1-p)\,\delta_0$ with nonnegative-real truncations of $p,1-p$, a probability measure for $0\le p\le1$.
-- source:
--   Talagrand, Concentration of measure and isoperimetric inequalities in product spaces, Publ. Math. IHÉS 81 (1995), pp. 162–163, Chapter 9 (definitions of G, χ(G,A), χ(G,m), G(n,p), Ω', A); p. 164, Eq. (9.3) and the definition of N(G,e); p. 164 (proof of Proposition 9.2: Ω = {0,1}, product on Ω^{E_0})

import Mathlib

namespace TalagrandConc.Chromatic

open MeasureTheory
open scoped Classical

/-- The set `E₀ = {(i, j) ; i < j}` of possible edges on the vertex set `V = {0, …, n-1}`
(the paper's `{1, …, n}`, shifted to 0-based indices). -/
abbrev EdgeSlot (n : ℕ) : Type := {e : Fin n × Fin n // e.1 < e.2}

/-- The probability measure on `Ω = {0, 1}` (here `Bool`, `true = 1`) giving weight `p` to `1`
and `1 - p` to `0`. It is a probability measure when `0 ≤ p ≤ 1`. -/
noncomputable def coin (p : ℝ) : Measure Bool :=
  Real.toNNReal p • Measure.dirac true + Real.toNNReal (1 - p) • Measure.dirac false

/-- The product probability `P` on `Ω^{E₀}`: one independent `coin p` per possible edge.
Under `P`, the graph `graphOf x` is the random graph `G(n, p)`. -/
noncomputable def gnp (n : ℕ) (p : ℝ) : Measure (EdgeSlot n → Bool) :=
  Measure.pi (fun _ : EdgeSlot n => coin p)

/-- The graph `G(x)` of an edge configuration `x ∈ {0,1}^{E₀}`: for `i < j`, `(i, j) ∈ G(x)` iff
`x_{(i,j)} = 1`. -/
def graphOf {n : ℕ} (x : EdgeSlot n → Bool) : SimpleGraph (Fin n) :=
  SimpleGraph.fromRel fun i j => ∃ h : i < j, x ⟨(i, j), h⟩ = true

/-- `χ(G, A)`: the chromatic number of the subgraph of `G` induced on `A`, i.e. the smallest
number of independent sets of `G` covering `A`. `χ(G, ∅) = 0`. -/
noncomputable def chiSet {n : ℕ} (G : SimpleGraph (Fin n)) (A : Finset (Fin n)) : ℕ∞ :=
  (G.induce (A : Set (Fin n))).chromaticNumber

/-- `χ(G, m) = inf {χ(G, A) ; card A = m}`, computed in `ℕ∞`; it is `⊤` (`+∞`) when `m > n`
(empty infimum). -/
noncomputable def chiM {n : ℕ} (G : SimpleGraph (Fin n)) (m : ℕ) : ℕ∞ :=
  ⨅ (A : Finset (Fin n)) (_ : A.card = m), chiSet G A

/-- `χ(G, m)` viewed in `WithTop ℤ` (same value, `⊤ ↦ ⊤`), so that it can be compared with
integers `a`, `a - k`. -/
noncomputable def chiMZ {n : ℕ} (G : SimpleGraph (Fin n)) (m : ℕ) : WithTop ℤ :=
  WithTop.map (fun c : ℕ => (c : ℤ)) (chiM G m)

/-- `sup {χ(G, F) ; F ⊂ V, card F ≤ s}` in `ℕ∞` (the family always contains `F = ∅` when
`0 ≤ s`). -/
noncomputable def localSup {n : ℕ} (G : SimpleGraph (Fin n)) (s : ℝ) : ℕ∞ :=
  ⨆ (F : Finset (Fin n)) (_ : (F.card : ℝ) ≤ s), chiSet G F

/-- The vertex-exposure product `Ω' = ∏_j Ω_j` with `Ω_j = {0,1}^{j}` for the 0-based vertex `j`
(the paper's `Ω_j = {0,1}^{j-1}` for `1 ≤ j ≤ n`): the coordinate `ω_j = (ω_{i,j})_{i<j}` records
the edges from `j` to the earlier vertices. The coordinate of vertex `0` is the one-point space
`{0,1}^0`. -/
abbrev VxSpace (n : ℕ) : Type := (j : Fin n) → (Fin j.val → Bool)

/-- The graph `G(ω)` of `ω ∈ Ω'`: for `i < j`, `(i, j) ∈ G(ω)` iff `ω_{i,j} = 1`. -/
def vxGraph {n : ℕ} (ω : VxSpace n) : SimpleGraph (Fin n) :=
  SimpleGraph.fromRel fun i j => ∃ h : i < j, ω j ⟨i.val, h⟩ = true

/-- The set `A ⊂ Ω'` of the proof of Theorem 9.1 (p. 163): the `ω` with `χ(G(ω), m) ≥ a` and
`sup {χ(G(ω), F) : card F ≤ t√m} ≤ k`. -/
noncomputable def setA (n m k : ℕ) (t : ℝ) (a : ℤ) : Set (VxSpace n) :=
  {ω | (a : WithTop ℤ) ≤ chiMZ (vxGraph ω) m ∧ localSup (vxGraph ω) (t * Real.sqrt m) ≤ k}

/-- The set `B` of Eq. (9.3): the `ω ∈ Ω'` such that for every family of nonnegative weights
`(α_j)` there is `ω' ∈ A` with `∑_j α_j 1_{ω_j ≠ ω'_j} ≤ t √(∑_j α_j²)`. -/
def setB {n : ℕ} (A : Set (VxSpace n)) (t : ℝ) : Set (VxSpace n) :=
  {ω | ∀ α : Fin n → ℝ, (∀ j, 0 ≤ α j) →
    ∃ ω' ∈ A, (∑ j, if ω j ≠ ω' j then α j else 0) ≤ t * Real.sqrt (∑ j, α j ^ 2)}

/-- `N(G, e)` for `e = (i, j) ∈ E₀`: the number of independent sets of `G` of size `r` that
contain both `i` and `j`. -/
noncomputable def indepCount {n : ℕ} (G : SimpleGraph (Fin n)) (r : ℕ) (e : EdgeSlot n) : ℕ :=
  ((G.indepSetFinset r).filter (fun s => e.1.1 ∈ s ∧ e.1.2 ∈ s)).card

end TalagrandConc.Chromatic


