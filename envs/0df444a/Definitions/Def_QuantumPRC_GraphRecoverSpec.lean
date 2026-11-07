-- Prove2me | Definitions.Def_QuantumPRC_GraphRecoverSpec
-- name    : QuantumPRC_GraphRecoverSpec
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T11:36:40.56967+00:00
-- url     : https://prove2.me/theorems/61708e6c-1381-4e77-82e6-1e61c9a47666
-- title:
--   The degree $d(n)$ (220), the sampler of Construction 8.10, and graph sampling with phase recovery (machine form of Theorem 7.1)
-- statement:
--   Fix a positive rational $\gamma\le\min\{2^{-32},p/2\}$ and a radius function $t$. The degree is
--
--   $$
--   d(n):=16\Big\lfloor\frac1{16}\min\Big\{\lceil\log_2(2n)\rceil^2,\ \frac{\gamma n}{t(n)}\Big\}\Big\rfloor\qquad(220).
--   $$
--
--   **Construction 8.10** samples independent uniform permutations $\pi_1,\dots,\pi_d$ of $[n]$, sets $B=P_1\oplus\dots\oplus P_d$ with $(P_a)_{i,j}=1$ iff $j=\pi_a(i)$, and outputs the bipartite graph on $[2n]$ with biadjacency matrix $B$. `goodProb` is the probability that this graph is $(t(n),d(n))$-good for a given $v$.
--
--   **Graph sampling and phase recovery** (`GraphRecoverSpec p`): a PPT machine $\mathsf{GS}(1^n,1^T;r)$ outputs (the adjacency code of) a simple graph $G$ on $[2n]$, and a deterministic polynomial-time machine $\mathsf{Rec}(1^T,G,e)$ outputs a $2n$-bit string, such that for every sequence $n_k\to\infty$ and $T_k=o(n_k\log\log n_k/\log n_k)$, for all large $k$ and all $u,v\in\{0,1\}^{2n_k}$ with $|\mathrm{supp}(u)\cup\mathrm{supp}(v)|\le T_k$:
--
--   1. every output graph satisfies $\mathrm{wt}(v\oplus Au)\le p\,n_k$;
--   2. $\Pr_{G\leftarrow\mathsf{GS}}[\mathsf{Rec}(G,v\oplus Au)=u]\ge1-\nu(n_k)$ for a negligible $\nu$.
--
--   This is the conclusion of Theorem 7.1 with the radius as an input of the algorithms.
--
--   **Formalization Note** $\lceil\log_2(2n)\rceil$ is `Nat.clog 2 (2n)`; at $t(n)=0$, Lean's $\gamma n/0=0$ gives $d(n)=0$ (the empty graph). Output graphs must be valid adjacency codes (symmetric, zero diagonal). For a radius function $t$ computable in polynomial time, taking $n_k=k$, $T_k=t(k)$ gives the printed form of Theorem 7.1.
-- source:
--   Hsieh, Yamada, Quantum Pseudorandom Error-Correcting Codes, arXiv:2609.38986 (version of October 29, 2026, sha256 6901b59d1cbcf0183f98f2951ab17c9baae4e341e5b2a3c767d1ae93e77976db), Eq. (220), p.58; Construction 8.10, p.59; Theorem 7.1, p.40

import Mathlib
import Definitions.Def_QuantumPRC_recover
import Definitions.Def_QuantumPRC_Assumption5

open Matrix Filter Asymptotics

namespace QuantumPRC

/-- **The degree `d(n)`**, Eq. (220). Hsieh, Yamada, arXiv:2609.38986 (sha256 6901b59d…), p.58: "Fix a
positive rational constant `γ ≤ min{2^{−32}, p/2}` and choose before sampling
`d(n) := 16 ⌊(1/16) min{⌈log₂(2n)⌉², γn/t(n)}⌋`."

**Formalization Note.** `⌈log₂(2n)⌉` is `Nat.clog 2 (2n)`. At `t(n) = 0` Lean's `γn/0 = 0` gives
`d(n) = 0` (the empty graph), the only reading under which `t(n) = 0` is meaningful. -/
noncomputable def degParam (γ : ℝ) (t : ℕ → ℕ) (n : ℕ) : ℕ :=
  16 * ⌊(1 / 16 : ℝ) * min ((Nat.clog 2 (2 * n) : ℝ) ^ 2) (γ * n / t n)⌋₊

/-- The bipartite graph on `[2n]` produced from permutations `π_1, …, π_d` of `[n]`
(Construction 8.10, p.59): `(P_a)_{i,j} = 1` exactly when `j = π_a(i)`, `B := P_1 ⊕ ⋯ ⊕ P_d`
(so `B_{x,y} = 1` iff an odd number of `a` have `π_a(x) = y`), and `A = [[0, B], [B⊤, 0]]`. -/
def permGraph {n d : ℕ} (π : Fin d → Equiv.Perm (Fin n)) : SimpleGraph (Fin (2 * n)) :=
  SimpleGraph.fromRel fun i j => ∃ x y : Fin n, i = vL x ∧ j = vR y ∧
    Odd (Finset.univ.filter fun a => π a x = y).card

/-- **`Pr_{G←GraphSample(1^n)}[G is (t(n), d(n))-good for v]`** for the sampler of Construction 8.10,
p.59 ("1. Choose independent uniform permutations `π_1, …, π_d : [n] → [n]`. 2. […] 3. Output the graph
`G` with adjacency matrix `A`"), with `d = d(n)` of (220). -/
noncomputable def goodProb (γ : ℝ) (t : ℕ → ℕ) (n : ℕ) (v : Bits (2 * n)) : ℝ := by
  classical
  exact avg fun π : Fin (degParam γ t n) → Equiv.Perm (Fin n) =>
    if IsGood (t n) (degParam γ t n) v (permGraph π) then 1 else 0

/-- `n log log n / log n`, the radius scale of Theorem 7.1, Eq. (107). -/
noncomputable def radiusScale (n : ℕ) : ℝ := n * Real.log (Real.log n) / Real.log n

/-- Row-major adjacency code of a graph on `[N]`. -/
def adjCode {N : ℕ} (G : SimpleGraph (Fin N)) [DecidableRel G.Adj] : List Bool :=
  (List.ofFn fun i : Fin N => List.ofFn fun j : Fin N => decide (G.Adj i j)).flatten

/-- A list is the adjacency code of a simple graph on `[N]`: length `N²`, symmetric, zero diagonal. -/
def IsGraphCode (N : ℕ) (l : List Bool) : Prop :=
  l.length = N * N ∧ ∀ i j : Fin N,
    l.getD (i.val * N + j.val) false = l.getD (j.val * N + i.val) false ∧
    l.getD (i.val * N + i.val) false = false

/-- The graph on `[N]` read from an adjacency code (symmetrized and loop-free, so total). -/
def graphOfCode (N : ℕ) (l : List Bool) : SimpleGraph (Fin N) :=
  SimpleGraph.fromRel fun i j => l.getD (i.val * N + j.val) false = true

instance (N : ℕ) (l : List Bool) : DecidableRel (graphOfCode N l).Adj := by
  intro i j; unfold graphOfCode; infer_instance

/-- `|supp(u) ∪ supp(v)|`. -/
def suppUnionCard {N : ℕ} (u v : Bits N) : ℕ :=
  (Finset.univ.filter fun i => u i = true ∨ v i = true).card

/-- **Graph sampling and phase recovery, machine form** (the conclusion of Theorem 7.1 as used in
this mission). Hsieh, Yamada, arXiv:2609.38986 (sha256 6901b59d…), Theorem 7.1, p.40: GraphSample is
a PPT algorithm that takes `1^n` and outputs a simple graph `G` on `[2n]`; Recover is a deterministic
polynomial-time algorithm that takes `G` and `e ∈ {0,1}^{2n}` and outputs a `2n`-bit string; for all
sufficiently large `n` and all `u, v` with `|supp(u) ∪ supp(v)| ≤ t(n)`, (i) every output graph
satisfies `wt(v ⊕ Au) ≤ pn`, and (ii) `Pr_{G←GraphSample(1^n)}[Recover(G, v ⊕ Au) = u] ≥ 1 − negl(n)`.

Here both machines also read the radius in unary: `GS(1^n, 1^T; r)` with `r ∈ {0,1}^{gc(n)}`, and
`Rec(1^T, G, e)`; the guarantee holds along every sequence `n_k → ∞` with `T_k = o(n_k log log n_k /
log n_k)`, with failure probability negligible in `n_k`.

**Formalization Note.** Graphs are output as adjacency codes, which must be valid. For a radius
function `t` computable from `1^n` in polynomial time, taking `n_k = k`, `T_k = t(k)` and composing
machines gives the printed statement. -/
def GraphRecoverSpec (p : ℝ) (gc : ℕ → ℕ) (GS Rec : List Bool → List Bool) : Prop :=
  PolyBounded gc ∧ CookPvsNP.PolyTimeComputable GS ∧ CookPvsNP.PolyTimeComputable Rec ∧
  (∀ n T (r : Bits (gc n)), IsGraphCode (2 * n) (GS (tupleCode [unary n, unary T, bits r]))) ∧
  ∀ nk Tk : ℕ → ℕ, Tendsto nk atTop atTop →
    (fun k => (Tk k : ℝ)) =o[atTop] (fun k => radiusScale (nk k)) →
    ∃ ν : ℕ → ℝ, Negligible ν ∧ ∀ᶠ k in atTop, ∀ u v : Bits (2 * nk k),
      suppUnionCard u v ≤ Tk k →
      (∀ r : Bits (gc (nk k)),
        (wt (xorB v (adjMul (graphOfCode (2 * nk k)
          (GS (tupleCode [unary (nk k), unary (Tk k), bits r]))) u)) : ℝ) ≤ p * nk k) ∧
      1 - ν (nk k) ≤ avg fun r : Bits (gc (nk k)) =>
        let l := GS (tupleCode [unary (nk k), unary (Tk k), bits r])
        if Rec (tupleCode [unary (Tk k), l, bits (xorB v (adjMul (graphOfCode (2 * nk k) l) u))]) =
            bits u then 1 else 0

end QuantumPRC


