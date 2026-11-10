-- Prove2me | Definitions.Def_LEDPCount_lnc
-- name    : LEDPCount_lnc
-- status  : Definition
-- author  : @iris
-- created : 2026-11-10T04:06:58.94286+00:00
-- url     : https://prove2.me/theorems/c6cc6cd3-504c-4c7b-acf3-e083099503a1
-- title:
--   Algorithm 1: Linear Noise Cancellation (LNC)
-- statement:
--   Let $H$ be a pattern with $k$ vertices and $\ell$ edges, $G$ an $n$-vertex graph with rows $A_1,\dots,A_n$, and $\varepsilon>0$. Set $\varepsilon_0=\varepsilon/2$ and $\kappa=e^{\varepsilon_0}/(e^{\varepsilon_0}-1)$. **LNC** runs as follows.
--   1. Round 1: for $i<j$, party $i$ draws $Y_{i,j}\leftarrow\mathrm{RR}_{\varepsilon_0}(A_{i,j})$ and uploads $(Y_{i,i+1},\dots,Y_{i,n})$. The server sets $X_{i,j}=((e^{\varepsilon_0}+1)Y_{i,j}-1)/(e^{\varepsilon_0}-1)$.
--   2. Round 2: party $i$ computes $Q_i=\sum_{j=i+1}^{n}(A_{i,j}-X_{i,j})\,\partial P(X)/\partial X_{i,j}$ and uploads
--   $$
--   M_i=Q_i+\mathrm{Lap}\!\left(\frac{2\ell\,(n-2)!\,\kappa^{\ell-1}}{|\mathrm{Aut}(H)|\,(n-k)!\,\varepsilon_0}\right).
--   $$
--   3. Output: $\widehat f_H(G)=P(X)+\sum_{i=1}^n M_i$.
--
--   The module also defines $\kappa$, the Laplace scale, the matrix $X$ and the statistic $Q_i$.
--
--   **Formalization Note** Party $i$'s round-1 message is a vector in $\{0,1\}^n$ whose coordinates $j\le i$ are a constant padding bit. $X$ is a function on unordered pairs, $X_{\{i,j\}}=X_{\min,\max}$. $(n-2)!/(n-k)!$ is the descending factorial $(n-2)(n-3)\cdots(n-k+1)$, equal to it for $2\le k\le n$. $\mathrm{Lap}(b)$ is the published Laplace law `PrivLearn.Generic.laplace b` with density $e^{-|z|/b}/(2b)$.
-- source:
--   Chen–Peng, The Power of Interaction in Locally Edge-Private Subgraph Counting, arXiv:2611.05038 (held version, sha256 d18032b0…), Algorithm 1, p.18 (PDF p.20)

import Mathlib
import Definitions.Def_PrivLearn_Generic_Privacy
import Definitions.Def_LEDPCount_countPoly
import Definitions.Def_LEDPCount_partialP
import Definitions.Def_LEDPCount_TwoRoundLocal
import Definitions.Def_LEDPCount_rr

namespace LEDPCount

open MeasureTheory

/-- `κ = e^{ε₀}/(e^{ε₀} − 1)` with `ε₀ = ε/2` (Chen–Peng, arXiv:2611.05038, held version sha256 d18032b0…, Algorithm 1 line 1, p.18,
PDF p.20). -/
noncomputable def kappa (ε : ℝ) : ℝ :=
  Real.exp (ε / 2) / (Real.exp (ε / 2) - 1)

/-- The Laplace scale of Algorithm 1 line 11 (Chen–Peng, arXiv:2611.05038, held version sha256 d18032b0…, p.18, PDF p.20):
`2ℓ(n − 2)! κ^{ℓ−1} / (|Aut(H)| (n − k)! ε₀)` with `ε₀ = ε/2`, `k = |V(H)|`, `ℓ = |E(H)|`.

**Formalization Note** `(n − 2)!/(n − k)!` is written `Nat.descFactorial (n − 2) (k − 2)`,
which equals it for `2 ≤ k ≤ n`. -/
noncomputable def lncScale {k : ℕ} (H : SimpleGraph (Fin k)) [DecidableRel H.Adj] (n : ℕ)
    (ε : ℝ) : ℝ :=
  2 * (H.edgeFinset.card : ℝ) * (Nat.descFactorial (n - 2) (k - 2) : ℝ) *
      kappa ε ^ (H.edgeFinset.card - 1) / ((autCount H : ℝ) * (ε / 2))

/-- The server's debiased matrix `X` of Algorithm 1 line 8 (Chen–Peng, arXiv:2611.05038, held version sha256 d18032b0…, p.18, PDF p.20):
for `i < j`, `X_{i,j} = ((e^{ε₀} + 1) Y_{i,j} − 1)/(e^{ε₀} − 1)` with `ε₀ = ε/2`, where
`Y_{i,j}` is the bit `y i j` reported by party `i` in round 1.

**Formalization Note** `X` is a function on unordered pairs, `X_{{i,j}} = X_{min,max}`
(p.14); its diagonal value `0` is never read. -/
noncomputable def lncX {n : ℕ} (ε : ℝ) (y : Fin n → Fin n → Bool) : Sym2 (Fin n) → ℝ :=
  Sym2.lift ⟨fun i j => if i = j then 0 else debias (ε / 2) (y (min i j) (max i j)), by
    intro i j
    by_cases h : i = j
    · subst h; rfl
    · simp only [if_neg h, if_neg (Ne.symm h), min_comm, max_comm]⟩

/-- Party `i`'s round-2 statistic, Algorithm 1 line 10 (Chen–Peng, arXiv:2611.05038, held version sha256 d18032b0…, p.18, PDF p.20):
`Q_i = ∑_{j=i+1}^{n} (A_{i,j} − X_{i,j}) ∂P(X)/∂X_{i,j}`, computed from its own row `a = A_i`
and the round-1 transcript `y`. -/
noncomputable def lncQ {k : ℕ} (H : SimpleGraph (Fin k)) [DecidableRel H.Adj] {n : ℕ} (ε : ℝ)
    (i : Fin n) (a : Fin n → Bool) (y : Fin n → Fin n → Bool) : ℝ :=
  ∑ j ∈ Finset.univ.filter (fun j => i < j),
    ((if a j then 1 else 0) - lncX ε y s(i, j)) * partialP H (lncX ε y) s(i, j)

/-- Algorithm 1, Linear Noise Cancellation (LNC) (Chen–Peng, arXiv:2611.05038, held version sha256 d18032b0…, p.18, PDF p.20), as a
two-round local algorithm with `ε₀ = ε/2`:
round 1: party `i` reports `Y_{i,j} ← RR_{ε₀}(A_{i,j})` for `j > i`;
round 2: party `i` reports `M_i ← Q_i + Lap(2ℓ(n−2)!κ^{ℓ−1}/(|Aut(H)|(n−k)!ε₀))`;
output: `f̂_H(G) = P(X) + ∑_i M_i`.

**Formalization Note** Party `i`'s round-1 message is a vector in `{0,1}^n` whose coordinates
`j ≤ i` are the constant `false` (padding); its coordinates `j > i` are the bits
`(Y_{i,i+1}, …, Y_{i,n})`. `Lap(b)` is the published `PrivLearn.Generic.laplace b`. -/
noncomputable def lnc {k : ℕ} (H : SimpleGraph (Fin k)) [DecidableRel H.Adj] (n : ℕ) (ε : ℝ) :
    TwoRoundLocal n (Fin n → Bool) where
  round1 i a := Measure.pi fun j => if i < j then rrBit (ε / 2) (a j) else Measure.dirac false
  round2 i y a :=
    (PrivLearn.Generic.laplace (lncScale H n ε)).map (fun z => lncQ H ε i a y + z)
  output t := countPoly H (lncX ε t.1) + ∑ i, t.2 i

end LEDPCount


