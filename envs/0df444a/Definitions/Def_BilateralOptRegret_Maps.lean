-- Prove2me | Definitions.Def_BilateralOptRegret_Maps
-- name    : BilateralOptRegret_Maps
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T05:40:08.169257+00:00
-- url     : https://prove2.me/theorems/a85b66a1-776e-4822-aa1b-7e60d5cbff86
-- title:
--   (17), Algorithm 2, (20) — target and queryable sets, BuildTargetMaps, the potential
-- statement:
--   Given $G$, $\hat F$ and a phase precision $\varepsilon$, with $\widehat{\mathrm{OPT}}=\max_{x\in G}\hat r(x)$, the **target** and **queryable** sets are
--   $$G_{\mathrm{tar}}=\{x\in G:\hat r(x)\ge\widehat{\mathrm{OPT}}-20\varepsilon\ell_K\},\qquad G_{\mathrm{qry}}=\{x\in G:\hat r(x)\ge\widehat{\mathrm{OPT}}-100\varepsilon\ell_K\}.$$
--   **Algorithm 2** builds maps $v_j$ row by row, starting from $v_{-1}=\mathrm{id}$: in row $j$, for each internal $i$, if the current representative $x_{q_i,j}$ is not in $G_{\mathrm{qry}}$ and some $u\in I_i$ has $x_{u,j}\in G_{\mathrm{tar}}$, then $q_i$ is replaced by one such $u$; otherwise it is unchanged. Boundary indices never change. A map $v$ is **admissible** if $v(i)\in I_i$ for internal $i$, and for such a map the **profit potential** is
--   $$\Phi(v,j)=\sum_{i=1}^{K-2}\big(r(x_{v(i),j})-r(x_{i-h_i,j})\big).$$
--   The potential is the device that bounds the number of replacements.
--
--   **Formalization Note** `repAfter sel Gtar Gqry t` is the map after $t$ rows, so $v_j$ is `repAfter (j+1)` and $v_{-1}$ is `repAfter 0`. Each index reads only its own value, so the inner loop is a pointwise update. On an empty $G$, $\widehat{\mathrm{OPT}}$ takes the value $0$; such an input never satisfies (15).
-- source:
--   Castiglioni, Lunghi, Marchesi, Optimal Regret for Profit Maximization in Bilateral Trade (manuscript, sha256 aafed174…), (17), p.27; Algorithm 2, p.29; (20), p.30

import Mathlib
import Definitions.Def_BilateralOptRegret_Model
import Definitions.Def_BilateralOptRegret_Dyadic

namespace BilateralOptRegret

open MeasureTheory

/-! # The target and queryable sets (17), Algorithm 2 and the potential (20)

Castiglioni, Lunghi, Marchesi (manuscript, sha256 aafed174…), (17), p.27; Algorithm 2, p.29; (20), p.30.

**Formalization Note.** `optHat` is `max_{x ∈ G} r̂(x)` (p.26), with the value `0` on an empty `G`, an input
which never meets (15). Here `ε` is the phase precision `ε_i` and `i` a column. `repAfter sel Gtar Gqry t` is the
map after `t` rows of Algorithm 2: so `v_j = repAfter (j + 1)` and `v_{−1} = repAfter 0 = id` (p.30). In a row each
index `i` reads only its own current value `q_i`, so the inner loop of Algorithm 2 is a pointwise
update and its order is immaterial. "Choose one such `u`" is the selection rule `sel`. -/

/-- `max_{x ∈ G} r̂(x)` (p.26). -/
noncomputable def optHat {K : ℕ} (G : Finset (Grid K)) (Fhat : Grid K → ℝ) : ℝ :=
  if h : G.Nonempty then G.sup' h (rhat Fhat) else 0

/-- `G_tar = {x ∈ G : r̂(x) ≥ OPT^ − 20 ε ℓ_K}`, (17), p.27. -/
noncomputable def gTar {n : ℕ} (G : Finset (Act n)) (Fhat : Act n → ℝ) (ε : ℝ) : Finset (Act n) := by
  classical
  exact G.filter fun q => optHat G Fhat - 20 * ε * (ell n : ℝ) ≤ rhat Fhat q

/-- `G_qry = {x ∈ G : r̂(x) ≥ OPT^ − 100 ε ℓ_K}`, (17), p.27. -/
noncomputable def gQry {n : ℕ} (G : Finset (Act n)) (Fhat : Act n → ℝ) (ε : ℝ) : Finset (Act n) := by
  classical
  exact G.filter fun q => optHat G Fhat - 100 * ε * (ell n : ℝ) ≤ rhat Fhat q

/-- The candidates `{u ∈ I_i : x_{u,j} ∈ G_tar}` (Algorithm 2, line 5). -/
def candidates {n : ℕ} (Gtar : Finset (Act n)) (i j : Idx n) : Finset (Idx n) :=
  (perm i).filter fun u => (u, j) ∈ Gtar

/-- One row of Algorithm 2, lines 3–10. -/
def stepRow {n : ℕ} (sel : Finset (Idx n) → Idx n) (Gtar Gqry : Finset (Act n)) (j : Idx n)
    (q : Idx n → Idx n) : Idx n → Idx n :=
  fun i =>
    if i ∈ internal n ∧ (q i, j) ∉ Gqry ∧ (candidates Gtar i j).Nonempty then
      sel (candidates Gtar i j)
    else
      q i

/-- **Algorithm 2, p.29**, BuildTargetMaps: the map after `t` rows. -/
def repAfter {n : ℕ} (sel : Finset (Idx n) → Idx n) (Gtar Gqry : Finset (Act n)) :
    ℕ → Idx n → Idx n
  | 0 => id
  | t + 1 => stepRow sel Gtar Gqry (Fin.ofNat (Kof n) t) (repAfter sel Gtar Gqry t)

/-- The number of replacements `∑_{j=1}^{K−1} ∑_{i=0}^{K−1} 1{v_j(i) ≠ v_{j−1}(i)}` (Lemma 7.7, p.34), for the
maps `v_j = v (j + 1)`, `v_{−1} = v 0`. -/
def replacements {n : ℕ} (v : ℕ → Idx n → Idx n) : ℕ :=
  ∑ j ∈ Finset.Ioc 0 (2 ^ n), (Finset.univ.filter fun i : Idx n => v (j + 1) i ≠ v j i).card

/-- `v` is admissible: `v(i) ∈ I_i` for internal `i` (p.30, before (20)). -/
def Admissible {n : ℕ} (v : Idx n → Idx n) : Prop := ∀ i ∈ internal n, v i ∈ perm i

/-- The profit potential `Φ(v, j) = ∑_{i=1}^{K−2} (r(x_{v(i),j}) − r(x_{i−h_i,j}))`, (20), p.30. -/
noncomputable def potential {n : ℕ} (L : Measure (ℝ × ℝ)) (v : Idx n → Idx n) (j : Idx n) : ℝ :=
  ∑ i ∈ internal n, (r L (pt (Kof n) (v i, j)) - r L (pt (Kof n) (lo i, j)))

end BilateralOptRegret


