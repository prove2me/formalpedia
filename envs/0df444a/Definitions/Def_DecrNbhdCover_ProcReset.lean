-- Prove2me | Definitions.Def_DecrNbhdCover_ProcReset
-- name    : DecrNbhdCover_ProcReset
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T11:02:40.386756+00:00
-- url     : https://prove2.me/theorems/4d0fa282-940a-4275-901e-cfa9bfc5d356
-- title:
--   The input and the properties R1–R5 of Procedure ProcReset (Lemma 6.1)
-- statement:
--   The input has a graph $G=(V,E,\ell_G)$, $n\ge2$, $d>0$, and $k\ge2$ with $|V|\le n$ and $k^2$ an integer. The output is a collection $\mathcal C$ of clusters with, for each $C$, a set $T(C)\subseteq C$ and a value $d\le D_C\le d2^{14k^2}$, such that:
--
--   1. every vertex lies in at most $4k^4n^{2/k^2}$ clusters;
--   2. every vertex lies in exactly one set $T(C)$;
--   3. $B_G(v,D_C)\subseteq C$ for $v\in T(C)$;
--   4. $\mathrm{dist}_C(v,v')\le D_C$ for $v,v'\in T(C)$;
--   5. $\mathrm{dist}_C(v,v')\le64D_C$ for $v,v'\in C$.
--
--   Here $\mathrm{dist}_C$ is the distance in $G[C]$. This is the reset step of the neighborhood cover construction.
--
--   **Formalization Note** The input word is $K=k^2$, as $k$ itself may be irrational (§6 uses $k=\sqrt{\lceil16/\epsilon\rceil}$). The clusters are the entries of the output list.
-- source:
--   Chuzhoy, Mosenzon, A Unified and Simplified Framework for Dynamic Distance-Based Graph Problems (STOC 2027 submission, preprint, sha256 4278ef58f7a6a1c6a6ac1cde172bfd04b0f0652af498f3f8d09c6e94c1c352df), Lemma 6.1, p.45 (PDF 49); §6, p.48 (PDF 52)

import Mathlib
import Definitions.Def_DecrNbhdCover_Streams
import Definitions.Def_DecrNbhdCover_Session

set_option autoImplicit false

namespace DecrNbhdCover

open DynConnWC
open scoped ENNReal

/-! # The input and output of Procedure ProcReset (Lemma 6.1)

Chuzhoy, Mosenzon (STOC 2027 submission, sha256 4278ef58…), Lemma 6.1, p.45.

**Formalization Note.** `k` is real with `k²` an integer (§6, p.48 uses `k = √⌈16/ϵ⌉`), so the word given to the program is `K = k²`, with `k = √K`, `k⁴ = K²`, `n^{2/k²} = n^{2/K}`, `2^{14k²} = 2^{14K}`, and `n^{1/k} = n^{1/√K}`. `d > 0` is a rational. A static run: one block, and one output list
`Dp, Dq, |C|, C, |T|, T` per cluster. The value `D_C` is a rational. The clusters are the list's entries, so a repeated vertex set still counts as two clusters. -/

/-- One output cluster: the value `D_C = Dp/Dq`, the cluster `C`, and `T(C)`. -/
structure ResetCluster where
  Dp : ℕ
  Dq : ℕ
  C : List ℕ
  T : List ℕ

/-- The words of an output cluster. -/
def ResetCluster.words (r : ResetCluster) : List ℕ :=
  [r.Dp, r.Dq] ++ r.C.length :: r.C ++ r.T.length :: r.T

/-- The value `D_C`. -/
noncomputable def ResetCluster.DC (r : ResetCluster) : ℝ := (r.Dp : ℝ) / (r.Dq : ℝ)

/-- The input of ProcReset. -/
structure ResetInput where
  n : ℕ
  N₀ : ℕ
  edges : List (ℕ × ℕ × ℕ)
  d : ℚ
  K : ℕ

namespace ResetInput

variable (I : ResetInput)

/-- The conditions of Lemma 6.1: `n ≥ 2`, `d > 0`, `k ≥ 2`, `|V| ≤ n`. -/
structure Ok : Prop where
  n_ge : 2 ≤ I.n
  N_pos : 1 ≤ I.N₀
  N_le : I.N₀ ≤ I.n
  edges_ok : EdgesOk I.N₀ I.edges
  d_pos : 0 < I.d
  K_ge : 4 ≤ I.K

/-- The input words. -/
def words : List ℕ :=
  [I.n, I.K, I.N₀] ++ edgeWords I.edges ++ ratWords I.d

/-- The graph. -/
def G : Graph ℕ ℕ := ofEdges I.N₀ I.edges

end ResetInput

/-- Properties R1–R5 of the output clusters, and the bounds on `D_C` and on `C`, `T(C)`. -/
structure ResetOk (I : ResetInput) (rs : List ResetCluster) : Prop where
  sub : ∀ r ∈ rs, 0 < r.Dq ∧ (∀ v ∈ r.C, v ∈ I.G.V) ∧ ∀ v ∈ r.T, v ∈ r.C
  DC_ge : ∀ r ∈ rs, (I.d : ℝ) ≤ r.DC
  DC_le : ∀ r ∈ rs, r.DC ≤ (I.d : ℝ) * (2 : ℝ) ^ (14 * I.K)
  /-- R1. -/
  r1 : ∀ v ∈ I.G.V, ((rs.countP (fun r => decide (v ∈ r.C)) : ℕ) : ℝ) ≤
    4 * (I.K : ℝ) ^ 2 * (I.n : ℝ) ^ (2 / (I.K : ℝ))
  /-- R2. -/
  r2 : ∀ v ∈ I.G.V, rs.countP (fun r => decide (v ∈ r.T)) = 1
  /-- R3. -/
  r3 : ∀ r ∈ rs, ∀ v ∈ r.T, I.G.ball v r.DC ⊆ {u | u ∈ r.C}
  /-- R4. -/
  r4 : ∀ r ∈ rs, ∀ v ∈ r.T, ∀ v' ∈ r.T,
    (((I.G.induced {u | u ∈ r.C}).dist v v' : ℕ∞) : ℝ≥0∞) ≤ ENNReal.ofReal r.DC
  /-- R5. -/
  r5 : ∀ r ∈ rs, ∀ v ∈ r.C, ∀ v' ∈ r.C,
    (((I.G.induced {u | u ∈ r.C}).dist v v' : ℕ∞) : ℝ≥0∞) ≤ ENNReal.ofReal (64 * r.DC)

end DecrNbhdCover


