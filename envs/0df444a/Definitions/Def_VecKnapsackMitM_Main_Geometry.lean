-- Prove2me | Definitions.Def_VecKnapsackMitM_Main_Geometry
-- name    : VecKnapsackMitM_Main_Geometry
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-09T20:34:15.135564+00:00
-- url     : https://prove2.me/theorems/03ea9bad-8b2a-4dbf-8ba2-e27035125569
-- title:
--   Embedding, range and matching (Definition 4.3); orthogonal range searching on the machine (Lemma 4.5)
-- statement:
--   Definition 4.3 and the machine interface of Lemma 4.5. Coordinates in $\mathbb R\cup\{\pm\infty\}$ are `EReal`. Indices are 0-based, so `maxIdx S` and `minIdx S` are the paper's $\max(S)-1$ and $\min(S)-1$ (shifted uniformly; no comparison $\max(S_1)<\min(S_2)$ changes), with $\max(\emptyset)=-\infty$ and $\min(\emptyset)=+\infty$.
--
--   * `Matched inst S₁ S₂`: $\bar w(S_1)+\bar w(S_2)\le\bar W$ and $\max(S_1)<\min(S_2)$.
--   * `embed I S` $\in(\mathbb R\cup\{-\infty\})^{d+1}$: coordinates $\bar w_1(S),\dots,\bar w_d(S)$, then $\max(S)$.
--   * `rangeLo d`, `rangeHi inst S`: the box $[0,b_1]\times\dots\times[0,b_d]\times[-\infty,b_{d+1}]$ with $b_t=\bar W_t-\bar w_t(S)$ and $b_{d+1}=\min(S)-1$ ($=+\infty$ for $S=\emptyset$, since $\top-1=\top$ in `EReal`).
--   * `InBox lo hi x`: $lo_j\le x_j\le hi_j$ for all $j$ (closed box).
--   * `erTag e`: $1$ for $-\infty$, $2$ for $+\infty$, $0$ otherwise; an extended real is stored as this tag in an index cell and `e.toReal` in a real cell.
--   * `orsBuildInput D m x pr`: $N[0]=D$, $N[1]=m$, then the tags of all coordinates (object by object); the real cells hold the profits, then the coordinates' real parts in the same order.
--   * `queryState s D lo hi`: from the post-build state $s$, the box word $lo_0,hi_0,\dots,lo_{D-1},hi_{D-1}$ is written (tags in $N$, reals in $R$) at the address $q=N[0]$ designated by the build, and the program counter is reset to $0$.
--   * `ORSAnswerOK x pr lo hi ans`: $ans=0$ ($\bot$) and no point lies in the box, or $ans=k+1$ for an object $k$ in the box of maximum profit among the objects in the box (ties: any).
-- source:
--   Bringmann, Kulik, Węgrzycki (2026), Fine-Grained Complexity of Approximating Vector Knapsack: A Faster Algorithm and Equivalence with k-SUM in 2D, STOC 2027 submission, SHA-256 966f42f7…10ac98; §4.3, Definition 4.3 and Lemma 4.5, printed p. 18 (PDF 19)

import Mathlib
import Definitions.Def_MatMulTimeLP_RealRAM
import Definitions.Def_VecKnapsackMitM_Main_Instance
import Definitions.Def_VecKnapsackMitM_Main_Machine

namespace VecKnapsackMitM.Main

open MatMulTimeLP

/-! Meet in the middle via orthogonal range searching (Bringmann, Kulik, Węgrzycki 2026, §4.3,
printed p. 18, PDF 19). Coordinates in `ℝ ∪ {−∞, ∞}` are `EReal`. Item indices are 0-based
(the paper's item `i + 1` is `i`), so `max(S)` and `min(S)` are shifted by one against the
paper, uniformly for all sets, which changes no comparison `max(S₁) < min(S₂)` and no
`max(S₁) ≤ min(S₂) − 1`. -/

/-- `max(S)` as an extended real: the largest (0-based) index in `S`; `max(∅) = −∞`. -/
noncomputable def maxIdx {n : ℕ} (S : Finset (Fin n)) : EReal :=
  S.sup fun i => (((i.val : ℝ)) : EReal)

/-- `min(S)` as an extended real: the smallest (0-based) index in `S`; `min(∅) = ∞`. -/
noncomputable def minIdx {n : ℕ} (S : Finset (Fin n)) : EReal :=
  S.inf fun i => (((i.val : ℝ)) : EReal)

/-- `S₁` and `S₂` can be matched: `w̄(S₁) + w̄(S₂) ≤ W̄` and `max(S₁) < min(S₂)`. -/
def Matched {d n : ℕ} (inst : Instance d n) (S₁ S₂ : Finset (Fin n)) : Prop :=
  (∀ t : Fin d, inst.toItems.weight S₁ t + inst.toItems.weight S₂ t ≤ inst.W t) ∧
    maxIdx S₁ < minIdx S₂

/-- Definition 4.3, the embedding `embed(S) ∈ (ℝ ∪ {−∞})^{d+1}`: coordinate `t < d` is
`w̄_{t+1}(S)`, the last coordinate (index `d`) is `max(S)`. -/
noncomputable def embed {d n : ℕ} (I : Items d n) (S : Finset (Fin n)) : Fin (d + 1) → EReal :=
  fun j => if h : j.val < d then ((I.weight S ⟨j.val, h⟩ : ℝ) : EReal) else maxIdx S

/-- Lower corner of every range: `0` in the first `d` coordinates, `−∞` in the last. -/
noncomputable def rangeLo (d : ℕ) : Fin (d + 1) → EReal :=
  fun j => if j.val < d then 0 else ⊥

/-- Definition 4.3, upper corner of `range_W̄(S) = [0, b₁] × … × [0, b_d] × [−∞, b_{d+1}]`:
`b_{t+1} = W̄_{t+1} − w̄_{t+1}(S)` for `t < d`, and `b_{d+1} = min(S) − 1` (`= ∞` for
`S = ∅`). -/
noncomputable def rangeHi {d n : ℕ} (inst : Instance d n) (S : Finset (Fin n)) :
    Fin (d + 1) → EReal :=
  fun j => if h : j.val < d then
      ((inst.W ⟨j.val, h⟩ - inst.toItems.weight S ⟨j.val, h⟩ : ℝ) : EReal)
    else minIdx S - 1

/-- The point `x` lies in the closed box `[lo₁, hi₁] × … × [lo_m, hi_m]`. -/
def InBox {m : ℕ} (lo hi x : Fin m → EReal) : Prop := ∀ j, lo j ≤ x j ∧ x j ≤ hi j

/-! Orthogonal range searching on the machine (Lemma 4.5). An extended real `e` is stored as a
tag in an index cell (`0` finite, `1` for `−∞`, `2` for `+∞`) and a real cell holding
`e.toReal` (`0` for `±∞`). -/

/-- The tag of an extended real: `1` for `−∞`, `2` for `+∞`, `0` otherwise. -/
noncomputable def erTag (e : EReal) : ℕ := if e = ⊥ then 1 else if e = ⊤ then 2 else 0

/-- Build input of the range-searching structure with `m` objects in dimension `D`, object `k`
with point `x k` and profit `pr k`: index cells `N[0] = D`, `N[1] = m`, then the tags of
`x 0 0, …, x 0 (D−1), x 1 0, …` from `N[2]` on; real cells: the profits `pr 0, …, pr (m−1)`,
then the real parts of the coordinates in the same order as the tags. -/
noncomputable def orsBuildInput (D m : ℕ) (x : Fin m → Fin D → EReal) (pr : Fin m → ℝ) :
    State :=
  initState2 (finVec pr ++ (List.finRange m).flatMap fun k => finVec fun j => (x k j).toReal)
    ([D, m] ++ (List.finRange m).flatMap fun k => (List.finRange D).map fun j => erTag (x k j))

/-- Coordinate `k` of the query word `lo₀, hi₀, lo₁, hi₁, …` of the box `[lo, hi]`. -/
noncomputable def boxWord {D : ℕ} (lo hi : Fin D → EReal) (k : ℕ) : EReal :=
  if h : k / 2 < D then (if k % 2 = 0 then lo ⟨k / 2, h⟩ else hi ⟨k / 2, h⟩) else 0

/-- The state in which a query with the box `[lo, hi]` starts, from the post-build state `s`:
program counter `0`; the build designates the query address `q = s.N 0`, and the box word
`lo₀, hi₀, …, lo_{D−1}, hi_{D−1}` is written with its tags in `N[q], …, N[q + 2D − 1]` and its
real parts in `R[q], …, R[q + 2D − 1]`; every other cell is as left by the build. -/
noncomputable def queryState (s : State) (D : ℕ) (lo hi : Fin D → EReal) : State :=
  ⟨0, fun i => if s.N 0 ≤ i ∧ i < s.N 0 + 2 * D then (boxWord lo hi (i - s.N 0)).toReal
      else s.R i,
    fun i => if s.N 0 ≤ i ∧ i < s.N 0 + 2 * D then erTag (boxWord lo hi (i - s.N 0))
      else s.N i⟩

/-- `ans` (read from `N[1]` after a query) is a correct answer for the box `[lo, hi]`: `0` (`⊥`)
when no object's point lies in the box, otherwise `k + 1` for an object `k` whose point lies in
the box and whose profit is maximum among all objects with points in the box (ties: any). -/
def ORSAnswerOK {D m : ℕ} (x : Fin m → Fin D → EReal) (pr : Fin m → ℝ)
    (lo hi : Fin D → EReal) (ans : ℕ) : Prop :=
  (ans = 0 ∧ ∀ k, ¬ InBox lo hi (x k)) ∨
    ∃ k : Fin m, ans = k.val + 1 ∧ InBox lo hi (x k) ∧
      ∀ k' : Fin m, InBox lo hi (x k') → pr k' ≤ pr k

end VecKnapsackMitM.Main


