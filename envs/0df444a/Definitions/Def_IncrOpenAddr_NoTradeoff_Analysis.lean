-- Prove2me | Definitions.Def_IncrOpenAddr_NoTradeoff_Analysis
-- name    : IncrOpenAddr_NoTradeoff_Analysis
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-10T04:37:21.926404+00:00
-- url     : https://prove2.me/theorems/e7e820d8-1180-4f63-82a1-e7feb5ac7804
-- title:
--   Direct attempts X, thresholds θ_j, bad subtrees Y and Z (8), Table 1 (J, K, I), the query's waiting rule and safety, expensive nodes
-- statement:
--   All objects are read off the run of `Algorithm` on a key list $xs$ and an outcome $\omega$.
--
--   **Direct attempts (§2.4), §2 algorithm.** $\theta_j=2^j/(50j^6)$. For a constant level $\lambda$, $X_{i,\lambda,k}$ is the number of current-array insertions of epoch $i$ whose element has $T_i[\lambda,k]$ as level-$\lambda$ ancestor; for $j>\lambda$, $X_{i,j,k}$ is the number of insertions of phase $j$ of epoch $i+1$ that call TryInsertSubtree$(x,i,j)$ with target $T_i[j,k]$. $Y_{i,j,k}=1$ iff $X_{i,j,k}<\theta_j$ ($j>\lambda$), and $Y_{i,\lambda,k}=1$ iff $X_{i,\lambda,k}<2^{\lambda+1}-\theta_{\lambda+1}/4$. The subtree of $T_i[j,k]$ is **bad**, $Z_{i,j,k}=1$: for $\lambda<j\le2\lambda+1$, iff some node of the subtree at levels $\lambda$ through $j$ has $Y=1$; for $j>2\lambda+1$, with $h=\lfloor j/2\rfloor$, iff
--   $$Y_{i,j,k}=1\quad\text{or}\quad\sum_{k'=2^{j-h}k}^{2^{j-h}(k+1)-1}Z_{i,h,k'}\ \ge\ 2^{j/4}.\tag{8}$$
--
--   **Table 1 and the waiting rule (§4).** For a key $x$ and tree $T_i$ with ancestors $a_1=L_i(x),a_2,\dots$ (levels $1,2,\dots$): $J_i(x)=J(g_i(x))$; $K_i(x)=K+1$ for the largest level $K$ such that $a_K$ has bit $1$ and $a_j$ has bit $1$ for every $j\in[J_i(x),K]$, and $K_i(x)=1$ if there is none; $S_i(x)$ is $x$'s level-$K_i(x)$ home subtree (the whole tree if $K_i(x)$ exceeds the height); $C(L)$ is the largest $J_1$ of an element of leaf $L$ ($1$ if $L$ is empty); and
--   $$I(x)=100\cdot\max\{K_1(x),\ C(L)\},$$
--   the maximum over $L_1(x)$ and the leaves of $S_1(x)$. With $I$ standing for $I(x)$, the query for $x$ **waits** for a node $v$ of $T_i$ iff $i\le\min\{I,\alpha\}$ and either $v$ is an ancestor of $L_i(x)$ at level at most $J_i(x)$ (at most $\max\{J_1(x),I\}$ when $i=1$), or $v$ lies in $S_i(x)$. $x$ is **safe** (with $I$) if every node holding $x$ is one the query waits for.
--
--   **Expensive nodes (§4.2), §4 algorithm.** Node $V$ is expensive after $t$ insertions if, among them, (1) a current-array insertion ran TryInsertSubtree with target $V$; (2) a cleanup attempt in a nonfinal phase had target $V$ and placed its element below $V$; (3) $V$ is the root of its tree and a final-phase cleanup attempt succeeded in that tree; or (4) $V\in T_1$ and step 3 of an insertion in an epoch $s>100$ selected $V$.
--
--   **Formalization Note.** $J$, $C$, $I$ take values in $\mathbb N\cup\{\infty\}$ ($J=\infty$ only for priority $0$, a null event). `nodeOf` finds the node holding a key.
-- source:
--   Farach-Colton, Krapivin, Kuszmaul, Incremental Open Addressing Has No Time-Space Tradeoff, arXiv:2611.04186 (manuscript sha256 9486c2b8…), p. 12–13 (PDF 13–14), θ_j, X, Y, (8); p. 19–21 (PDF 20–22), Table 1, queries, safety; p. 23 (PDF 24), expensive nodes

import Mathlib
import Definitions.Def_IncrOpenAddr_NoTradeoff_Layout
import Definitions.Def_IncrOpenAddr_NoTradeoff_HashModel
import Definitions.Def_IncrOpenAddr_NoTradeoff_Algorithm

set_option autoImplicit false

/-!
# The objects of the analysis: direct attempts, bad subtrees, Table 1, safety, expensive nodes

Farach-Colton, Krapivin, Kuszmaul, arXiv:2611.04186 (manuscript sha256 9486c2b8…):
direct attempts, `θ_j`, `X`, `Y` (p. 12, PDF 13), bad subtrees `Z` and (8) (p. 13, PDF 14);
Table 1, the query's waiting rule and safety (p. 19–21, PDF 20–22); expensive nodes (p. 23,
PDF 24).  All of them are read off the run of `Def_IncrOpenAddr_NoTradeoff_Algorithm`.
-/

namespace IncrOpenAddr.NoTradeoff

variable {K : Type} [LinearOrder K]

/-! ## Direct attempts and bad subtrees (§2.4); runs of the §2 algorithm -/

/-- `θ_j = 2^j / (50 j⁶)`. -/
noncomputable def theta (j : ℕ) : ℝ := (2 : ℝ) ^ j / (50 * (j : ℝ) ^ 6)

/-- `X_{i,j,k}`, the number of direct attempts on `T_i[j, k]` in the run of the §2 algorithm on
`xs`: for `j = λ`, the current-array insertions of epoch `i` whose element has `T_i[λ, k]` as its
level-`λ` ancestor; for `j > λ`, the insertions of phase `j` of epoch `i + 1` that call
`TryInsertSubtree(x, i, j)` with target `T_i[j, k]`. -/
noncomputable def Xcount (lam n : ℕ) (η : ℝ) (ω : Outcome K n) (xs : List K) (i j k : ℕ) : ℕ :=
  if j = lam then
    ((recs .sec2 n η ω xs).filter fun r =>
      decide (r.epoch = i) && !r.s2.caTargets.isEmpty &&
        decide (leafOf ω r.placedKey i / 2 ^ (lam - 1) = k)).length
  else
    ((recs .sec2 n η ω xs).filter fun r =>
      decide (r.epoch = i + 1) && decide (r.phase = j) &&
        decide (r.s2.cleanupTarget = some ⟨i, j, k⟩)).length

/-- `Y_{i,j,k}`: `1` iff `X_{i,j,k} < θ_j` (for `j > λ`), resp. `X_{i,λ,k} < 2^{λ+1} - θ_{λ+1}/4`. -/
noncomputable def Yb (lam n : ℕ) (η : ℝ) (ω : Outcome K n) (xs : List K) (i j k : ℕ) : Bool :=
  if j = lam then decide ((Xcount lam n η ω xs i j k : ℝ) < (2 : ℝ) ^ (lam + 1) - theta (lam + 1) / 4)
  else decide ((Xcount lam n η ω xs i j k : ℝ) < theta j)

/-- `Z_{i,j,k}` (bad subtree): for `λ < j ≤ 2λ + 1`, some `Y` of the subtree of `T_i[j, k]` at
levels `λ` through `j` is `1`; for `j > 2λ + 1`, with `h = ⌊j/2⌋`, `Y_{i,j,k} = 1` or
`Σ_{k' = 2^{j-h} k}^{2^{j-h}(k+1) - 1} Z_{i,h,k'} ≥ 2^{j/4}` (8). -/
noncomputable def Zb (lam n : ℕ) (η : ℝ) (ω : Outcome K n) (xs : List K) (i : ℕ) :
    ℕ → ℕ → Bool
  | j, k =>
    if _h : j ≤ 2 * lam + 1 then
      (subtreeNodesFrom lam ⟨i, j, k⟩).any fun v => Yb lam n η ω xs i v.level v.idx
    else
      Yb lam n η ω xs i j k ||
        decide ((2 : ℝ) ^ ((j : ℝ) / 4) ≤
          (((List.range (2 ^ (j - j / 2))).filter fun t =>
            Zb lam n η ω xs i (j / 2) (2 ^ (j - j / 2) * k + t)).length : ℝ))
termination_by j => j
decreasing_by omega

/-- The subtree of `v` is full in table `A`. -/
def subtreeFull (n : ℕ) (A : Arr K) (v : Node) : Bool := (subtreeNodes v).all (nodeFull n A)

/-- The number of occupied slots of tree `T_i`. -/
def occupiedIn (n : ℕ) (A : Arr K) (i : ℕ) : ℕ :=
  ((List.range (treeSize n i)).filter fun a => (A (treeOffset n i + a)).isSome).length

/-- The node holding `x` in table `A`, if any. -/
def nodeOf (n : ℕ) (A : Arr K) (x : K) : Option Node :=
  (allNodes n).find? fun v => decide (x ∈ nodeElems n A v)

/-! ## Table 1 and the query's waiting rule (§4) -/

/-- `K_i(x)` (Table 1): `K + 1` for the largest level `K` of tree `i` such that the level-`j`
ancestor of `L_i(x)` has bit `1` for `j = K` and for every `j ∈ [J_i(x), K]`; `1` if there is
none. -/
noncomputable def Kof (n : ℕ) (A : Arr K) (ω : Outcome K n) (x : K) (i : ℕ) : ℕ :=
  let h := height n i
  let ℓ := leafOf ω x i
  let J := Jof (prio ω x i)
  let good : ℕ → Bool := fun Kl =>
    nodeBit n A (ancestor i ℓ Kl) &&
      (List.range (Kl + 1)).all fun j =>
        if 1 ≤ j ∧ J ≤ (j : ℕ∞) then nodeBit n A (ancestor i ℓ j) else true
  match ((List.range h).map (h - ·)).find? good with
  | some Kl => Kl + 1
  | none => 1

/-- The root of `S_i(x)`, the level-`K_i(x)` home subtree of `x` in `T_i` (the whole tree if
`K_i(x)` exceeds its height). -/
noncomputable def Sroot (n : ℕ) (A : Arr K) (ω : Outcome K n) (x : K) (i : ℕ) : Node :=
  ancestor i (leafOf ω x i) (min (Kof n A ω x i) (height n i))

/-- `C(L)`: the largest `J₁` of an element of leaf `L`, or `1` if `L` is empty. -/
noncomputable def Cleaf (n : ℕ) (A : Arr K) (ω : Outcome K n) (L : Node) : ℕ∞ :=
  match nodeElems n A L with
  | [] => 1
  | es => es.foldr (fun y m => max (Jof (prio ω y 1)) m) 0

/-- `I(x) = 100 · max {K₁(x), C(L)}` over the leaves `L` of `T₁` the query waits for (`L₁(x)` and
the leaves of `S₁(x)`). -/
noncomputable def Iof (n : ℕ) (A : Arr K) (ω : Outcome K n) (x : K) : ℕ∞ :=
  let leaves := (subtreeNodes (Sroot n A ω x 1)).filter (fun v => v.level = 1)
  100 * max (Kof n A ω x 1 : ℕ∞)
    ((ancestor 1 (leafOf ω x 1) 1 :: leaves).foldr (fun L m => max (Cleaf n A ω L) m) 0)

/-- The query for `x`, with `I` standing for `I(x)`, waits for node `v`: `v` lies in a tree `T_i`
with `i ≤ min {I, α}`, and `v` is an ancestor of `L_i(x)` at a level at most `J_i(x)`
(at most `max {J₁(x), I}` if `i = 1`), or `v` lies in `S_i(x)`. -/
def Waits (n : ℕ) (A : Arr K) (ω : Outcome K n) (x : K) (I : ℕ∞) (v : Node) : Prop :=
  let i := v.tree
  let J := Jof (prio ω x i)
  v.Valid n ∧ (i : ℕ∞) ≤ I ∧
    ((v = ancestor i (leafOf ω x i) v.level ∧ (v.level : ℕ∞) ≤ (if i = 1 then max J I else J)) ∨
      InSubtree v (Sroot n A ω x i))

/-- `x` is safe in table `A` (with `I` standing for `I(x)`): every node holding `x` is one the
query for `x` waits for. -/
def Safe (n : ℕ) (A : Arr K) (ω : Outcome K n) (x : K) (I : ℕ∞) : Prop :=
  ∀ v ∈ allNodes n, x ∈ nodeElems n A v → Waits n A ω x I v

/-! ## Expensive nodes (§4.2); runs of the §4 algorithm -/

/-- Node `V` is expensive after the first `t` insertions of `xs` (by the §4 algorithm): before
then, (1) a current-array insertion ran `TryInsertSubtree` with target `V`; (2) a cleanup attempt
in a nonfinal phase had target `V` and inserted its element below `V`; (3) `V` is the root of its
tree and a final-phase cleanup attempt succeeded in that tree; or (4) `V` is in `T₁` and step 3
of an insertion in an epoch `s > 100` selected `V`. -/
def ExpensiveAt (n : ℕ) (η : ℝ) (ω : Outcome K n) (xs : List K) (V : Node) (t : ℕ) : Prop :=
  ∃ r ∈ (recs .sec4 n η ω xs).take t,
    V ∈ r.s2.caTargets ∨
    (1 ≤ r.phase ∧ r.phase ≤ height n (r.epoch - 1) ∧ r.s2.cleanupTarget = some V ∧
      r.s2.cleanupOK = true ∧ ∃ U, r.s2.placed = some U ∧ U.level < V.level) ∨
    (V.level = height n V.tree ∧ 2 ≤ r.epoch ∧ r.phase = height n (r.epoch - 1) + 1 ∧
      r.s2.cleanupOK = true ∧ V.tree = r.epoch - 1) ∨
    (V.tree = 1 ∧ r.step3Node = some V)

end IncrOpenAddr.NoTradeoff


