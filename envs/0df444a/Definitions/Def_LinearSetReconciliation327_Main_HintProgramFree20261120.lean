-- Prove2me | Definitions.Def_LinearSetReconciliation327_Main_HintProgramFree20261120
-- name    : LinearSetReconciliation327_Main_HintProgramFree20261120
-- status  : Definition
-- author  : @djwj233
-- created : 2026-11-22T09:08:14.592122+00:00
-- url     : https://prove2.me/theorems/8e389389-44a5-4a1c-bdc3-095386a9d436
-- title:
--   LinearSetReconciliation327 — HintProgramFree (2026-11-20)
-- statement:
--   Internal dependency module `Definitions.LinearSetReconciliation327_Main_HintProgramFree20261120` of the LinearSetReconciliation327 development that formalizes Theorem 5.1 (Performance of HintSketch). It factors the toggle-program / decoder construction into a small node so that every node compiles well inside the platform's compilation limit; it contains only the definitions, structures, lemmas and proofs belonging to this module, and it is sorry-free. This definition is a supporting node, not a statement of independent mathematical interest.
-- source:
--   Tianren Liu, Rui Xu, Tong Yang, Kangyang Zhou, STOC 2027 submission #327 (October 2026), Theorem 5.1 (HintSketch), PDF p.19 (printed p.18)

import Definitions.Def_LinearSetReconciliation327_Main_HintUpdateRoot20261120
import Mathlib
import Definitions.Def_LinearSetReconciliation327_Main_Basic
import Definitions.Def_LinearSetReconciliation327_Main_WordRAM
import Definitions.Def_LinearSetReconciliation327_Main_Framework
import Definitions.Def_LinearSetReconciliation327_Main_HintSketch
import Definitions.Def_LinearSetReconciliation327_Main_HintUpstream5920261120
import Definitions.Def_LinearSetReconciliation327_Main_HintUpstream51020261120
import Definitions.Def_LinearSetReconciliation327_Main_HintUpstream5420261120
import Definitions.Def_LinearSetReconciliation327_Main_HintUpstream5620261120

open scoped ENNReal
open Finset

set_option autoImplicit false

noncomputable section

namespace LinearSetReconciliation327.Main.HintProgramFree

/-! # Theorem 5.1 (`HintSketch`), program-free part: construction and roadmap

This file fixes the concrete objects of Theorem 5.1 for a given node `(n, lam, N, X, Y)` and
isolates the five *program-free* conjuncts:

1. `WidthOK W n cW (lg n)`
2. `spec.Fits W`
3. `wordsOf W M ≤ 2 ^ W`
4. `(M : ℝ) ≤ (1 + C₁/lg n) * ((X:ℝ) + α * hN N Y) + C₂ * (N/lg n^8) + C₃ * lam * lg n^p₁`
5. `∀ r, ColumnWeightLE (H r) (Cu * lg n ^ pu)`

The machine conjuncts (`TogglesWithin`, `HaltsWithin`, the failure-probability bound) are owned by
another agent and are only marked `-- TODO(machine)` here (see the end of the file).

## Design (see `Solutions/_NOTES_5_1.md` for the full rationale)

* `A = 100`, `C = 40`: the thresholds of `tree_exists_root` / `LinearSetReconciliation327.Main.HintUpstream510.lemma_5_10`, so that the recursion
  tree `T` of §5 exists and satisfies `depth ≤ K(lg lg n + 1)`, `nodeCount ≤ K·A·lg²⁷ n`.
* `W = 1024·(⌈log₂(n+2)⌉ + 1)`, `cW = 4096`: a concrete `Θ(log n)` width with enormous slack, so
  that *every* table size (`N_v`, `m_v·ℓ_v·N_max,v`) fits in a word with room to spare.
* `spec` records, per node `v` of the recursion tree with a row scheme (in preorder), its universe
  `N_v` (one public permutation) and one coefficient table of shape `(m_v·ℓ_v·N_max,v, 2)` holding
  the node's row coins `β_{j,s}` (there are `m_v` rows, each with `ℓ_v` columns and `N_max,v`
  coefficients per column).
* `M = synLen CR T`, the total number of stored bits of the tree: at a `store` node `N` bits, at a CR
  node `CR.rows N t` bits, at a `direct` node `m·ℓ + CR.rows N t`, at a `recursive` node the sum of
  its children's sizes plus its own residual `CR` sketch.  `bitVal` is the value of the bit at a
  given flat index, defined by the same recursion with `Fin.append` / `finSigmaFinEquiv` /
  `finProdFinEquiv`; the flattening order is therefore the tree's preorder with, at each node, the
  stored columns before the residual `CR` sketch.  `H r` is the linear map `x ↦` those bits at the
  support of `x`; it is the flattening of `Node.sketch CR T r` (the identification is
  `bitVal = bit of Node.sketch`, still to be written down).
-/

/-! ## 1. Absolute constants (chosen before `n, lam, N, X, Y`, as Theorem 5.1 requires) -/

/-- `A`, the first absolute constant of §5.2. -/
def hintA : ℕ := 100

/-- `C`, the second absolute constant of §5.2 (`C ≥ A`). -/
def hintC : ℕ := 40

/-- `W = 1024(⌈K⌉₊ + 2)(⌈log₂(n+2)⌉ + 1)`, a concrete `Θ(log n)`.  The multiplier `⌈K⌉₊ + 2` is
what makes it dominate the *hidden* constant `K` of Lemmas 5.9/5.10 as in the paper: as in the paper,
`W = Θ(log n)`, but concretely `2^W ≥ (n+2)^(1024(⌈K⌉₊+2))` — astronomically more than any `log^{O(1)} n`
or polynomial factor the length analysis produces. -/
def hintW (K : ℝ) (n : ℕ) : ℕ := 1024 * (⌈K⌉₊ + 2) * (Nat.clog 2 (n + 2) + 1)

/-- The constant `cW` of `WidthOK W n cW (lg n)`.  Since
`W ≤ 1024(K + 3)(lg n + 2) ≤ 16384(K+2) lg n` for `n ≥ 2`, `K ≥ 0`, this is admissible. -/
def hintcW (K : ℝ) : ℝ := 16384 * (K + 2)

/-- `α`, the constant of the outside-cost term.  It has to dominate both `C²` (the charge
conservation of Lemma 5.9) and the cross term `K·C` produced by Lemma 5.9's first conclusion, so
`α = (K+C)²` — the paper's `α = C²` after absorbing the hidden `K` into `C`. -/
def hintAlpha (K : ℝ) : ℝ := (K + (hintC : ℝ)) ^ 2

/-- `C₁`, the constant of the relative overhead `1 + C₁/log n`.  It must dominate the constant of the
direct leaf's relative overhead `C·X/log n` (equation `eq:hint-direct-storage`), where `C` is the
`C` of `HintParams`; with the paper's `C = 40` and `C₁ = 4096` it does, with a factor-100 margin.  (The
previous value `16` was *smaller* than `40`, so the bound was false; see `TODO(5.9)` for the
counterexample, which also shows that `C` must be quantified as `C ≤ hintC` in the statement.) -/
def hintC₁ : ℝ := 4096

/-- `C₂`, the constant of the additive `N/log⁸ n` term (it must dominate `4K`, the number of residual
rows of a cheap node). -/
def hintC₂ (K : ℝ) : ℝ := 64 * (K + 1)

/-- `C₃`, the constant of the `λ log^{p₁} n` term. -/
def hintC₃ (K : ℝ) : ℝ := (2 : ℝ) ^ 30 * (K + 1) ^ 8

/-- `p₁`, the exponent of the `λ log^{p₁} n` term.  It must exceed `8 + 2A = 208`: a `small` node's
residual rows carry a factor `η^{-2} = log^{2A} n`. -/
def hintp₁ : ℕ := 1024

/-- `Cu`, the constant of the column-locality bound. -/
def hintCu (K : ℝ) : ℝ := (2 : ℝ) ^ 30 * (K + 1) ^ 4

/-- `pu`, the exponent of the column-locality bound. -/
def hintpu : ℕ := 1024

/-! ## 3. The public table specification `spec` -/

/-- The nodes of the tree that own a row scheme (`direct` and `recursive` nodes), in preorder.
`store` and `cr` leaves have no tables of their own. -/
def schemeNodes : Node → List Node
  | .store _ => []
  | .cr _ _ => []
  | .direct sch t => [.direct sch t]
  | .recursive sch t Xs Ys child =>
      [.recursive sch t Xs Ys child] ++
        (List.ofFn fun s : Fin sch.ℓ => schemeNodes (child s)).flatten

/-- Number of columns `ℓ_v` of a node. -/
def nodeEll : Node → ℕ
  | .direct sch _ => sch.ℓ
  | .recursive sch _ _ _ _ => sch.ℓ
  | _ => 0

/-- Number of rows `m_v` of a node. -/
def nodeM : Node → ℕ
  | .direct sch _ => sch.m
  | .recursive sch _ _ _ _ => sch.m
  | _ => 0

/-- `N_max,v = ⌈N_v/m_v⌉`, the number of coefficients per column and row.  For a node of the
`HintSketch` recursion this is exactly `HintParams.Nmax N_v X_v Y_v`, because `m_v = rows X_v Y_v`. -/
def nodeNmax (v : Node) : ℕ := ⌈(v.N : ℝ) / (nodeM v : ℝ)⌉₊

/-- The shape of the coefficient table of a node: the row coins are
`β : Fin m_v → Fin ℓ_v → Fin N_max,v → ZMod 2`, i.e. `m_v·ℓ_v·N_max,v` uniform bits. -/
def nodeCoins (v : Node) : ℕ × ℕ := (nodeM v * nodeEll v * nodeNmax v, 2)

/-- The universe of each node that owns a row scheme, in preorder: one public permutation per node. -/
def permSizesOf (T : Node) : List ℕ := (schemeNodes T).map Node.N

/-- The coefficient tables of the tree, one per node that owns a row scheme, in the same order. -/
def coeffShapesOf (T : Node) : List (ℕ × ℕ) := (schemeNodes T).map nodeCoins

/-- The public table specification of the whole tree. -/
def hintSpec (T : Node) : TableSpec where
  permSizes := permSizesOf T
  coeffShapes := coeffShapesOf T
  coeff_pos := by
    intro p hp
    obtain ⟨v, _, rfl⟩ := List.mem_map.mp hp
    show 0 < (nodeCoins v).2
    simp [nodeCoins]

/-! ### Elementary facts about the width -/

/-- Unfolding `2 ^ W`. -/
lemma two_pow_hintW (K : ℝ) (n : ℕ) :
    2 ^ hintW K n = (2 * 2 ^ Nat.clog 2 (n + 2)) ^ (1024 * (⌈K⌉₊ + 2)) := by
  have hbase : 2 ^ (Nat.clog 2 (n + 2) + 1) = 2 * 2 ^ Nat.clog 2 (n + 2) := by
    rw [Nat.pow_succ, Nat.mul_comm]
  rw [hintW, Nat.mul_comm (1024 * (⌈K⌉₊ + 2)) (Nat.clog 2 (n + 2) + 1), Nat.pow_mul, hbase]

/-- Every table size used below is far smaller than a word: `n ≤ 2 ^ W`. -/
lemma n_le_two_pow_hintW (K : ℝ) (n : ℕ) : n ≤ 2 ^ hintW K n := by
  rw [two_pow_hintW]
  have h1 : n + 2 ≤ 2 ^ Nat.clog 2 (n + 2) := Nat.le_pow_clog (by norm_num) (n + 2)
  have h2 : n + 2 ≤ 2 * 2 ^ Nat.clog 2 (n + 2) := by omega
  have hm : 1 ≤ 1024 * (⌈K⌉₊ + 2) := Nat.mul_pos (by norm_num) (by omega)
  calc n ≤ n + 2 := by omega
    _ ≤ 2 * 2 ^ Nat.clog 2 (n + 2) := h2
    _ ≤ (2 * 2 ^ Nat.clog 2 (n + 2)) ^ (1024 * (⌈K⌉₊ + 2)) := by
        refine le_trans (le_of_eq (Nat.pow_one _).symm) ?_
        exact Nat.pow_le_pow_right (by omega) hm

/-! ## 3b. Conjunct 1: the width is `Θ(log n)`

The paper's `W = Θ(log n)`: the loop bound `clog 2 n ≤ W` and the `cW·lg n` upper bound both come
from `clog 2 m ≤ lg m + 1`, i.e. from `2^{clog 2 m - 1} < m`. -/

/-- `⌈log₂ m⌉ ≤ log₂ m + 1` for `m ≥ 2` (`Nat.pow_pred_clog_lt_self` + monotonicity of `logb`). -/
lemma clog_two_le_lg_add_one {m : ℕ} (hm : 2 ≤ m) :
    (Nat.clog 2 m : ℝ) ≤ lg (m : ℝ) + 1 := by
  have hb : 1 < 2 := by norm_num
  have hk : 0 < Nat.clog 2 m := Nat.clog_pos hb (by omega)
  have h1 : 2 ^ (Nat.clog 2 m).pred < m := Nat.pow_pred_clog_lt_self hb (by omega)
  have hcast : ((2 ^ (Nat.clog 2 m).pred : ℕ) : ℝ) = (2 : ℝ) ^ (Nat.clog 2 m).pred := by
    push_cast
    ring
  have h2 : (2 : ℝ) ^ (Nat.clog 2 m).pred < (m : ℝ) := by
    rw [← hcast]
    exact_mod_cast h1
  have h3 : lg ((2 : ℝ) ^ (Nat.clog 2 m).pred) < lg (m : ℝ) :=
    Real.logb_lt_logb (by norm_num) (by positivity) h2
  have h3' : ((Nat.clog 2 m).pred : ℝ) < lg (m : ℝ) := by
    have h := h3
    rw [lg, Real.logb_pow, Real.logb_self_eq_one (by norm_num), mul_one] at h
    exact h
  have h4 : ((Nat.clog 2 m).pred : ℝ) = (Nat.clog 2 m : ℝ) - 1 := by
    rw [Nat.pred_eq_sub_one, Nat.cast_sub hk, Nat.cast_one]
  rw [h4] at h3'
  linarith

/-- `ln`/`lg` of a natural at least `2` is at least `1`. -/
lemma one_le_lg {n : ℕ} (hn : 2 ≤ n) : 1 ≤ lg (n : ℝ) := by
  have h := Real.logb_le_logb_of_le (b := 2) (by norm_num) (by norm_num : (0 : ℝ) < 2)
    (by exact_mod_cast hn : (2 : ℝ) ≤ (n : ℝ))
  have h2 : Real.logb 2 (2 : ℝ) = 1 := Real.logb_self_eq_one (by norm_num)
  rw [h2] at h
  exact h

/-- The cast of `hintW`. -/
lemma hintW_cast (K : ℝ) (n : ℕ) :
    (hintW K n : ℝ) = 1024 * ((⌈K⌉₊ : ℝ) + 2) * ((Nat.clog 2 (n + 2) : ℝ) + 1) := by
  rw [hintW]
  push_cast
  ring

/-- `lg (n+2) ≤ lg n + 1` for `n ≥ 2`. -/
lemma lg_add_two_le {n : ℕ} (hn : 2 ≤ n) : lg ((n : ℝ) + 2) ≤ lg (n : ℝ) + 1 := by
  have hmono : lg ((n : ℝ) + 2) ≤ lg (2 * (n : ℝ)) := by
    refine Real.logb_le_logb_of_le (b := 2) (by norm_num) (by positivity) ?_
    have hn' : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
    linarith
  have hmul : lg (2 * (n : ℝ)) = lg (n : ℝ) + 1 := by
    have h : Real.logb 2 (2 * (n : ℝ)) = Real.logb 2 (2 : ℝ) + Real.logb 2 (n : ℝ) :=
      Real.logb_mul (by norm_num) (by positivity)
    rw [Real.logb_self_eq_one (by norm_num)] at h
    simp only [lg]
    linarith
  linarith

/-- `W ≤ cW·lg n`: the width is `Θ(log n)` with the explicit constant `16384(K+2)`. -/
lemma hintW_le_lgn {K : ℝ} (hK : 0 ≤ K) {n : ℕ} (hn : 2 ≤ n) :
    (hintW K n : ℝ) ≤ hintcW K * lg (n : ℝ) := by
  have hc : (Nat.clog 2 (n + 2) : ℝ) ≤ lg ((n : ℝ) + 2) + 1 := by
    have h := clog_two_le_lg_add_one (m := n + 2) (by omega)
    have hcast : ((n + 2 : ℕ) : ℝ) = (n : ℝ) + 2 := by push_cast; ring
    rwa [hcast] at h
  have h1 := one_le_lg hn
  have h2 := lg_add_two_le hn
  have hK3 : ((⌈K⌉₊ : ℝ) + 2) ≤ 3 * (K + 2) := by
    have hle : (⌈K⌉₊ : ℝ) ≤ K + 1 := by
      have hlt := Nat.ceil_lt_add_one hK
      linarith
    linarith
  have hclog : ((Nat.clog 2 (n + 2) : ℝ) + 1) ≤ 4 * lg (n : ℝ) := by linarith
  have h3 : (0 : ℝ) ≤ 3 * (K + 2) := by linarith
  have h5 : (0 : ℝ) ≤ (Nat.clog 2 (n + 2) : ℝ) + 1 := by positivity
  have hstep : ((⌈K⌉₊ : ℝ) + 2) * ((Nat.clog 2 (n + 2) : ℝ) + 1) ≤
      (3 * (K + 2)) * (4 * lg (n : ℝ)) := mul_le_mul hK3 hclog h5 h3
  have hstep2 : 1024 * (((⌈K⌉₊ : ℝ) + 2) * ((Nat.clog 2 (n + 2) : ℝ) + 1)) ≤
      1024 * ((3 * (K + 2)) * (4 * lg (n : ℝ))) :=
    mul_le_mul_of_nonneg_left hstep (by norm_num)
  have hKl : (0 : ℝ) ≤ (K + 2) * lg (n : ℝ) :=
    mul_nonneg (by linarith) (by linarith)
  have hfin : 1024 * ((3 * (K + 2)) * (4 * lg (n : ℝ))) ≤ 16384 * (K + 2) * lg (n : ℝ) := by
    have h := mul_le_mul_of_nonneg_right (show (1024 : ℝ) * (3 * 4) ≤ 16384 by norm_num) hKl
    nlinarith [h]
  rw [hintW_cast, hintcW]
  calc 1024 * ((⌈K⌉₊ : ℝ) + 2) * ((Nat.clog 2 (n + 2) : ℝ) + 1)
      = 1024 * (((⌈K⌉₊ : ℝ) + 2) * ((Nat.clog 2 (n + 2) : ℝ) + 1)) := by ring
    _ ≤ 1024 * ((3 * (K + 2)) * (4 * lg (n : ℝ))) := hstep2
    _ ≤ 16384 * (K + 2) * lg (n : ℝ) := hfin

/-! ## 3c. Conjunct 4's constants, extracted from the witnesses of Lemmas 5.9 / 5.10

`HintLengthOK` has to be instantiated at *some* `A, C`.  Lemmas 5.9/5.10 only hold for `A ≥ A₀`,
`C ≥ C₀`, and `A₀, C₀` are opaque existential witnesses, so neither `A = 100, C = 40` (what
`hintFits_tree`/`hintWords_tree` use) nor any other explicit pair can be *proved* admissible
(`A₀ ≤ 100` is not derivable from the statement of Lemma 5.9).  Following Lemma 5.9's own internal
choice we do not fight the witnesses but *use* them:

    A := max (max A₀⁵⁹ A₀¹⁰) 100,        C := max (max C₀⁵⁹ C₀¹⁰) 40.

Then `A ≥ A₀` and `C ≥ C₀` are `le_max` arithmetic instead of an unprovable numeric bound.  Every
constant below depends only on `KCR` — never on `n, lam, N, X, Y` — so Theorem 5.1's requirement
that all constants precede the node is met.

Two constants must *grow* with the witnesses, which is why `A` and `C` cannot remain universally
quantified above the witnesses (the `∃A₀, ∀A ≥ A₀, ∃C₀, ∀C ≥ C₀` form of `TODO(5.9)` is not
provable with a fixed `p₁`/`C₁`):

* `p₁` must exceed `9 + 2A`: a `small` node's residual carries `η^{-2} = log^{2A}n`;
* `C₁` must exceed `C` (a `direct` leaf's relative overhead is `C·X/log n`, FIX 1) and `~A`.
-/

/-- Lemma 5.10's hidden constant. -/
noncomputable def hintLenK₁₀ : ℝ := Classical.choose LinearSetReconciliation327.Main.HintUpstream510.lemma_5_10

/-- Lemma 5.10's `A₀`. -/
noncomputable def hintLenA₀₁₀ : ℕ := Classical.choose (Classical.choose_spec LinearSetReconciliation327.Main.HintUpstream510.lemma_5_10).2

/-- Lemma 5.9's hidden constant (it depends on `KCR`). -/
noncomputable def hintLenK₅₉ (KCR : ℝ) : ℝ := Classical.choose (LinearSetReconciliation327.Main.HintUpstream59.lemma_5_9 KCR)

/-- Lemma 5.9's `A₀`. -/
noncomputable def hintLenA₀₅₉ (KCR : ℝ) : ℕ :=
  Classical.choose (Classical.choose_spec (LinearSetReconciliation327.Main.HintUpstream59.lemma_5_9 KCR)).2

/-- Lemma 5.4's `A₀` (it does not depend on `KCR`). -/
noncomputable def hintLenA₀₅₄ : ℕ := Classical.choose LinearSetReconciliation327.Main.HintUpstream54.lemma_5_4

/-- Lemma 5.6's `A₀` (it does not depend on `KCR`). -/
noncomputable def hintLenA₀₅₆ : ℕ := Classical.choose LinearSetReconciliation327.Main.HintUpstream56.lemma_5_6

/-- `A = max (max (max (max A₀⁵⁹ A₀¹⁰) A₀⁵⁴) A₀⁵⁶) 100`: the first absolute constant of §5.2,
admissible for Lemmas 5.4, 5.6, 5.9 and 5.10 alike.  Adding `A₀⁵⁴` and `A₀⁵⁶` is a *constant
choice*, not a statement change: `hintLenA` only ever appears inside `∃`-quantified constants, and
Lemma 5.4/5.6 are instantiated below at `(hintLenA KCR, hintLenC KCR)`, which needs exactly these
two inequalities. -/
noncomputable def hintLenA (KCR : ℝ) : ℕ :=
  max (max (max (max (hintLenA₀₅₉ KCR) (hintLenA₀₁₀)) (hintLenA₀₅₄)) (hintLenA₀₅₆)) 100

theorem le_hintLenA₅₉ (KCR : ℝ) : hintLenA₀₅₉ KCR ≤ hintLenA KCR := by
  unfold hintLenA; omega

theorem le_hintLenA₁₀ (KCR : ℝ) : hintLenA₀₁₀ ≤ hintLenA KCR := by
  unfold hintLenA; omega

theorem le_hintLenA₅₄ (KCR : ℝ) : hintLenA₀₅₄ ≤ hintLenA KCR := by
  unfold hintLenA; omega

theorem le_hintLenA₅₆ (KCR : ℝ) : hintLenA₀₅₆ ≤ hintLenA KCR := by
  unfold hintLenA; omega

/-- Lemma 5.9's `C₀` at `A = hintLenA KCR`. -/
noncomputable def hintLenC₀₅₉ (KCR : ℝ) : ℕ :=
  Classical.choose (Classical.choose_spec (Classical.choose_spec (LinearSetReconciliation327.Main.HintUpstream59.lemma_5_9 KCR)).2
    (hintLenA KCR) (le_hintLenA₅₉ KCR))

/-- Lemma 5.10's `C₀` at `A = hintLenA KCR`. -/
noncomputable def hintLenC₀₁₀ (KCR : ℝ) : ℕ :=
  Classical.choose (Classical.choose_spec (Classical.choose_spec LinearSetReconciliation327.Main.HintUpstream510.lemma_5_10).2
    (hintLenA KCR) (le_hintLenA₁₀ KCR))

/-- Lemma 5.4's `C₀` at `A = hintLenA KCR`. -/
noncomputable def hintLenC₀₅₄ (KCR : ℝ) : ℕ :=
  Classical.choose (Classical.choose_spec LinearSetReconciliation327.Main.HintUpstream54.lemma_5_4 (hintLenA KCR) (le_hintLenA₅₄ KCR))

/-- Lemma 5.6's `C₀` at `A = hintLenA KCR`. -/
noncomputable def hintLenC₀₅₆ (KCR : ℝ) : ℕ :=
  Classical.choose (Classical.choose_spec LinearSetReconciliation327.Main.HintUpstream56.lemma_5_6 (hintLenA KCR) (le_hintLenA₅₆ KCR))

/-- `8 · ⌈log₂ (K₁₀ + 1)⌉` (with slack): the part of `C` that dominates Lemma 5.10's hidden
constant `K = hintLenK₁₀`.  The factor `8` leaves room for the `C³ ≤ 2^{C/8}` step of the numeric
bound `boundCount · 2^{-λ_*} ≤ 2^{-λ}`: `K₁₀ ≤ 2^{C/8}` and `C³ ≤ 2^{C/8}` then give
`2(E+1)·K₁₀·A ≤ 2^C`. -/
noncomputable def hintLenK₁₀bits (KCR : ℝ) : ℕ :=
  8 * Nat.clog 2 (⌈hintLenK₁₀⌉₊ + 2)

/-- `C = max (max (max (max (max C₀⁵⁹ C₀¹⁰) C₀⁵⁴) C₀⁵⁶) (48(A+42))) (8⌈log₂(K₁₀+1)⌉)) 40`: the
second absolute constant of §5.2, admissible for Lemmas 5.4, 5.6, 5.9 and 5.10, and large enough
to absorb Lemma 5.10's hidden node-count constant.  The two extra terms (`48(A+42)` and
`hintLenK₁₀bits`) are *constant choices*: they make `4(E+2) ≤ 2^{C-2}` and
`2(E+1)·K₁₀·A ≤ 2^C` true by `le_max` arithmetic instead of leaving them as unprovable numeric
side conditions. -/
noncomputable def hintLenC (KCR : ℝ) : ℕ :=
  max (max (max (hintLenC₀₅₉ KCR) (hintLenC₀₁₀ KCR)) (max (hintLenC₀₅₄ KCR) (hintLenC₀₅₆ KCR)))
    (max (48 * (hintLenA KCR + 40 + 2)) (hintLenK₁₀bits KCR + 3 * hintLenA KCR + 40))

theorem le_hintLenC₅₉ (KCR : ℝ) : hintLenC₀₅₉ KCR ≤ hintLenC KCR := by
  unfold hintLenC; omega

theorem le_hintLenC₁₀ (KCR : ℝ) : hintLenC₀₁₀ KCR ≤ hintLenC KCR := by
  unfold hintLenC; omega

theorem le_hintLenC₅₄ (KCR : ℝ) : hintLenC₀₅₄ KCR ≤ hintLenC KCR := by
  unfold hintLenC; omega

theorem le_hintLenC₅₆ (KCR : ℝ) : hintLenC₀₅₆ KCR ≤ hintLenC KCR := by
  unfold hintLenC; omega

theorem le_hintLenK₁₀bits (KCR : ℝ) : hintLenK₁₀bits KCR ≤ hintLenC KCR := by
  unfold hintLenC; omega

/-- The `48(A+42)` term is definitionally in the maximum: this is the `hfix` that discharges `hE`. -/
theorem hfix_le_hintLenC (KCR : ℝ) : 48 * (hintLenA KCR + 40 + 2) ≤ hintLenC KCR := by
  unfold hintLenC; omega

/-- `C ≥ 40`, which is what makes the charge constant `α = (K+C)²` at least `1600`. -/
theorem forty_le_hintLenC (KCR : ℝ) : 40 ≤ hintLenC KCR := by
  unfold hintLenC; omega

/-- The four conclusions of Lemma 5.9, at `A = hintLenA KCR`, `C = hintLenC KCR`. -/
def Hint509 (K KCR : ℝ) (n lam N X Y : ℕ) (CR : CRFamily) : Prop :=
  let P : HintParams := ⟨hintLenA KCR, hintLenC KCR, n, lam⟩
  let I := range (P.ell N X Y)
  let Xs := P.capX N X Y
  let Ys := P.capY N X Y
  (∑ s ∈ I, (Xs s : ℝ) ≤ (X : ℝ) + K * ((hintLenC KCR : ℝ) * hN N Y)) ∧
    (∑ s ∈ I, hN Y (Ys s) ≤ hN N Y / 4) ∧
    (∑ s ∈ I, ((Ys s : ℝ) / (Y : ℝ)) ≤ ((Y : ℝ) / (N : ℝ)) / 4) ∧
    (∑ s ∈ I.filter (fun s => P.rule Y (Xs s) (Ys s) = .recursive),
          ((Xs s : ℝ) + (hintLenC KCR : ℝ) ^ 2 * hN Y (Ys s)) +
        ∑ s ∈ I.filter (fun s => P.rule Y (Xs s) (Ys s) = .direct), (Xs s : ℝ) +
        ∑ s ∈ I.filter (fun s => P.rule Y (Xs s) (Ys s) = .cheap),
          (CR.rows Y (HintParams.D Y (Xs s) (Ys s)) : ℝ) ≤
      (X : ℝ) + (hintLenC KCR : ℝ) ^ 2 * hN N Y)

/-- **Lemma 5.9 at the extracted witnesses.** -/
theorem lemma_5_9_at (KCR : ℝ) {n lam N X Y : ℕ} {CR : CRFamily}
    (hrows : ∀ N' t : ℕ, t ≤ N' → (CR.rows N' t : ℝ) ≤ KCR * ((t : ℝ) * lg ((N' : ℝ) + 2) ^ 2))
    (hargs : (⟨hintLenA KCR, hintLenC KCR, n, lam⟩ : HintParams).NodeArgs N X Y)
    (hrec : (⟨hintLenA KCR, hintLenC KCR, n, lam⟩ : HintParams).rule N X Y = .recursive) :
    Hint509 (hintLenK₅₉ KCR) KCR n lam N X Y CR :=
  Classical.choose_spec
    (Classical.choose_spec (Classical.choose_spec (LinearSetReconciliation327.Main.HintUpstream59.lemma_5_9 KCR)).2
      (hintLenA KCR) (le_hintLenA₅₉ KCR))
    (hintLenC KCR) (le_hintLenC₅₉ KCR) n lam N X Y CR hrows hargs hrec

/-- **Lemma 5.10 at the extracted witnesses.** -/
theorem lemma_5_10_at (KCR : ℝ) :
    ∀ (n lam N X Y : ℕ),
      (⟨hintLenA KCR, hintLenC KCR, n, lam⟩ : HintParams).NodeArgs N X Y →
      ∃ (fuel : ℕ) (T : Node), (⟨hintLenA KCR, hintLenC KCR, n, lam⟩ : HintParams).tree fuel N X Y
          = some T ∧
        (fuel : ℝ) ≤ hintLenK₁₀ * (lg (lg n) + 1) ∧
        (T.depth : ℝ) ≤ hintLenK₁₀ * (lg (lg n) + 1) ∧
        (T.recursiveCount : ℝ) ≤ hintLenK₁₀ * lg n ^ 13 ∧
        (T.nodeCount : ℝ) ≤ hintLenK₁₀ * (hintLenA KCR : ℝ) * lg n ^ 27 :=
  Classical.choose_spec
    (Classical.choose_spec (Classical.choose_spec LinearSetReconciliation327.Main.HintUpstream510.lemma_5_10).2
      (hintLenA KCR) (le_hintLenA₁₀ KCR))
    (hintLenC KCR) (le_hintLenC₁₀ KCR)

/-- **Lemma 5.4 (Remaining errors) at the extracted witnesses.**  `P.NodeArgs N X Y → P.NonLeaf N
X Y` gives both conclusions; the probability half is the `hZ` of `Node.BoundsProb`. -/
theorem lemma_5_4_at (KCR : ℝ) :
    ∀ (n lam N X Y : ℕ),
      let P : HintParams := ⟨hintLenA KCR, hintLenC KCR, n, lam⟩
      P.NodeArgs N X Y → P.NonLeaf N X Y →
      ∀ x J : Finset ℕ, Node.Valid N X Y x J →
        let sch := P.scheme N X Y
        expU (fun lr : sch.LocalSeed => (sch.Z lr x J : ℝ)) ≤
            P.eta * ((HintParams.D N X Y : ℝ) + 1) ∧
        prU (fun lr : sch.LocalSeed => P.resid N X Y < sch.Z lr x J) ≤
            ((2 : ℝ) ^ P.lamStar)⁻¹ :=
  Classical.choose_spec
    (Classical.choose_spec LinearSetReconciliation327.Main.HintUpstream54.lemma_5_4 (hintLenA KCR) (le_hintLenA₅₄ KCR))
    (hintLenC KCR) (le_hintLenC₅₄ KCR)

/-- **Lemma 5.6 (Sufficient child capacities) at the extracted witnesses.**  The two probability
conjuncts are the `hUV` of `Node.BoundsProb`. -/
theorem lemma_5_6_at (KCR : ℝ) :
    ∀ (n lam N X Y : ℕ),
      let P : HintParams := ⟨hintLenA KCR, hintLenC KCR, n, lam⟩
      P.NodeArgs N X Y → P.rule N X Y = .recursive →
      ∀ x J : Finset ℕ, Node.Valid N X Y x J →
        let sch := P.scheme N X Y
        ∀ s : Fin sch.ℓ,
          expU (fun lr : sch.LocalSeed => (sch.U lr x J s : ℝ)) ≤
            P.Q N X Y s.val + (HintParams.D N X Y : ℝ) * P.eta ^ 2 ∧
          expU (fun lr : sch.LocalSeed => (sch.V lr x J s : ℝ)) ≤
            ((2 : ℝ) ^ (P.c N X Y))⁻¹ * P.Q N X Y s.val + (HintParams.D N X Y : ℝ) * P.eta ^ 2 ∧
          prU (fun lr : sch.LocalSeed => P.capX N X Y s.val < sch.U lr x J s) ≤
            ((2 : ℝ) ^ P.lamStar)⁻¹ ∧
          prU (fun lr : sch.LocalSeed => P.capY N X Y s.val < sch.V lr x J s) ≤
            ((2 : ℝ) ^ P.lamStar)⁻¹ :=
  Classical.choose_spec
    (Classical.choose_spec LinearSetReconciliation327.Main.HintUpstream56.lemma_5_6 (hintLenA KCR) (le_hintLenA₅₆ KCR))
    (hintLenC KCR) (le_hintLenC₅₆ KCR)

/-- The `K` of conjunct 4: it dominates Lemma 5.9's, Lemma 5.10's and the given `KCR`. -/
noncomputable def hintLenK (KCR : ℝ) : ℝ := hintLenK₅₉ KCR + hintLenK₁₀ + max KCR 0 + 1

theorem hintLenK_pos (KCR : ℝ) : 0 < hintLenK KCR := by
  have h1 : 0 < hintLenK₅₉ KCR := (Classical.choose_spec (LinearSetReconciliation327.Main.HintUpstream59.lemma_5_9 KCR)).1
  have h2 : 0 < hintLenK₁₀ := (Classical.choose_spec LinearSetReconciliation327.Main.HintUpstream510.lemma_5_10).1
  have h3 : (0 : ℝ) ≤ max KCR 0 := le_max_right _ _
  unfold hintLenK
  linarith

theorem KCR_le_hintLenK (KCR : ℝ) : KCR ≤ hintLenK KCR := by
  have h3 : KCR ≤ max KCR 0 := le_max_left _ _
  have h4 : 0 < hintLenK₅₉ KCR + hintLenK₁₀ + 1 := by
    have h1 : 0 < hintLenK₅₉ KCR := (Classical.choose_spec (LinearSetReconciliation327.Main.HintUpstream59.lemma_5_9 KCR)).1
    have h2 : 0 < hintLenK₁₀ := (Classical.choose_spec LinearSetReconciliation327.Main.HintUpstream510.lemma_5_10).1
    linarith
  unfold hintLenK
  linarith

/-- `q = 8 + 2A + 16`: the exponent of the internal `λ log^q n · nodeCount` bucket.  It exceeds
`9 + 2A`, the exponent a `small` node's residual produces. -/
noncomputable def hintLenQ (KCR : ℝ) : ℕ := 8 + 2 * hintLenA KCR + 16

theorem hintLenQ_ge (KCR : ℝ) : 9 + 2 * hintLenA KCR ≤ hintLenQ KCR := by
  unfold hintLenQ; omega

theorem three_le_hintLenQ (KCR : ℝ) : 3 ≤ hintLenQ KCR := by
  unfold hintLenQ; omega

/-- `E = 48(A + C + 2)`: `ℓ_v ≤ log³n + E·log²n` at every node of the recursion. -/
noncomputable def hintLenE (KCR : ℝ) : ℕ := 48 * (hintLenA KCR + hintLenC KCR + 2)

/-- `m + 1 ≤ 2 ^ m` (the elementary exponential domination of a linear function). -/
theorem hintLen_succ_add_one_le_two_pow (m : ℕ) : m + 1 ≤ 2 ^ m := by
  induction m with
  | zero => norm_num
  | succ k ih =>
      rw [pow_succ]
      omega

/-- The numeric core of `four_hintLenE_add_two_le_pow`: `196C + 392 ≤ 2^(C-2)` for `C ≥ 40`.
From `C - 39 ≤ 2^(C-40)` and `2^(C-2) = 2^38 · 2^(C-40)`, with `2^38 = 274877906944`. -/
theorem hintLen_linear_le_pow (C : ℕ) (hC : 40 ≤ C) : 196 * C + 392 ≤ 2 ^ (C - 2) := by
  have hsplit : C - 2 = 38 + (C - 40) := by omega
  have hstep : C - 39 ≤ 2 ^ (C - 40) := by
    have h := hintLen_succ_add_one_le_two_pow (C - 40)
    omega
  have hlin : 196 * C + 392 ≤ 274877906944 * (C - 39) := by omega
  calc 196 * C + 392 ≤ 274877906944 * (C - 39) := hlin
    _ = 2 ^ 38 * (C - 39) := by
          rw [show (2 : ℕ) ^ 38 = 274877906944 by norm_num]
    _ ≤ 2 ^ 38 * 2 ^ (C - 40) := by gcongr
    _ = 2 ^ (38 + (C - 40)) := (pow_add 2 38 (C - 40)).symm
    _ = 2 ^ (C - 2) := by rw [hsplit]

/-- **The exponential domination of `E`.**  Since `C ≥ 48(A + 42)`, a fortiori `48A ≤ C`, hence
`E = 48(A + C + 2) ≤ 49C + 96` and `4(E + 2) ≤ 196C + 392 ≤ 2^(C-2)` by `hintLen_linear_le_pow`.
This is the arithmetic input that conjunct 8 needs. -/
theorem four_hintLenE_add_two_le_pow (KCR : ℝ) :
    4 * (hintLenE KCR + 2) ≤ 2 ^ (hintLenC KCR - 2) := by
  have hC : 48 * (hintLenA KCR + 40 + 2) ≤ hintLenC KCR := hfix_le_hintLenC KCR
  have h48 : 48 * hintLenA KCR ≤ hintLenC KCR := by omega
  have hE : hintLenE KCR ≤ 49 * hintLenC KCR + 96 := by
    unfold hintLenE
    omega
  have h1 : 4 * (hintLenE KCR + 2) ≤ 196 * hintLenC KCR + 392 := by omega
  exact le_trans h1 (hintLen_linear_le_pow _ (forty_le_hintLenC KCR))

/-- `α = (K+C)²`, the charge constant of the length invariant. -/
noncomputable def hintLenAlpha (KCR : ℝ) (K : ℝ) : ℝ := (K + (hintLenC KCR : ℝ)) ^ 2

/-- `C₂`: the constant of the additive `N/log⁸n` bucket. -/
noncomputable def hintLenC₂ (KCR : ℝ) (K : ℝ) : ℝ :=
  64 * (K + 1) * ((hintLenC KCR : ℝ) + 1) + 64 * max KCR 0 + 64

/-- `C₁`: the constant of the relative overhead `1 + C₁/(2 log n)` of the invariant.  It dominates
`2E` (the `direct` leaf, `ell_le_four`) and `2C₂(E+1)/α` (the `recursive` node's `∑_s N_s`
overflow) — the latter by construction, so no nonlinear side condition is left. -/
noncomputable def hintLenC₁ (KCR : ℝ) (K : ℝ) : ℝ :=
  (2 : ℝ) ^ 24 * (K + 1) * (((hintLenC KCR : ℝ) + 1) ^ 2) * ((hintLenE KCR : ℝ) + 1) +
    2 * hintLenC₂ KCR K * ((hintLenE KCR : ℝ) + 1) + 2 * ((hintLenE KCR : ℝ) + 1) + 2

/-- `C₃`: the constant of the `λ log^q n` bucket. -/
noncomputable def hintLenC₃ (KCR : ℝ) (K : ℝ) : ℝ :=
  (2 : ℝ) ^ 30 * (K + 1) ^ 8 * ((hintLenC KCR : ℝ) + 1) ^ 4 * ((hintLenA KCR : ℝ) + 1) +
    ((hintLenE KCR : ℝ) + 1) + 1

/-- `p₁ = q + 27`: the `nodeCount ≤ K·A·log²⁷n` factor is absorbed by `C₃'`. -/
noncomputable def hintLenP₁ (KCR : ℝ) : ℕ := hintLenQ KCR + 27

/-- The `λ`-constant of `HintLengthOK`; it absorbs the node count (`hintLenP₁`). -/
noncomputable def hintLenC₃' (KCR : ℝ) (K : ℝ) : ℝ :=
  hintLenC₃ KCR K * (⌈K⌉₊ + 1) * ((hintLenA KCR : ℝ) + 1)

theorem hintLenAlpha_pos (KCR : ℝ) {K : ℝ} (hK : 0 < K) : 0 < hintLenAlpha KCR K := by
  have hC : (40 : ℝ) ≤ (hintLenC KCR : ℝ) := by
    have h := forty_le_hintLenC KCR
    exact_mod_cast h
  unfold hintLenAlpha
  have : 0 < K + (hintLenC KCR : ℝ) := by linarith
  positivity

/-- `K·C + α/4 ≤ α` for *every* `C ≥ 0` (not only `C ≤ 40`): `3(K+C)² ≥ 4KC`. -/
theorem charge_alpha_general {K C : ℝ} (hC : 0 ≤ C) :
    K * C + (K + C) ^ 2 / 4 ≤ (K + C) ^ 2 := by
  nlinarith [sq_nonneg K, sq_nonneg C, sq_nonneg (K + C)]

/-- `α = (K+C)² ≥ 1600` for `K > 0`, because `C ≥ 40`. -/
theorem hintLenAlpha_ge (KCR : ℝ) {K : ℝ} (hK : 0 < K) : (1600 : ℝ) ≤ hintLenAlpha KCR K := by
  have hC : (40 : ℝ) ≤ (hintLenC KCR : ℝ) := by
    have h := forty_le_hintLenC KCR
    exact_mod_cast h
  unfold hintLenAlpha
  have h2 : (0 : ℝ) ≤ K + (hintLenC KCR : ℝ) := by linarith
  nlinarith only [hC, hK, h2, sq_nonneg (K + (hintLenC KCR : ℝ))]

/-- `0 ≤ C₂`. -/
theorem hintLenC₂_nonneg {KCR : ℝ} {K : ℝ} (hK : 0 < K) :
    (0 : ℝ) ≤ hintLenC₂ KCR K := by
  have h1 : (0 : ℝ) ≤ 64 * (K + 1) * ((hintLenC KCR : ℝ) + 1) :=
    mul_nonneg (mul_nonneg (by norm_num) (by linarith)) (by positivity)
  have h2 : (0 : ℝ) ≤ max KCR 0 := le_max_right _ _
  unfold hintLenC₂
  linarith only [h1, h2]

/-- `4·KCR ≤ C₂` (`cheap` leaf). -/
theorem four_KCR_le_C₂ {KCR : ℝ} {K : ℝ} (hK : KCR ≤ K) (hK0 : 0 < K) :
    4 * KCR ≤ hintLenC₂ KCR K := by
  have hmax : KCR ≤ max KCR 0 := le_max_left _ _
  have hmax0 : (0 : ℝ) ≤ max KCR 0 := le_max_right _ _
  have h1 : (0 : ℝ) ≤ 64 * (K + 1) * ((hintLenC KCR : ℝ) + 1) :=
    mul_nonneg (mul_nonneg (by norm_num) (by linarith)) (by positivity)
  unfold hintLenC₂
  linarith only [hmax, hmax0, h1]

/-- `16·KCR ≤ C₂` (`direct`/`recursive` residual). -/
theorem sixteen_KCR_le_C₂ {KCR : ℝ} {K : ℝ} (hK : KCR ≤ K) (hK0 : 0 < K) :
    16 * KCR ≤ hintLenC₂ KCR K := by
  have hmax : KCR ≤ max KCR 0 := le_max_left _ _
  have hmax0 : (0 : ℝ) ≤ max KCR 0 := le_max_right _ _
  have h1 : (0 : ℝ) ≤ 64 * (K + 1) * ((hintLenC KCR : ℝ) + 1) :=
    mul_nonneg (mul_nonneg (by norm_num) (by linarith)) (by positivity)
  unfold hintLenC₂
  linarith only [hmax, hmax0, h1]

/-- `0 ≤ C₁`. -/
theorem hintLenC₁_nonneg {KCR : ℝ} {K : ℝ} (hK0 : 0 < K) : (0 : ℝ) ≤ hintLenC₁ KCR K := by
  have hE : (0 : ℝ) ≤ (hintLenE KCR : ℝ) := by positivity
  have h2 : (0 : ℝ) ≤ 2 * ((hintLenE KCR : ℝ) + 1) + 2 := by linarith only [hE]
  have h1 : (0 : ℝ) ≤ 2 * hintLenC₂ KCR K * ((hintLenE KCR : ℝ) + 1) :=
    mul_nonneg (mul_nonneg (by norm_num) (hintLenC₂_nonneg hK0)) (by linarith only [hE])
  have h3 : (0 : ℝ) ≤ (2 : ℝ) ^ 24 * (K + 1) * (((hintLenC KCR : ℝ) + 1) ^ 2) *
      ((hintLenE KCR : ℝ) + 1) :=
    mul_nonneg
      (mul_nonneg (mul_nonneg (by norm_num) (by linarith)) (by positivity)) (by linarith only [hE])
  unfold hintLenC₁
  linarith only [h1, h2, h3]

/-- `2E ≤ C₁` (the `direct` leaf's relative overhead). -/
theorem two_E_le_C₁ {KCR : ℝ} {K : ℝ} (hK : 0 < K) :
    2 * (hintLenE KCR : ℝ) ≤ hintLenC₁ KCR K := by
  have hE : (0 : ℝ) ≤ (hintLenE KCR : ℝ) := by positivity
  have h1 : (0 : ℝ) ≤ (2 : ℝ) ^ 24 * (K + 1) * (((hintLenC KCR : ℝ) + 1) ^ 2) *
      ((hintLenE KCR : ℝ) + 1) :=
    mul_nonneg
      (mul_nonneg (mul_nonneg (by norm_num) (by linarith)) (by positivity)) (by linarith only [hE])
  have h2 : (0 : ℝ) ≤ 2 * hintLenC₂ KCR K * ((hintLenE KCR : ℝ) + 1) :=
    mul_nonneg (mul_nonneg (by norm_num) (hintLenC₂_nonneg hK)) (by linarith only [hE])
  unfold hintLenC₁
  linarith only [h1, h2]

/-- `2·C₂·(E+1) ≤ C₁`: `C₁` contains that term by construction. -/
theorem two_C₂_E_le_C₁ {KCR : ℝ} {K : ℝ} (hK : 0 < K) :
    2 * hintLenC₂ KCR K * ((hintLenE KCR : ℝ) + 1) ≤ hintLenC₁ KCR K := by
  have hE : (0 : ℝ) ≤ (hintLenE KCR : ℝ) := by positivity
  have h1 : (0 : ℝ) ≤ (2 : ℝ) ^ 24 * (K + 1) * (((hintLenC KCR : ℝ) + 1) ^ 2) *
      ((hintLenE KCR : ℝ) + 1) :=
    mul_nonneg
      (mul_nonneg (mul_nonneg (by norm_num) (by linarith)) (by positivity)) (by linarith only [hE])
  have h3 : (0 : ℝ) ≤ 2 * ((hintLenE KCR : ℝ) + 1) + 2 := by linarith only [hE]
  unfold hintLenC₁
  linarith only [h1, h3]

/-- `2·C₂·(E+1) ≤ C₁·α`. -/
theorem two_C₂_E_le_C₁_alpha {KCR : ℝ} {K : ℝ} (hK0 : 0 < K) :
    2 * hintLenC₂ KCR K * ((hintLenE KCR : ℝ) + 1) ≤ hintLenC₁ KCR K * hintLenAlpha KCR K := by
  have h1 := two_C₂_E_le_C₁ (KCR := KCR) hK0
  have hC1 : (0 : ℝ) ≤ hintLenC₁ KCR K := hintLenC₁_nonneg hK0
  have ha := hintLenAlpha_ge KCR hK0
  have h3 : hintLenC₁ KCR K ≤ hintLenC₁ KCR K * hintLenAlpha KCR K := by
    nlinarith only [hC1, ha]
  linarith only [h1, h3]

/-- `E + 1 ≤ C₃` (the `λ log^q n` bucket contains the additive part). -/
theorem E_add_one_le_C₃ (KCR : ℝ) {K : ℝ} (hK : 0 < K) :
    (hintLenE KCR : ℝ) + 1 ≤ hintLenC₃ KCR K := by
  have hK1 : (0 : ℝ) ≤ K + 1 := by linarith
  have h : (0 : ℝ) ≤ (2 : ℝ) ^ 30 * (K + 1) ^ 8 * ((hintLenC KCR : ℝ) + 1) ^ 4 *
      ((hintLenA KCR : ℝ) + 1) := by
    have h1 : (0 : ℝ) ≤ (2 : ℝ) ^ 30 * (K + 1) ^ 8 := by
      have h2 : (0 : ℝ) ≤ (K + 1) ^ 8 := pow_nonneg hK1 8
      nlinarith only [h2]
    exact mul_nonneg (mul_nonneg h1 (by positivity)) (by positivity)
  unfold hintLenC₃
  linarith only [h]

/-- `0 ≤ C₃`. -/
theorem hintLenC₃_nonneg (KCR : ℝ) {K : ℝ} (hK : 0 < K) :
    (0 : ℝ) ≤ hintLenC₃ KCR K := by
  have h : (0 : ℝ) ≤ (hintLenE KCR : ℝ) := by positivity
  have h2 := E_add_one_le_C₃ KCR hK
  linarith only [h2, h]

/-- `L^3 ≤ L^q` for `L ≥ 1`, `q ≥ 3`. -/
theorem pow_three_le_pow_q {L : ℝ} (hL1 : 1 ≤ L) {q : ℕ} (hq : 3 ≤ q) : L ^ 3 ≤ L ^ q := by
  have hq' : q = 3 + (q - 3) := by omega
  rw [hq', pow_add]
  have h1 : (1 : ℝ) ≤ L ^ (q - 3) := one_le_pow₀ hL1
  have h2 : (0 : ℝ) ≤ L ^ 3 := by positivity
  nlinarith only [h1, h2]

/-- `L^2 ≤ L^q` for `L ≥ 1`, `q ≥ 2`. -/
theorem pow_two_le_pow_q {L : ℝ} (hL1 : 1 ≤ L) {q : ℕ} (hq : 2 ≤ q) : L ^ 2 ≤ L ^ q := by
  have hq' : q = 2 + (q - 2) := by omega
  rw [hq', pow_add]
  have h1 : (1 : ℝ) ≤ L ^ (q - 2) := one_le_pow₀ hL1
  have h2 : (0 : ℝ) ≤ L ^ 2 := by positivity
  nlinarith only [h1, h2]

/-! ## 4. The five program-free conjuncts, as named `Prop`s

Each of these is the exact shape that has to be proved.  Conjunct 4 is proved in §9f–9g
(`hintLengthOK`) and conjunct 5 in §9h (`hintColumnOK`).  They are stated here so that a later
session only has to fill in proofs, and so that the machine conjuncts can be glued on. -/

/-- Theorem 5.1, conjunct 1. -/
def HintWidthOK (K : ℝ) (n : ℕ) : Prop := WidthOK (hintW K n) n (hintcW K) (lg n)

/-- Theorem 5.1, conjunct 2.  The width is `hintW K n`, where `K` has to dominate the *hidden*
constant of Lemma 5.10: with the literal multiplier `1024` of the previous session, conjunct 2 was
**false**. -/
def HintFits (K : ℝ) (n : ℕ) (T : Node) : Prop := (hintSpec T).Fits (hintW K n)

/-- Theorem 5.1, conjunct 3.  Same remark as for `HintFits`; the statement also needs the residual
row bound of Proposition 2.3 for `CR` (with the *same* `K`). -/
def HintWordsOK (K : ℝ) (n : ℕ) (CR : CRFamily) (T : Node) : Prop :=
  wordsOf (hintW K n) (synLen CR T) ≤ 2 ^ hintW K n

/-- Theorem 5.1, conjunct 4: the paper's length bound, equation `hint-forest-length`
(`(1+O(1/log n))(X + α h_N(Y)) + O(N/log⁸ n) + λ log^{O(1)} n`).  The constants are those of §3c:
functions of the witnesses of Lemmas 5.9/5.10, hence absolute (no dependence on `n, lam, N, X, Y`),
and the two that must grow with the witnesses (`p₁` with `A`, `C₁` with `C`) are defined that way. -/
def HintLengthOK (K KCR : ℝ) (CR : CRFamily) (T : Node) (n lam N X Y : ℕ) : Prop :=
  (synLen CR T : ℝ) ≤ (1 + hintLenC₁ KCR K / lg n) * ((X : ℝ) + hintLenAlpha KCR K * hN N Y) +
    hintLenC₂ KCR K * ((N : ℝ) / lg n ^ 8) +
      hintLenC₃' KCR K * (lam : ℝ) * lg n ^ hintLenP₁ KCR

/-- Theorem 5.1, conjunct 5: column locality `Cu log^{pu} n`, applied to each `H r`. -/
def HintColumnOK {N M : ℕ} (K : ℝ) (H : (Fin N → ZMod 2) →ₗ[ZMod 2] (Fin M → ZMod 2)) (n : ℕ) :
    Prop :=
  ColumnWeightLE H (hintCu K * lg n ^ hintpu)

/-! ## 4b. Conjunct 1 proved -/

/-- Theorem 5.1, conjunct 1, as in the paper: `W = Θ(log n)` with `cW = 16384(K+2)`. -/
theorem hintWidthOK {K : ℝ} (hK : 0 ≤ K) {n : ℕ} (hn : 2 ≤ n) : HintWidthOK K n := by
  unfold HintWidthOK WidthOK
  refine ⟨?_, ?_, ?_⟩
  · show 1 ≤ hintW K n
    rw [hintW]
    exact Nat.mul_pos (Nat.mul_pos (by norm_num) (by omega)) (by omega)
  · show Nat.clog 2 n ≤ hintW K n
    rw [Nat.clog_le_iff_le_pow (by norm_num)]
    exact n_le_two_pow_hintW K n
  · exact hintW_le_lgn hK hn

/-! ## 5. Linearity of the sketch in the input

`Node.sketch` is binary linear in `x` (as the paper's §3.1 remark says: "The map is binary linear:
columns are linear in `x`"), and `bitVal` — the flattened sketch — inherits this.  This is what makes
`H r` a `LinearMap`.  We prove the `Finset` identities one layer at a time:

* `rowImage_symmDiff`: the row-local image of `x + x'` is the symmetric difference of the images;
* `rowsWhere_add`: a row-level predicate `A_j + B_j = 1` gives the symmetric difference of the
  supports (this is where `ZMod 2` is used: `{0,1}` has no other elements);
* `column_symmDiff`: the paper's column `C_s(x)`;
* `sketch_symmDiff`: the CR syndrome. -/

section Linearity

open Classical in
/-- The row-local image is additive in the set, for a nonempty row (`m > 0`): two coordinates with the
same row and the same local index coincide, so membership is unique and parity is preserved. -/
lemma rowImage_symmDiff (N m : ℕ) (hm : 0 < m) (π : Equiv.Perm (Fin N)) (j : ℕ)
    (S S' : Finset ℕ) :
    rowImage N m π j (symmDiff S S') = symmDiff (rowImage N m π j S) (rowImage N m π j S') := by
  classical
  have key : ∀ i i' : Fin N, (π i).val % m = (π i').val % m →
      (π i).val / m = (π i').val / m → i = i' := by
    intro i i' h1 h2
    have e1 := Nat.div_add_mod (π i).val m
    have e2 := Nat.div_add_mod (π i').val m
    have e : (π i).val = (π i').val := by
      rw [h1, h2] at e1
      rw [e1] at e2
      exact e2
    exact π.injective (Fin.ext e)
  ext a
  simp only [rowImage, mem_image, mem_filter, mem_univ, true_and, mem_symmDiff]
  constructor
  · rintro ⟨i, ⟨hi, hj⟩, ha⟩
    rcases hi with ⟨hS, hS'⟩ | ⟨hS, hS'⟩
    · left
      refine ⟨⟨i, ⟨hS, hj⟩, ha⟩, ?_⟩
      rintro ⟨i', ⟨hi', hj'⟩, ha'⟩
      have h : i' = i := key i' i (hj'.trans hj.symm) (ha'.trans ha.symm)
      rw [h] at hi'
      exact hS' hi'
    · right
      refine ⟨⟨i, ⟨hS, hj⟩, ha⟩, ?_⟩
      rintro ⟨i', ⟨hi', hj'⟩, ha'⟩
      have h : i' = i := key i' i (hj'.trans hj.symm) (ha'.trans ha.symm)
      rw [h] at hi'
      exact hS' hi'
  · rintro (⟨⟨i, ⟨hS, hj⟩, ha⟩, hnot⟩ | ⟨⟨i, ⟨hS, hj⟩, ha⟩, hnot⟩)
    · refine ⟨i, ⟨?_, hj⟩, ha⟩
      exact Or.inl ⟨hS, fun hc => hnot ⟨i, ⟨hc, hj⟩, ha⟩⟩
    · refine ⟨i, ⟨?_, hj⟩, ha⟩
      exact Or.inr ⟨hS, fun hc => hnot ⟨i, ⟨hc, hj⟩, ha⟩⟩

/-- `ZMod 2` has only the values `0` and `1`. -/
lemma zmod2_eq_zero_or_one (a : ZMod 2) : a = 0 ∨ a = 1 := by
  have hlt : ZMod.val a < 2 := ZMod.val_lt a
  have hcast : ((ZMod.val a : ℕ) : ZMod 2) = a := ZMod.natCast_zmod_val a
  have h : ZMod.val a = 0 ∨ ZMod.val a = 1 := by omega
  rcases h with h | h
  · left
    rw [← hcast, h]
    simp
  · right
    rw [← hcast, h]
    simp

/-- In `ZMod 2`, `a + b = 1` is exactly "one of `a`, `b` is `1` and the other `0`". -/
lemma zmod2_add_eq_one_iff (a b : ZMod 2) :
    a + b = 1 ↔ (a = 1 ∧ b = 0) ∨ (a = 0 ∧ b = 1) := by
  rcases zmod2_eq_zero_or_one a with rfl | rfl <;> rcases zmod2_eq_zero_or_one b with rfl | rfl <;>
    decide

open Classical in
/-- At one node, the support `{j : A_j + B_j = 1}` is the symmetric difference of the supports of
`A` and of `B`. -/
lemma rowsWhere_add (sch : RowScheme) (A B : Fin sch.m → ZMod 2) :
    sch.rowsWhere (fun j => A j + B j = 1) =
      symmDiff (sch.rowsWhere (fun j => A j = 1)) (sch.rowsWhere (fun j => B j = 1)) := by
  classical
  ext a
  simp only [RowScheme.rowsWhere, mem_symmDiff, mem_image, mem_filter, mem_univ, true_and]
  constructor
  · rintro ⟨i, hi, rfl⟩
    rcases (zmod2_add_eq_one_iff (A i) (B i)).1 hi with ⟨hA, hB⟩ | ⟨hA, hB⟩
    · left
      refine ⟨⟨i, hA, rfl⟩, ?_⟩
      rintro ⟨i', hi', hv⟩
      have h : i' = i := Fin.ext hv
      rw [h, hB] at hi'
      exact zero_ne_one hi'
    · right
      refine ⟨⟨i, hB, rfl⟩, ?_⟩
      rintro ⟨i', hi', hv⟩
      have h : i' = i := Fin.ext hv
      rw [h, hA] at hi'
      exact zero_ne_one hi'
  · rintro (⟨⟨i, hi, hv⟩, hnot⟩ | ⟨⟨i, hi, hv⟩, hnot⟩)
    · refine ⟨i, ?_, hv⟩
      rw [zmod2_add_eq_one_iff]
      left
      refine ⟨hi, ?_⟩
      rcases zmod2_eq_zero_or_one (B i) with h | h
      · exact h
      · exact absurd ⟨i, ⟨h, hv⟩⟩ hnot
    · refine ⟨i, ?_, hv⟩
      rw [zmod2_add_eq_one_iff]
      right
      refine ⟨?_, hi⟩
      rcases zmod2_eq_zero_or_one (A i) with h | h
      · exact h
      · exact absurd ⟨i, ⟨h, hv⟩⟩ hnot

open Classical in
/-- The paper's column `C_s(x)` is additive in `x` (for an empty row scheme both sides are empty). -/
lemma column_symmDiff (sch : RowScheme) (lr : sch.LocalSeed) (x y : Finset ℕ) (s : Fin sch.ℓ) :
    sch.column lr (symmDiff x y) s = symmDiff (sch.column lr x s) (sch.column lr y s) := by
  classical
  rcases Nat.eq_zero_or_pos sch.m with hm | hm
  · have hempty : (univ : Finset (Fin sch.m)) = ∅ := by
      have hc : (univ : Finset (Fin sch.m)).card = 0 := by simp [hm]
      exact Finset.card_eq_zero.mp hc
    simp [RowScheme.column, RowScheme.rowsWhere, hempty]
  · unfold RowScheme.column
    have hrow : ∀ j, sch.rowOf lr (symmDiff x y) j = symmDiff (sch.rowOf lr x j) (sch.rowOf lr y j) :=
      fun j => rowImage_symmDiff sch.N sch.m hm lr.1 j x y
    have hcode : ∀ j, sch.code j (lr.2 j) (sch.rowOf lr (symmDiff x y) j) s =
        sch.code j (lr.2 j) (sch.rowOf lr x j) s + sch.code j (lr.2 j) (sch.rowOf lr y j) s := by
      intro j
      rw [hrow j, sch.code_linear]
    simp only [hcode]
    exact rowsWhere_add sch _ _

end Linearity

/-! ## 6. The CR syndrome is additive -/

/-- Filtering commutes with the symmetric difference. -/
lemma filter_symmDiff (p : ℕ → Prop) [DecidablePred p] (A B : Finset ℕ) :
    (symmDiff A B).filter p = symmDiff (A.filter p) (B.filter p) := by
  classical
  ext a
  simp only [mem_symmDiff, mem_filter]
  tauto

/-- The parity of a symmetric-difference cardinality is the XOR of the two parities (each coordinate
in the intersection contributes twice). -/
lemma odd_card_symmDiff (A B : Finset ℕ) :
    Odd (symmDiff A B).card ↔ (Odd A.card ∧ ¬ Odd B.card) ∨ (Odd B.card ∧ ¬ Odd A.card) := by
  classical
  have hdisj1 : Disjoint (A \ B) (B \ A) := by
    rw [Finset.disjoint_left]
    intro a ha hb
    exact (Finset.mem_sdiff.mp ha).2 (Finset.mem_sdiff.mp hb).1
  have hdisj2 : Disjoint (A \ B) (A ∩ B) := by
    rw [Finset.disjoint_left]
    intro a ha hb
    exact (Finset.mem_sdiff.mp ha).2 (Finset.mem_inter.mp hb).2
  have hdisj3 : Disjoint (B \ A) (A ∩ B) := by
    rw [Finset.disjoint_left]
    intro a ha hb
    exact (Finset.mem_sdiff.mp ha).2 (Finset.mem_inter.mp hb).1
  have hAB : (symmDiff A B).card = (A \ B).card + (B \ A).card := by
    rw [symmDiff_def, sup_eq_union]
    exact Finset.card_union_of_disjoint hdisj1
  have hA : A.card = (A \ B).card + (A ∩ B).card := by
    have hunion : A \ B ∪ A ∩ B = A := by
      ext a
      simp only [Finset.mem_union, Finset.mem_sdiff, Finset.mem_inter]
      tauto
    calc A.card = (A \ B ∪ A ∩ B).card := by rw [hunion]
      _ = (A \ B).card + (A ∩ B).card := Finset.card_union_of_disjoint hdisj2
  have hB : B.card = (B \ A).card + (A ∩ B).card := by
    have hunion : B \ A ∪ A ∩ B = B := by
      ext a
      simp only [Finset.mem_union, Finset.mem_sdiff, Finset.mem_inter]
      tauto
    calc B.card = (B \ A ∪ A ∩ B).card := by rw [hunion]
      _ = (B \ A).card + (A ∩ B).card := Finset.card_union_of_disjoint hdisj3
  rw [hAB, hA, hB, Nat.odd_add, Nat.odd_add, Nat.odd_add, ← Nat.not_odd_iff_even,
    ← Nat.not_odd_iff_even]
  tauto

open Classical in
/-- The CR syndrome `CR_{N,t} x` is additive in `x` (each row of the syndrome is one syndrome bit). -/
lemma sketch_symmDiff (CR : CRFamily) (N t : ℕ) (x y : Finset ℕ) :
    CR.sketch N t (symmDiff x y) = symmDiff (CR.sketch N t x) (CR.sketch N t y) := by
  classical
  ext r
  have hfilt : (symmDiff x y).filter (fun i => r ∈ CR.col N t i) =
      symmDiff (x.filter fun i => r ∈ CR.col N t i) (y.filter fun i => r ∈ CR.col N t i) :=
    filter_symmDiff _ x y
  simp only [CRFamily.sketch, hfilt, mem_symmDiff, mem_filter, mem_range, true_and,
    odd_card_symmDiff]
  tauto

/-- A membership indicator is additive over the symmetric difference. -/
lemma ite_mem_symmDiff (A B : Finset ℕ) (a : ℕ) :
    (if a ∈ symmDiff A B then (1 : ZMod 2) else 0) =
      (if a ∈ A then 1 else 0) + (if a ∈ B then 1 else 0) := by
  classical
  by_cases hA : a ∈ A <;> by_cases hB : a ∈ B <;>
    simp [Finset.mem_symmDiff, hA, hB] <;> decide

/-! ## 7. The flat sketch is additive in the support

This is the linearity of `Node.sketch` in `x`, transported to the flattened bit vector `bitVal`:
the machine's stored bits of `x + y` are the sum of the stored bits of `x` and of `y`.  Together
with the seed splitting this makes `H r` a `LinearMap`. -/

theorem bitVal_symmDiff (CR : CRFamily) (T : Node) :
    ∀ (r : Node.Seed T) (p : Fin (synLen CR T)) (x y : Finset ℕ),
      bitVal CR T r p (symmDiff x y) = bitVal CR T r p x + bitVal CR T r p y := by
  induction T with
  | store N =>
      intro r p x y
      simpa only [bitVal] using ite_mem_symmDiff x y p.val
  | cr N t =>
      intro r p x y
      have hs := sketch_symmDiff CR N t x y
      simpa only [bitVal, hs] using ite_mem_symmDiff (CR.sketch N t x) (CR.sketch N t y) p.val
  | direct sch t =>
      intro r p x y
      simp only [bitVal]
      by_cases hp : p.val < sch.m * sch.ℓ
      · have hm : 0 < sch.m := by
          rcases Nat.eq_zero_or_pos sch.m with h | h
          · rw [h, Nat.zero_mul] at hp
            omega
          · exact h
        have hp' : p = Fin.castAdd (CR.rows sch.N t) ⟨p.val, hp⟩ := Fin.ext rfl
        rw [hp', Fin.append_left, Fin.append_left, Fin.append_left]
        simp only [RowScheme.rowOf]
        rw [rowImage_symmDiff sch.N sch.m hm r.1 _ x y, sch.code_linear]
      · have hlt : p.val - sch.m * sch.ℓ < CR.rows sch.N t := by
          have hp2 : p.val < sch.m * sch.ℓ + CR.rows sch.N t := p.isLt
          omega
        have hp' : p = Fin.natAdd (sch.m * sch.ℓ) ⟨p.val - sch.m * sch.ℓ, hlt⟩ := by
          apply Fin.ext
          simp only [Fin.val_natAdd]
          omega
        rw [hp', Fin.append_right, Fin.append_right, Fin.append_right, sketch_symmDiff]
        exact ite_mem_symmDiff _ _ _
  | recursive sch t Xs Ys child ih =>
      intro r p x y
      cases r with
      | mk localSeed childSeeds =>
        simp only [bitVal]
        by_cases hp : p.val < ∑ s : Fin sch.ℓ, synLen CR (child s)
        · have hp' : p = Fin.castAdd (CR.rows sch.N t) ⟨p.val, hp⟩ := Fin.ext rfl
          rw [hp', Fin.append_left, Fin.append_left, Fin.append_left]
          rw [column_symmDiff]
          exact ih _ (childSeeds _) _ _ _
        · have hlt : p.val - (∑ s : Fin sch.ℓ, synLen CR (child s)) < CR.rows sch.N t := by
            have hp2 : p.val < (∑ s : Fin sch.ℓ, synLen CR (child s)) + CR.rows sch.N t := p.isLt
            omega
          have hp' : p = Fin.natAdd (∑ s : Fin sch.ℓ, synLen CR (child s))
              ⟨p.val - (∑ s : Fin sch.ℓ, synLen CR (child s)), hlt⟩ := by
            apply Fin.ext
            simp only [Fin.val_natAdd]
            omega
          rw [hp', Fin.append_right, Fin.append_right, Fin.append_right, sketch_symmDiff]
          exact ite_mem_symmDiff _ _ _

/-! ## 8. The hint matrix `H`

`H r` is the flattened sketch: the support of `x`, flattened through `bitVal`, for the tree seed
obtained from the public seed `r`.  The seed splitting itself is built in section 8b below. -/

/-- The support of a `ZMod 2` vector over `[N]`, as the `Finset ℕ` on which `Node.sketch` acts. -/
def support {N : ℕ} (x : Fin N → ZMod 2) : Finset ℕ := (univ.filter fun i => x i = 1).image Fin.val

/-- The support of a sum is the symmetric difference of the supports. -/
lemma support_add {N : ℕ} (x y : Fin N → ZMod 2) :
    support (x + y) = symmDiff (support x) (support y) := by
  classical
  ext a
  simp only [support, mem_image, mem_filter, mem_univ, true_and, mem_symmDiff]
  constructor
  · rintro ⟨i, hi, rfl⟩
    have hsum : x i + y i = 1 := hi
    rcases (zmod2_add_eq_one_iff (x i) (y i)).1 hsum with ⟨hx, hy⟩ | ⟨hx, hy⟩
    · left
      refine ⟨⟨i, hx, rfl⟩, ?_⟩
      rintro ⟨i', hi', hv⟩
      have h : i' = i := Fin.ext hv
      rw [h, hy] at hi'
      exact zero_ne_one hi'
    · right
      refine ⟨⟨i, hy, rfl⟩, ?_⟩
      rintro ⟨i', hi', hv⟩
      have h : i' = i := Fin.ext hv
      rw [h, hx] at hi'
      exact zero_ne_one hi'
  · rintro (⟨⟨i, hi, hv⟩, hnot⟩ | ⟨⟨i, hi, hv⟩, hnot⟩)
    · refine ⟨i, ?_, hv⟩
      show x i + y i = 1
      rw [zmod2_add_eq_one_iff]
      left
      refine ⟨hi, ?_⟩
      rcases zmod2_eq_zero_or_one (y i) with h | h
      · exact h
      · exact absurd ⟨i, ⟨h, hv⟩⟩ hnot
    · refine ⟨i, ?_, hv⟩
      show x i + y i = 1
      rw [zmod2_add_eq_one_iff]
      right
      refine ⟨?_, hi⟩
      rcases zmod2_eq_zero_or_one (x i) with h | h
      · exact h
      · exact absurd ⟨i, ⟨h, hv⟩⟩ hnot

/-- The zero vector stores nothing. -/
lemma support_zero {N : ℕ} : support (0 : Fin N → ZMod 2) = ∅ := by
  classical
  ext a
  simp [support]

/-- The empty support stores nothing: the flat sketch of `∅` is the zero bit vector. -/
lemma bitVal_empty (CR : CRFamily) (T : Node) (r : Node.Seed T) (p : Fin (synLen CR T)) :
    bitVal CR T r p ∅ = 0 := by
  have h0 : symmDiff (∅ : Finset ℕ) ∅ = ∅ := by
    simp [symmDiff_def]
  have h := bitVal_symmDiff CR T r p ∅ ∅
  rw [h0] at h
  rw [h]
  exact CharTwo.add_self_eq_zero _

/-- `H r` for a fixed seed: the matrix whose `p`-th row is the `p`-th stored bit of the sketch of the
support of `x`.  It is linear in `x` because the support is additive (`support_add`) and the flat
sketch is additive (`bitVal_symmDiff`). -/
def hintH (CR : CRFamily) (T : Node) (κ : (hintSpec T).Seed → Node.Seed T)
    (r : (hintSpec T).Seed) :
    (Fin (Node.N T) → ZMod 2) →ₗ[ZMod 2] (Fin (synLen CR T) → ZMod 2) where
  toFun x := fun p => bitVal CR T (κ r) p (support x)
  map_add' x y := by
    funext p
    simp only [Pi.add_apply]
    rw [support_add, bitVal_symmDiff]
  map_smul' c x := by
    funext p
    simp only [Pi.smul_apply]
    rcases zmod2_eq_zero_or_one c with hc | hc
    · rw [hc]
      simp [support_zero, bitVal_empty]
    · rw [hc]
      simp

/-- The family `r ↦ H r`, i.e. the quintuple's `H : spec.Seed → (Fin N → ZMod 2) →ₗ (Fin M → ZMod 2)`,
with `spec = hintSpec T`, `N = Node.N T`, `M = synLen CR T`. -/
def hintHfun (CR : CRFamily) (T : Node) (κ : (hintSpec T).Seed → Node.Seed T) :
    (hintSpec T).Seed → (Fin (Node.N T) → ZMod 2) →ₗ[ZMod 2] (Fin (synLen CR T) → ZMod 2) :=
  fun r => hintH CR T κ r

/-- `H r` applied: its `p`-th bit is the `p`-th stored bit of the flattened sketch. -/
lemma hintH_apply (CR : CRFamily) (T : Node) (κ : (hintSpec T).Seed → Node.Seed T)
    (r : (hintSpec T).Seed) (x : Fin (Node.N T) → ZMod 2) (p : Fin (synLen CR T)) :
    hintH CR T κ r x p = bitVal CR T (κ r) p (support x) := rfl

/-! ## 8b. The seed splitting `κ`

`TableSpec.Seed` is a *dependent product*: one permutation of size `permSizes.get k` and one
coefficient table of shape `coeffShapes.get k` per index `k`, indexed by `Fin length`.  A tree seed
`Node.Seed T` is instead a *tree-shaped* product: each `direct`/`recursive` node wants
`sch.LocalSeed = Perm (Fin sch.N) × (Fin sch.m → sch.Rand)`.

Splitting the former into the latter has two obstacles, both handled below.

* `RowScheme.Rand` is an **abstract field** of `RowScheme`, so `Fin m_v → sch.Rand` can only be
  identified with `Fin m_v → Fin ℓ_v → Fin N_max,v → ZMod 2` when `sch` is *known* to be
  `P.scheme N_v X_v Y_v`.  Hence `IsSchemeTree P T`, which records the parameters of every node
  (`isSchemeTree_tree` shows that the tree produced by `P.tree` is one).
* the preorder position of a node in `schemeNodes T` has to be transported.  Rather than prove the
  list arithmetic, `permNode`/`coeffAt` read entry `k` with a junk fallback, so the *definition* is
  total for any tree; the fallbacks are never taken on `P.tree`'s output, but nothing below needs to
  know that (`H` is linear for any `κ`).

`Kappa` is the resulting seed splitting, and `hintH_trees` is `H`. -/

/-- Every node of the tree is a `HintSketch` node.  This is *data* (not a `Prop`), because the
parameters `N, X, Y` are exactly what identifies `RowScheme.Rand`. -/
inductive IsSchemeTree (P : HintParams) : Node → Type 1 where
  | store (N : ℕ) : IsSchemeTree P (.store N)
  | cr (N t : ℕ) : IsSchemeTree P (.cr N t)
  | direct (N X Y t : ℕ) : IsSchemeTree P (.direct (P.scheme N X Y) t)
  | recursive (N X Y t : ℕ) (Xs Ys : Fin (P.scheme N X Y).ℓ → ℕ)
      (child : Fin (P.scheme N X Y).ℓ → Node) (hchild : ∀ s, IsSchemeTree P (child s)) :
      IsSchemeTree P (.recursive (P.scheme N X Y) t Xs Ys child)

/-- `allSome f = some g` reads back each value. -/
lemma allSome_spec {α : Type 1} {k : ℕ} (f : Fin k → Option α) (g : Fin k → α)
    (h : HintParams.allSome f = some g) : ∀ s, f s = some (g s) := by
  intro s
  unfold HintParams.allSome at h
  split at h
  · rename_i hsome
    have hfun : (fun s => (f s).get (hsome s)) = g := Option.some.inj h
    rw [← congrFun hfun s]
    exact (Option.some_get (hsome s)).symm
  · exact absurd h (by simp)

/-- `P.tree` only ever builds `P.scheme` nodes, so its output is a scheme tree. -/
def isSchemeTree_tree (P : HintParams) (fuel : ℕ) :
    ∀ (N X Y : ℕ) (T : Node), P.tree fuel N X Y = some T → IsSchemeTree P T := by
  induction fuel with
  | zero =>
      intro N X Y T h
      simp only [HintParams.tree] at h
      exact absurd h (by simp)
  | succ f ih =>
      intro N X Y T h
      simp only [HintParams.tree] at h
      cases hr : P.rule N X Y
      · simp only [hr] at h
        have hT : T = .cr N (HintParams.D N X Y) := by simpa using h.symm
        subst hT
        exact .cr N (HintParams.D N X Y)
      · simp only [hr] at h
        have hT : T = .cr N (HintParams.D N X Y) := by simpa using h.symm
        subst hT
        exact .cr N (HintParams.D N X Y)
      · simp only [hr] at h
        have hex : ∃ child : Fin (P.ell N X Y) → Node,
            HintParams.allSome (fun s : Fin (P.ell N X Y) =>
              P.tree f Y (P.capX N X Y s.val) (P.capY N X Y s.val)) = some child ∧
            (fun child : Fin (P.ell N X Y) → Node =>
              Node.recursive (P.scheme N X Y) (P.resid N X Y)
                (fun s => P.capX N X Y s.val) (fun s => P.capY N X Y s.val) child) child = T :=
          Option.map_eq_some_iff.mp h
        let child := Classical.choose hex
        have hsome : HintParams.allSome (fun s : Fin (P.ell N X Y) =>
            P.tree f Y (P.capX N X Y s.val) (P.capY N X Y s.val)) = some child :=
          (Classical.choose_spec hex).1
        have hT : Node.recursive (P.scheme N X Y) (P.resid N X Y)
            (fun s => P.capX N X Y s.val) (fun s => P.capY N X Y s.val) child = T :=
          (Classical.choose_spec hex).2
        rw [← hT]
        exact .recursive N X Y (P.resid N X Y) _ _ child (fun s =>
          ih Y (P.capX N X Y s.val) (P.capY N X Y s.val) (child s)
            (allSome_spec _ _ hsome s))
      · simp only [hr] at h
        have hT : T = .direct (P.scheme N X Y) (P.resid N X Y) := by simpa using h.symm
        subst hT
        exact .direct N X Y (P.resid N X Y)

/-- The row-coin type of a `HintSketch` node, definitionally equal to `(P.scheme N X Y).Rand`. -/
def NodeCoins (P : HintParams) (N X Y : ℕ) : Type :=
  Fin (P.rows X Y) → Fin (P.ell N X Y) → Fin (P.Nmax N X Y) → ZMod 2

/-- The local seed of a `HintSketch` node, definitionally equal to `(P.scheme N X Y).LocalSeed`. -/
def NodeLocalSeed (P : HintParams) (N X Y : ℕ) : Type :=
  Equiv.Perm (Fin N) × NodeCoins P N X Y

/-- The `k`-th public permutation of `hintSpec R`, with a junk fallback outside the range. -/
def permNode (R : Node) (r : (hintSpec R).Seed) (k N : ℕ) : Equiv.Perm (Fin N) :=
  if h : k < (hintSpec R).permSizes.length then
    if h2 : (hintSpec R).permSizes.get ⟨k, h⟩ = N then
      (h2 ▸ r.1 ⟨k, h⟩ : Equiv.Perm (Fin N))
    else 1
  else 1

/-- The `a`-th bit of the `k`-th coefficient table of `hintSpec R`, junk outside the range. -/
def coeffAt (R : Node) (r : (hintSpec R).Seed) (k a : ℕ) : ZMod 2 :=
  if h : k < (hintSpec R).coeffShapes.length then
    if h' : a < ((hintSpec R).coeffShapes.get ⟨k, h⟩).1 then
      (((r.2 ⟨k, h⟩) ⟨a, h'⟩).val : ZMod 2)
    else 0
  else 0

/-- The row coins of a `HintSketch` node, read from the `k`-th table of `hintSpec R`. -/
def coinsNode (P : HintParams) (R : Node) (r : (hintSpec R).Seed) (N X Y : ℕ) (k : ℕ) :
    NodeCoins P N X Y :=
  fun j s v => coeffAt R r k ((j.val * P.ell N X Y + s.val) * P.Nmax N X Y + v.val)

/-- The seed splitting of a specification into per-node seeds.  `k` is the preorder index of the node
inside `hintSpec R`'s lists; all out-of-range reads return junk. -/
def hintKappaAux (P : HintParams) (R : Node) (r : (hintSpec R).Seed) :
    (T : Node) → IsSchemeTree P T → ℕ → Node.Seed T
  | _, .store N, _ => ()
  | _, .cr N t, _ => ()
  | _, .direct N X Y t, k =>
      (show NodeLocalSeed P N X Y from (permNode R r k N, coinsNode P R r N X Y k))
  | _, .recursive N X Y t _ _ child hchild, k =>
      (show NodeLocalSeed P N X Y from (permNode R r k N, coinsNode P R r N X Y k),
        fun s => hintKappaAux P R r (child s) (hchild s)
          (k + 1 + ((List.ofFn fun i : Fin (P.scheme N X Y).ℓ =>
            (schemeNodes (child i)).length).take s.val).sum))

/-- `κ`: the seed splitting of `hintSpec T` into the tree seed of `Node.Seed T`. -/
def hintKappa (P : HintParams) (T : Node) (hT : IsSchemeTree P T) :
    (hintSpec T).Seed → Node.Seed T :=
  fun r => hintKappaAux P T r T hT 0

/-- `H`: the hint matrix family of Theorem 5.1 for the tree `P.tree` produces.  It is the flattened
sketch `bitVal` at the node seeds that `κ` carves out of the public seed. -/
def hintH_trees (CR : CRFamily) (P : HintParams) (T : Node) (hT : IsSchemeTree P T) :
    (hintSpec T).Seed → (Fin (Node.N T) → ZMod 2) →ₗ[ZMod 2] (Fin (synLen CR T) → ZMod 2) :=
  hintHfun CR T (hintKappa P T hT)

/-- `H` applied: the `p`-th word bit is the `p`-th stored bit of the flattened sketch. -/
lemma hintH_trees_apply (CR : CRFamily) (P : HintParams) (T : Node) (hT : IsSchemeTree P T)
    (r : (hintSpec T).Seed) (x : Fin (Node.N T) → ZMod 2) (p : Fin (synLen CR T)) :
    hintH_trees CR P T hT r x p = bitVal CR T (hintKappa P T hT r) p (support x) := rfl

/-! ## 8c. Sizes: the tree of `P.tree` fits in a word

Conjuncts 2 and 3 are the only place where the *hidden* constant `K` of Lemma 5.10 enters the width;
this is why `hintW` carries the multiplier `⌈K⌉₊ + 2`.  Everything here is of the form
`X ≤ (n+2)^(512(⌈K⌉₊+2))`, and `(n+2)^(512(⌈K⌉₊+2))·(n+2)^(512(⌈K⌉₊+2)) ≤ 2^W`, so the halved
budget also absorbs every constant factor (`c ≤ (n+2)^c`). -/

/-- All unmarked logarithms are to base two. -/
lemma lg_eq_log_div (x : ℝ) : lg x = Real.log x / Real.log 2 := rfl

/-- `lg 2 = 1`. -/
lemma lg_two : lg 2 = 1 := by
  rw [lg_eq_log_div,
    div_self (ne_of_gt (by linarith [Real.log_two_gt_d9] : (0 : ℝ) < Real.log 2))]

/-- `lg` of a product of positive reals. -/
lemma lg_mul_pos {x y : ℝ} (hx : 0 < x) (hy : 0 < y) : lg (x * y) = lg x + lg y := by
  simp only [lg, Real.logb_mul (ne_of_gt hx) (ne_of_gt hy)]

/-- `lg` of a positive power. -/
lemma lg_pow_pos {x : ℝ} (hx : 0 < x) (n : ℕ) : lg (x ^ n) = (n : ℝ) * lg x := by
  rw [lg_eq_log_div, lg_eq_log_div, Real.log_pow]
  push_cast
  field_simp

/-- `lg 16 = 4`. -/
lemma lg_sixteen : lg (16 : ℝ) = 4 := by
  have h : (16 : ℝ) = 2 ^ (4 : ℕ) := by norm_num
  rw [h, lg_pow_pos (by norm_num)]
  simp [lg_two]

/-- `lg x ≤ 2x` for `x ≥ 1`: the paper's `log = O(x)`. -/
lemma lg_le_two_mul (x : ℝ) (hx : 1 ≤ x) : lg x ≤ 2 * x := by
  have h0 : 0 < Real.log 2 := by linarith [Real.log_two_gt_d9]
  rw [lg_eq_log_div, div_le_iff₀ h0]
  have h1 : Real.log x ≤ x - 1 := Real.log_le_sub_one_of_pos (by linarith)
  nlinarith [Real.log_two_gt_d9]

/-- `lg` is nonnegative on `[1, ∞)`. -/
lemma lg_nonneg_of_one_le {x : ℝ} (hx : 1 ≤ x) : 0 ≤ lg x :=
  Real.logb_nonneg (by norm_num) hx

/-- `lg (e) ≤ 2`. -/
lemma lg_exp_one_le_two : lg (Real.exp 1) ≤ 2 := by
  have h0 : 0 < Real.log 2 := by linarith [Real.log_two_gt_d9]
  rw [lg_eq_log_div, Real.log_exp, div_le_iff₀ h0]
  linarith [Real.log_two_gt_d9]

/-- `1 ≤ lg e`. -/
lemma one_le_lg_exp : (1 : ℝ) ≤ lg (Real.exp 1) := by
  have h0 : 0 < Real.log 2 := by linarith [Real.log_two_gt_d9]
  rw [lg_eq_log_div, Real.log_exp, le_div_iff₀ h0]
  linarith [Real.log_two_lt_d9]

/-- `η^{-2} = log^{2A} n` (the `small` rule's residual carries this factor). -/
lemma inv_eta_sq (P : HintParams) : (P.eta ^ 2)⁻¹ = P.lgn ^ (2 * P.A) := by
  have hL : P.eta = (P.lgn ^ P.A)⁻¹ := rfl
  rw [hL, inv_pow, inv_inv, ← pow_mul]
  congr 1
  omega

/-- The width dominates every power `(n+2)^a` with `a ≤ 1024(⌈K⌉₊+2)`. -/
lemma pow_le_two_pow_hintW (K : ℝ) (n a : ℕ) (ha : a ≤ 1024 * (⌈K⌉₊ + 2)) :
    (n + 2) ^ a ≤ 2 ^ hintW K n := by
  have hbase : n + 2 ≤ 2 * 2 ^ Nat.clog 2 (n + 2) := by
    have h := Nat.le_pow_clog (by norm_num : 1 < 2) (n + 2)
    omega
  rw [two_pow_hintW]
  exact le_trans (Nat.pow_le_pow_right (by omega) ha) (Nat.pow_le_pow_left hbase _)

/-- A constant `c ≤ (n+2)^k` times `(n+2)^d` is within the halved budget. -/
lemma mul_pow_le_two_pow_hintW (K : ℝ) (n : ℕ) {c k d : ℕ}
    (hc : c ≤ (n + 2) ^ k) (hkd : k + d ≤ 512 * (⌈K⌉₊ + 2)) :
    c * (n + 2) ^ d ≤ 2 ^ hintW K n := by
  have h1 : c * (n + 2) ^ d ≤ (n + 2) ^ k * (n + 2) ^ d := Nat.mul_le_mul_right _ hc
  rw [← Nat.pow_add] at h1
  exact le_trans h1 (pow_le_two_pow_hintW K n (k + d) (le_trans hkd (by omega)))

/-- The total number of scheme nodes of the children of a node. -/
lemma sum_schemeCount (sch : RowScheme) (child : Fin sch.ℓ → Node) :
    ((List.ofFn fun s : Fin sch.ℓ => (schemeNodes (child s)).length)).sum
      = ∑ s : Fin sch.ℓ, (schemeNodes (child s)).length :=
  List.sum_ofFn

lemma schemeNodes_length_recursive (sch : RowScheme) (t : ℕ) (Xs Ys : Fin sch.ℓ → ℕ)
    (child : Fin sch.ℓ → Node) :
    (schemeNodes (.recursive sch t Xs Ys child)).length
      = 1 + ∑ s : Fin sch.ℓ, (schemeNodes (child s)).length := by
  have h1 : ((List.ofFn fun s : Fin sch.ℓ => schemeNodes (child s)).flatten).length
      = ∑ s : Fin sch.ℓ, (schemeNodes (child s)).length := by
    rw [List.length_flatten, List.map_ofFn]
    exact sum_schemeCount sch child
  rw [schemeNodes, List.length_append, List.length_cons, List.length_nil, h1]

/-- The number of scheme nodes is at most the number of nodes. -/
lemma schemeCount_le_nodeCount (T : Node) : (schemeNodes T).length ≤ Node.nodeCount T := by
  induction T with
  | store N => simp [schemeNodes, Node.nodeCount]
  | cr N t => simp [schemeNodes, Node.nodeCount]
  | direct sch t => simp [schemeNodes, Node.nodeCount]
  | recursive sch t Xs Ys child ih =>
      rw [schemeNodes_length_recursive]
      simp only [Node.nodeCount]
      have h2 : (∑ s : Fin sch.ℓ, (schemeNodes (child s)).length) ≤
          ∑ s : Fin sch.ℓ, Node.nodeCount (child s) := Finset.sum_le_sum fun s _ => ih s
      omega

/-- Lemma 5.10's node count, made explicit: with `A = 100`,
`nodeCount ≤ ⌈K⌉₊·100·2^27·n^27 ≤ (n+2)^(⌈K⌉₊+61)`. -/
lemma nodeCount_le_pow {K : ℝ} (hK : 1 ≤ K) {P : HintParams} {T : Node} (hA : P.A = hintA)
    (hn : 2 ≤ P.n) (hnc : (T.nodeCount : ℝ) ≤ K * (P.A : ℝ) * P.lgn ^ 27) :
    T.nodeCount ≤ (P.n + 2) ^ (⌈K⌉₊ + 61) := by
  have hn1 : (1 : ℝ) ≤ (P.n : ℝ) := by exact_mod_cast (by omega : 1 ≤ P.n)
  have hlg0 : (0 : ℝ) ≤ P.lgn := by
    have h := one_le_lg hn
    show (0 : ℝ) ≤ lg (P.n : ℝ)
    linarith
  have hlgn : P.lgn ≤ 2 * (P.n : ℝ) := lg_le_two_mul _ hn1
  have hpow : P.lgn ^ 27 ≤ (2 : ℝ) ^ 27 * (P.n : ℝ) ^ 27 := by
    have h1 : P.lgn ^ 27 ≤ (2 * (P.n : ℝ)) ^ 27 := pow_le_pow_left₀ hlg0 hlgn 27
    rwa [mul_pow] at h1
  have hA100 : (P.A : ℝ) = 100 := by rw [hA]; norm_num [hintA]
  have hKle : K ≤ (⌈K⌉₊ : ℝ) := Nat.le_ceil K
  -- the real bound, then its natural-number form
  have h2 : (T.nodeCount : ℝ) ≤ 100 * (K * P.lgn ^ 27) := by nlinarith [hA100, hnc]
  have h1 : K * P.lgn ^ 27 ≤ (⌈K⌉₊ : ℝ) * ((2 : ℝ) ^ 27 * (P.n : ℝ) ^ 27) :=
    mul_le_mul hKle hpow (by positivity) (by positivity)
  have h3 : (100 : ℝ) * (K * P.lgn ^ 27) ≤
      100 * ((⌈K⌉₊ : ℝ) * ((2 : ℝ) ^ 27 * (P.n : ℝ) ^ 27)) :=
    mul_le_mul_of_nonneg_left h1 (by norm_num)
  have h4 : (100 : ℝ) * ((⌈K⌉₊ : ℝ) * ((2 : ℝ) ^ 27 * (P.n : ℝ) ^ 27)) =
      ((⌈K⌉₊ * 100 * 2 ^ 27 * P.n ^ 27 : ℕ) : ℝ) := by push_cast; ring
  have hstep : (T.nodeCount : ℝ) ≤ ((⌈K⌉₊ * 100 * 2 ^ 27 * P.n ^ 27 : ℕ) : ℝ) := by
    linarith [h2, h3, h4]
  have hnat : T.nodeCount ≤ ⌈K⌉₊ * 100 * 2 ^ 27 * P.n ^ 27 := by exact_mod_cast hstep
  -- absorb the constants into the halved budget
  have hKb : ⌈K⌉₊ ≤ (P.n + 2) ^ ⌈K⌉₊ := by
    calc ⌈K⌉₊ ≤ 2 ^ ⌈K⌉₊ := le_of_lt Nat.lt_two_pow_self
      _ ≤ (P.n + 2) ^ ⌈K⌉₊ := Nat.pow_le_pow_left (by omega) _
  have h100 : 100 ≤ (P.n + 2) ^ 7 := by
    calc 100 ≤ 2 ^ 7 := by norm_num
      _ ≤ (P.n + 2) ^ 7 := Nat.pow_le_pow_left (by omega) _
  have h227 : 2 ^ 27 ≤ (P.n + 2) ^ 27 := Nat.pow_le_pow_left (by omega) _
  have hn27 : P.n ^ 27 ≤ (P.n + 2) ^ 27 := Nat.pow_le_pow_left (by omega) _
  have ha : ⌈K⌉₊ * 100 ≤ (P.n + 2) ^ ⌈K⌉₊ * (P.n + 2) ^ 7 := Nat.mul_le_mul hKb h100
  have hb : ⌈K⌉₊ * 100 * 2 ^ 27 ≤
      ((P.n + 2) ^ ⌈K⌉₊ * (P.n + 2) ^ 7) * (P.n + 2) ^ 27 := Nat.mul_le_mul ha h227
  have hc : ⌈K⌉₊ * 100 * 2 ^ 27 * P.n ^ 27 ≤
      (((P.n + 2) ^ ⌈K⌉₊ * (P.n + 2) ^ 7) * (P.n + 2) ^ 27) * (P.n + 2) ^ 27 :=
    Nat.mul_le_mul hb hn27
  have he : (((P.n + 2) ^ ⌈K⌉₊ * (P.n + 2) ^ 7) * (P.n + 2) ^ 27) * (P.n + 2) ^ 27
      = (P.n + 2) ^ (⌈K⌉₊ + 61) := by
    rw [← Nat.pow_add, ← Nat.pow_add, ← Nat.pow_add]
  rw [he] at hc
  exact le_trans hnat hc

/-- Lemma 5.10's node count dominates every list of the specification, and the multiplier
`1024(⌈K⌉₊+2)` dominates it. -/
theorem hintFits_lengths {K : ℝ} (hK : 1 ≤ K) {P : HintParams} {T : Node} (hA : P.A = hintA)
    (hn : 2 ≤ P.n) (hnc : (T.nodeCount : ℝ) ≤ K * (P.A : ℝ) * P.lgn ^ 27) :
    (hintSpec T).permSizes.length ≤ 2 ^ hintW K P.n ∧
      (hintSpec T).coeffShapes.length ≤ 2 ^ hintW K P.n := by
  have hfinal : (schemeNodes T).length ≤ 2 ^ hintW K P.n :=
    le_trans (schemeCount_le_nodeCount T)
      (le_trans (nodeCount_le_pow hK hA hn hnc)
        (pow_le_two_pow_hintW K P.n (⌈K⌉₊ + 61) (by omega)))
  refine ⟨?_, ?_⟩ <;> simpa [hintSpec, permSizesOf, coeffShapesOf] using hfinal

/-! ## 8d. Per-node size bounds, and conjunct 2

The paper's §5.2 bounds: every node's universe, row count and `N_max` are at most `n`, and every
node's `ℓ` is `O(log¹⁴ n)`, hence certainly at most `(n+2)^10`.  We prove the uniform (weaker)
bounds, which is what `Fits` needs. -/

/-- `m = max{Y, ⌈X/log³n⌉} ≤ N`. -/
lemma rows_le_N {P : HintParams} {N X Y : ℕ} (hL : 1 ≤ P.lgn) (hXN : X ≤ N) (hYN : Y ≤ N) :
    P.rows X Y ≤ N := by
  unfold HintParams.rows
  refine max_le hYN ?_
  rw [Nat.ceil_le]
  have h3 : (1 : ℝ) ≤ P.lgn ^ 3 := by
    calc (1 : ℝ) = 1 ^ 3 := by norm_num
      _ ≤ P.lgn ^ 3 := pow_le_pow_left₀ (by norm_num) hL 3
  rw [div_le_iff₀ (by linarith : (0 : ℝ) < P.lgn ^ 3)]
  have hX : (X : ℝ) ≤ (N : ℝ) := by exact_mod_cast hXN
  have hN0 : (0 : ℝ) ≤ (N : ℝ) := by positivity
  nlinarith

/-- `N_max = ⌈N/m⌉ ≤ N`. -/
lemma Nmax_le_N {P : HintParams} {N X Y : ℕ} : P.Nmax N X Y ≤ N := by
  unfold HintParams.Nmax
  rw [Nat.ceil_le]
  rcases Nat.eq_zero_or_pos (P.rows X Y) with hm | hm
  · rw [hm]; simp
  · have hmR : (0 : ℝ) < (P.rows X Y : ℝ) := by exact_mod_cast hm
    rw [div_le_iff₀ hmR]
    have hm1 : (1 : ℝ) ≤ (P.rows X Y : ℝ) := by exact_mod_cast hm
    have hN0 : (0 : ℝ) ≤ (N : ℝ) := by positivity
    nlinarith

/-- `lg(e·x) ≤ 2 + 2x` for a natural `x`. -/
lemma lg_exp_mul_nat_le (x : ℕ) : lg (Real.exp 1 * (x : ℝ)) ≤ 2 + 2 * (x : ℝ) := by
  rcases Nat.eq_zero_or_pos x with h0 | h0
  · rw [h0]; push_cast; simp [lg_eq_log_div]
  · have hx1 : (1 : ℝ) ≤ (x : ℝ) := by exact_mod_cast h0
    rw [lg_mul_pos (Real.exp_pos 1) (by linarith)]
    have h1 := lg_exp_one_le_two
    have h2 : lg (x : ℝ) ≤ 2 * (x : ℝ) := lg_le_two_mul _ hx1
    linarith

/-- `lg(16/η²) = 4 + 2A·lg log n ≤ 4 + 800 log n`, the factor of the `small` rule's residual. -/
lemma eta_inv_sq_lg_le {P : HintParams} (hn : 2 ≤ P.n) (hA : P.A = hintA) :
    lg (16 / P.eta ^ 2) ≤ 4 + 800 * (P.n : ℝ) := by
  have hL1 : (1 : ℝ) ≤ P.lgn := one_le_lg hn
  have hlgn : (0 : ℝ) < P.lgn := by linarith
  have hpos : (0 : ℝ) < P.lgn ^ (2 * P.A) := by positivity
  have heta : (16 : ℝ) / P.eta ^ 2 = 16 * P.lgn ^ (2 * P.A) := by
    rw [div_eq_mul_inv, inv_eta_sq]
  rw [heta, lg_mul_pos (by norm_num) hpos, lg_sixteen, lg_pow_pos hlgn]
  have h2A : ((2 * P.A : ℕ) : ℝ) = 200 := by rw [hA]; norm_num [hintA]
  rw [h2A]
  have h1 : lg (P.lgn) ≤ 2 * P.lgn := lg_le_two_mul _ hL1
  have h2 : P.lgn ≤ 2 * (P.n : ℝ) :=
    lg_le_two_mul _ (by exact_mod_cast (by omega : 1 ≤ P.n))
  linarith

/-- A polynomial of degree two is below `(n+2)^10` for `n ≥ 2`. -/
lemma ell_poly_bound {n : ℕ} (hn : 2 ≤ n) :
    2 * (n : ℝ) ^ 2 + 809 * (n : ℝ) + 15 ≤ ((n + 2 : ℕ) : ℝ) ^ 10 := by
  have hcast : ((n + 2 : ℕ) : ℝ) = (n : ℝ) + 2 := by push_cast; ring
  rw [hcast]
  rcases Nat.lt_or_ge n 3 with h | h
  · have hn2 : n = 2 := by omega
    subst hn2
    norm_num
  · have hn3 : (3 : ℝ) ≤ (n : ℝ) := by exact_mod_cast h
    have h1 : 2 * (n : ℝ) ^ 2 + 809 * (n : ℝ) + 15 ≤ 826 * (n : ℝ) ^ 2 := by
      nlinarith [sq_nonneg ((n : ℝ) - 1)]
    have h2 : (826 : ℝ) * (n : ℝ) ^ 2 ≤ (n : ℝ) ^ 10 := by
      have hn8 : (826 : ℝ) ≤ (n : ℝ) ^ 8 := by
        have h38 : (3 : ℝ) ^ 8 ≤ (n : ℝ) ^ 8 := pow_le_pow_left₀ (by norm_num) hn3 8
        have h826 : (826 : ℝ) ≤ (3 : ℝ) ^ 8 := by norm_num
        linarith
      have hm := mul_le_mul_of_nonneg_right hn8 (by positivity : (0 : ℝ) ≤ (n : ℝ) ^ 2)
      calc (826 : ℝ) * (n : ℝ) ^ 2 ≤ (n : ℝ) ^ 8 * (n : ℝ) ^ 2 := hm
        _ = (n : ℝ) ^ 10 := by ring
    have hmono : (n : ℝ) ^ 10 ≤ ((n : ℝ) + 2) ^ 10 :=
      pow_le_pow_left₀ (by positivity) (by linarith) 10
    linarith

/-- The paper's §5.2 node bounds, uniformly: `ell ≤ (n+2)^10`. -/
lemma ell_le {P : HintParams} {N X Y : ℕ} (hn : 2 ≤ P.n) (hNn : N ≤ P.n)
    (hXN : X ≤ N) (hYN : Y ≤ N) (hA : P.A = hintA) :
    P.ell N X Y ≤ (P.n + 2) ^ 10 := by
  have hL1 : (1 : ℝ) ≤ P.lgn := one_le_lg hn
  have hrows : P.rows X Y ≤ N := rows_le_N hL1 hXN hYN
  have hNmax : P.Nmax N X Y ≤ N := Nmax_le_N
  have hBX : P.BX N X Y ≤ N := le_trans (min_le_left _ _) hNmax
  have hBY : P.BY N X Y ≤ N := le_trans (min_le_left _ _) hNmax
  have hx1 : (0 : ℝ) ≤ lg (Real.exp 1 * (P.Nmax N X Y : ℝ)) := by
    rcases Nat.eq_zero_or_pos (P.Nmax N X Y) with h0 | h0
    · rw [h0]; push_cast; simp [lg_eq_log_div]
    · apply lg_nonneg_of_one_le
      have h1 : (1 : ℝ) ≤ (P.Nmax N X Y : ℝ) := by exact_mod_cast h0
      have he : (1 : ℝ) ≤ Real.exp 1 := Real.one_le_exp (by norm_num)
      have h2 : (1 : ℝ) * 1 ≤ Real.exp 1 * (P.Nmax N X Y : ℝ) :=
        mul_le_mul he h1 (by norm_num) (by linarith)
      simpa using h2
  have hc1 : (⌈lg (Real.exp 1 * (P.Nmax N X Y : ℝ))⌉₊ : ℝ) ≤ 3 + 2 * (P.n : ℝ) := by
    have hlt := Nat.ceil_lt_add_one hx1
    have hle := lg_exp_mul_nat_le (P.Nmax N X Y)
    have hNm : (P.Nmax N X Y : ℝ) ≤ (P.n : ℝ) := by exact_mod_cast le_trans hNmax hNn
    linarith
  have hx2 : (0 : ℝ) ≤ lg (16 / P.eta ^ 2) := by
    apply lg_nonneg_of_one_le
    have hlgn : (0 : ℝ) < P.lgn := by linarith
    have h1 : (1 : ℝ) ≤ P.lgn ^ (2 * P.A) := one_le_pow₀ hL1
    rw [div_eq_mul_inv, inv_eta_sq]
    nlinarith
  have hc2 : (⌈lg (16 / P.eta ^ 2)⌉₊ : ℝ) ≤ 5 + 800 * (P.n : ℝ) := by
    have hlt := Nat.ceil_lt_add_one hx2
    have hle := eta_inv_sq_lg_le hn hA
    linarith
  have hell : (P.ell N X Y : ℝ) = (P.BX N X Y : ℝ) +
      (P.BY N X Y : ℝ) * (⌈lg (Real.exp 1 * (P.Nmax N X Y : ℝ))⌉₊ : ℝ) +
      (P.BY N X Y : ℝ) + (⌈lg (16 / P.eta ^ 2)⌉₊ : ℝ) + 10 := by
    unfold HintParams.ell
    push_cast
    ring
  have b1 : (P.BX N X Y : ℝ) ≤ (P.n : ℝ) := by exact_mod_cast le_trans hBX hNn
  have b2 : (P.BY N X Y : ℝ) ≤ (P.n : ℝ) := by exact_mod_cast le_trans hBY hNn
  have b3 : (0 : ℝ) ≤ (⌈lg (Real.exp 1 * (P.Nmax N X Y : ℝ))⌉₊ : ℝ) := by positivity
  have b4 : (P.BY N X Y : ℝ) * (⌈lg (Real.exp 1 * (P.Nmax N X Y : ℝ))⌉₊ : ℝ) ≤
      (P.n : ℝ) * (3 + 2 * (P.n : ℝ)) := mul_le_mul b2 hc1 b3 (by positivity)
  have hbound : (P.ell N X Y : ℝ) ≤ 2 * (P.n : ℝ) ^ 2 + 809 * (P.n : ℝ) + 15 := by
    rw [hell]; linarith [b1, b2, b4, hc2]
  have hpoly := ell_poly_bound hn
  have hfin : (P.ell N X Y : ℝ) ≤ ((P.n + 2 : ℕ) : ℝ) ^ 10 := le_trans hbound hpoly
  rw [← Nat.cast_pow] at hfin
  exact_mod_cast hfin

/-- The uniform §5.2 size bundle: every scheme node's universe, `m`, `ℓ` and `N_max` are small. -/
def NodeSizes (P : HintParams) (fuel : ℕ) (N X Y : ℕ) (T : Node) : Prop :=
  ∀ v ∈ schemeNodes T,
    Node.N v ≤ P.n ∧ nodeM v ≤ P.n ∧ nodeEll v ≤ (P.n + 2) ^ 10 ∧ nodeNmax v ≤ P.n

lemma tree_bound (P : HintParams) (fuel : ℕ) :
    ∀ (N X Y : ℕ) (T : Node), P.tree fuel N X Y = some T → N ≤ P.n → X ≤ N → Y ≤ N →
      2 ≤ P.n → P.A = hintA → NodeSizes P fuel N X Y T := by
  induction fuel with
  | zero =>
      intro N X Y T h
      simp only [HintParams.tree] at h
      exact absurd h (by simp)
  | succ f ih =>
      intro N X Y T h hNn hXN hYN hn hA
      simp only [HintParams.tree] at h
      have hL1 : (1 : ℝ) ≤ P.lgn := one_le_lg hn
      have hn2 : 2 ≤ P.n := hn
      -- the bounds of the node itself
      have key : ∀ (M A B : ℕ), M ≤ P.n → A ≤ M → B ≤ M → Node.N (.direct (P.scheme M A B) 0) ≤ P.n ∧
          nodeM (.direct (P.scheme M A B) 0) ≤ P.n ∧
          nodeEll (.direct (P.scheme M A B) 0) ≤ (P.n + 2) ^ 10 ∧
          nodeNmax (.direct (P.scheme M A B) 0) ≤ P.n := by
        intro M A B hM hA' hB'
        refine ⟨hM, ?_, ?_, ?_⟩
        · show P.rows A B ≤ P.n
          exact le_trans (rows_le_N hL1 hA' hB') hM
        · show P.ell M A B ≤ (P.n + 2) ^ 10
          exact ell_le hn hM hA' hB' hA
        · show P.Nmax M A B ≤ P.n
          exact le_trans Nmax_le_N hM
      cases hr : P.rule N X Y
      · simp only [hr] at h
        have hT : T = .cr N (HintParams.D N X Y) := by simpa using h.symm
        subst hT
        intro v hv
        simp [schemeNodes] at hv
      · simp only [hr] at h
        have hT : T = .cr N (HintParams.D N X Y) := by simpa using h.symm
        subst hT
        intro v hv
        simp [schemeNodes] at hv
      · -- recursive: the node itself plus the children
        simp only [hr] at h
        have hex : ∃ child : Fin (P.ell N X Y) → Node,
            HintParams.allSome (fun s : Fin (P.ell N X Y) =>
              P.tree f Y (P.capX N X Y s.val) (P.capY N X Y s.val)) = some child ∧
            (fun child : Fin (P.ell N X Y) → Node =>
              Node.recursive (P.scheme N X Y) (P.resid N X Y)
                (fun s => P.capX N X Y s.val) (fun s => P.capY N X Y s.val) child) child = T :=
          Option.map_eq_some_iff.mp h
        let child := Classical.choose hex
        have hsome : HintParams.allSome (fun s : Fin (P.ell N X Y) =>
            P.tree f Y (P.capX N X Y s.val) (P.capY N X Y s.val)) = some child :=
          (Classical.choose_spec hex).1
        have hT : Node.recursive (P.scheme N X Y) (P.resid N X Y)
            (fun s => P.capX N X Y s.val) (fun s => P.capY N X Y s.val) child = T :=
          (Classical.choose_spec hex).2
        rw [← hT]
        intro v hv
        simp only [schemeNodes, List.mem_append, List.mem_cons, List.not_mem_nil, or_false,
          List.mem_flatten, List.mem_ofFn] at hv
        rcases hv with rfl | ⟨l', ⟨s, rfl⟩, hvl'⟩
        · obtain ⟨h1, h2, h3, h4⟩ := key N X Y hNn hXN hYN
          exact ⟨h1, h2, h3, h4⟩
        · have hYN' : Y ≤ P.n := le_trans hYN hNn
          have hXY : P.capX N X Y s.val ≤ Y := min_le_left _ _
          have hYY : P.capY N X Y s.val ≤ Y := min_le_left _ _
          exact ih Y (P.capX N X Y s.val) (P.capY N X Y s.val) (child s)
            (allSome_spec _ _ hsome s) hYN' hXY hYY hn hA v hvl'
      · simp only [hr] at h
        have hT : T = .direct (P.scheme N X Y) (P.resid N X Y) := by simpa using h.symm
        subst hT
        intro v hv
        simp only [schemeNodes, List.mem_cons, List.not_mem_nil, or_false] at hv
        subst hv
        obtain ⟨h1, h2, h3, h4⟩ := key N X Y hNn hXN hYN
        exact ⟨h1, h2, h3, h4⟩

/-- Theorem 5.1, conjunct 2, at the tree Lemma 5.10 produces. -/
theorem hintFits_tree {K : ℝ} (hK : 1 ≤ K) {P : HintParams} (hA : P.A = hintA) (hn : 2 ≤ P.n)
    {fuel N X Y : ℕ} {T : Node} (hargs : P.NodeArgs N X Y) (hT : P.tree fuel N X Y = some T)
    (hnc : (T.nodeCount : ℝ) ≤ K * (P.A : ℝ) * P.lgn ^ 27) : HintFits K P.n T := by
  obtain ⟨hargs1, _, hargs3, hargs4, hXN, hYN⟩ := hargs
  obtain ⟨hlen1, hlen2⟩ := hintFits_lengths hK hA hn hnc
  have hb := tree_bound P fuel N X Y T hT hargs4 hXN hYN hn hA
  unfold HintFits
  refine ⟨hlen1, hlen2, ?_, ?_⟩
  · intro a ha
    obtain ⟨v, hv, rfl⟩ := List.mem_map.mp ha
    exact le_trans (hb v hv).1 (n_le_two_pow_hintW K P.n)
  · intro p hp
    obtain ⟨v, hv, rfl⟩ := List.mem_map.mp hp
    obtain ⟨hN, hM, hE, hNM⟩ := hb v hv
    have h1 : nodeM v * nodeEll v * nodeNmax v ≤ P.n * (P.n + 2) ^ 10 * P.n := by
      have h2 : nodeM v * nodeEll v ≤ P.n * (P.n + 2) ^ 10 := Nat.mul_le_mul hM hE
      exact Nat.mul_le_mul h2 hNM
    have h3 : P.n * (P.n + 2) ^ 10 * P.n ≤ (P.n + 2) ^ 2 * (P.n + 2) ^ 10 := by
      have h4 : P.n * P.n ≤ (P.n + 2) * (P.n + 2) :=
        Nat.mul_le_mul (by omega) (by omega)
      calc P.n * (P.n + 2) ^ 10 * P.n = (P.n * P.n) * (P.n + 2) ^ 10 := by ring
        _ ≤ ((P.n + 2) * (P.n + 2)) * (P.n + 2) ^ 10 := Nat.mul_le_mul_right _ h4
        _ = (P.n + 2) ^ 2 * (P.n + 2) ^ 10 := by ring
    have h5 : nodeCoins v = (nodeM v * nodeEll v * nodeNmax v, 2) := rfl
    refine ⟨?_, ?_⟩
    · show (nodeCoins v).1 ≤ 2 ^ hintW K P.n
      rw [show (nodeCoins v).1 = nodeM v * nodeEll v * nodeNmax v from rfl]
      refine le_trans h1 (le_trans h3 ?_)
      exact mul_pow_le_two_pow_hintW K P.n (c := (P.n + 2) ^ 2) (k := 2) (d := 10)
        le_rfl (by omega)
    · show (nodeCoins v).2 ≤ 2 ^ hintW K P.n
      show 2 ≤ 2 ^ hintW K P.n
      have hW : 1 ≤ hintW K P.n := by
        rw [hintW]
        exact Nat.mul_pos (Nat.mul_pos (by norm_num) (by omega)) (by omega)
      calc 2 = 2 ^ 1 := (Nat.pow_one 2).symm
        _ ≤ 2 ^ hintW K P.n := Nat.pow_le_pow_right (by norm_num) hW

/-! ## 8e. Conjunct 3: the stored payload fits in `2^W` words

The paper's §5.4 length accounting (`sec:hint-forest-cost`), first half.  Writing `Len` for `synLen`,
every node of the recursion tree contributes its own stored bits — `m_v·ℓ_v` column bits at a `direct`
leaf, and the residual CR sketch `Len_CR(v) = CR.rows N_v t_v` at any node — so
`Len ≤ nodeCount(T) · ((n+2)^11 + (n+2)^(⌈K⌉₊+7) + (n+2))`, because

* `m_v·ℓ_v ≤ n·(n+2)^10 ≤ (n+2)^11` (the §5.2 bounds `m_v ≤ N_v ≤ n`, `ℓ_v ≤ (n+2)^10`);
* `CR.rows N_v t_v ≤ K·t_v·log²(N_v+2) ≤ (n+2)^(⌈K⌉₊+7)` (Proposition 2.3's row bound, `t_v ≤ N_v ≤ n`);
* at a `store` leaf `N_v ≤ n+2`.

Lemma 5.10's `nodeCount ≤ K·A·log²⁷ n ≤ (n+2)^(⌈K⌉₊+61)` then gives
`Len ≤ (n+2)^(2⌈K⌉₊+73) < 2^W`, since `2^W ≥ (n+2)^(1024(⌈K⌉₊+2))` (`pow_le_two_pow_hintW`), and
`wordsOf W Len ≤ Len`. -/

/-- `1 ≤ W`, so `wordsOf` is well behaved. -/
lemma one_le_hintW (K : ℝ) (n : ℕ) : 1 ≤ hintW K n := by
  rw [hintW]
  exact Nat.mul_pos (Nat.mul_pos (by norm_num) (by omega)) (by omega)

/-- `wordsOf W M = ⌈M/W⌉ ≤ M` for `W ≥ 1`, since `M + W - 1 ≤ M·W`. -/
lemma wordsOf_le_self {W M : ℕ} (hW : 1 ≤ W) : wordsOf W M ≤ M := by
  have hW0 : 0 < W := by omega
  unfold wordsOf
  have h1 : (M + W - 1) / W < M + 1 := by
    rw [Nat.div_lt_iff_lt_mul hW0]
    have hm : M ≤ M * W := by
      have h := Nat.mul_le_mul_left M hW
      simpa using h
    have e : M + W - 1 = M + (W - 1) := by omega
    have e2 : (M + 1) * W = M * W + W := by ring
    omega
  omega

/-- The per-node length budget of §5.4: `m_v·ℓ_v ≤ (n+2)^11` at a `direct` node, the residual CR sketch
`Len_CR` at most `(n+2)^(⌈K⌉₊+7)` bits, and `N_v ≤ n+2` at a `store` leaf. -/
def hintBlk (K : ℝ) (n : ℕ) : ℕ := (n + 2) ^ 11 + (n + 2) ^ (⌈K⌉₊ + 7) + (n + 2)

/-- `n + 2 ≤ Blk`, the `store` leaf's share. -/
lemma le_hintBlk (K : ℝ) (n : ℕ) : n + 2 ≤ hintBlk K n := by
  unfold hintBlk
  omega

/-- `(n+2)^(⌈K⌉₊+7) ≤ Blk`, the residual CR sketch's share. -/
lemma pow_le_hintBlk (K : ℝ) (n : ℕ) : (n + 2) ^ (⌈K⌉₊ + 7) ≤ hintBlk K n := by
  unfold hintBlk
  omega

/-- The per-node size data the length induction needs: every node's universe and residual capacity are
at most `n`, its row count at most `n`, and its column count at most `(n+2)^10` (the §5.2 bounds). -/
def NodeSized (n : ℕ) : Node → Prop
  | .store N => N ≤ n
  | .cr N t => N ≤ n ∧ t ≤ N
  | .direct sch t => sch.N ≤ n ∧ t ≤ sch.N ∧ sch.m ≤ n ∧ sch.ℓ ≤ (n + 2) ^ 10
  | .recursive sch t _ _ child =>
      sch.N ≤ n ∧ t ≤ sch.N ∧ sch.m ≤ n ∧ sch.ℓ ≤ (n + 2) ^ 10 ∧ ∀ s, NodeSized n (child s)

/-- The tree of `P.tree` is `NodeSized`, by the same induction as `tree_bound`. -/
lemma tree_sized (P : HintParams) (fuel : ℕ) :
    ∀ (N X Y : ℕ) (T : Node), P.tree fuel N X Y = some T → N ≤ P.n → X ≤ N → Y ≤ N →
      2 ≤ P.n → P.A = hintA → NodeSized P.n T := by
  induction fuel with
  | zero =>
      intro N X Y T h
      simp only [HintParams.tree] at h
      exact absurd h (by simp)
  | succ f ih =>
      intro N X Y T h hNn hXN hYN hn hA
      simp only [HintParams.tree] at h
      have hL1 : (1 : ℝ) ≤ P.lgn := one_le_lg hn
      have hrows : P.rows X Y ≤ P.n := le_trans (rows_le_N hL1 hXN hYN) hNn
      have hell : P.ell N X Y ≤ (P.n + 2) ^ 10 := ell_le hn hNn hXN hYN hA
      cases hr : P.rule N X Y
      · simp only [hr] at h
        have hT : T = .cr N (HintParams.D N X Y) := by simpa using h.symm
        subst hT
        exact ⟨hNn, min_le_left _ _⟩
      · simp only [hr] at h
        have hT : T = .cr N (HintParams.D N X Y) := by simpa using h.symm
        subst hT
        exact ⟨hNn, min_le_left _ _⟩
      · simp only [hr] at h
        have hex : ∃ child : Fin (P.ell N X Y) → Node,
            HintParams.allSome (fun s : Fin (P.ell N X Y) =>
              P.tree f Y (P.capX N X Y s.val) (P.capY N X Y s.val)) = some child ∧
            (fun child : Fin (P.ell N X Y) → Node =>
              Node.recursive (P.scheme N X Y) (P.resid N X Y)
                (fun s => P.capX N X Y s.val) (fun s => P.capY N X Y s.val) child) child = T :=
          Option.map_eq_some_iff.mp h
        let child := Classical.choose hex
        have hsome : HintParams.allSome (fun s : Fin (P.ell N X Y) =>
            P.tree f Y (P.capX N X Y s.val) (P.capY N X Y s.val)) = some child :=
          (Classical.choose_spec hex).1
        have hT : Node.recursive (P.scheme N X Y) (P.resid N X Y)
            (fun s => P.capX N X Y s.val) (fun s => P.capY N X Y s.val) child = T :=
          (Classical.choose_spec hex).2
        rw [← hT]
        have hYN' : Y ≤ P.n := le_trans hYN hNn
        refine ⟨hNn, min_le_left _ _, hrows, hell, fun s => ?_⟩
        exact ih Y (P.capX N X Y s.val) (P.capY N X Y s.val) (child s)
          (allSome_spec _ _ hsome s) hYN' (min_le_left _ _) (min_le_left _ _) hn hA
      · simp only [hr] at h
        have hT : T = .direct (P.scheme N X Y) (P.resid N X Y) := by simpa using h.symm
        subst hT
        exact ⟨hNn, min_le_left _ _, hrows, hell⟩

/-- The paper's per-node length accounting: `Len ≤ nodeCount · Blk`, as in §5.4. -/
lemma hintLen_le_block (CR : CRFamily) (K : ℝ) (n : ℕ) :
    ∀ T : Node, NodeSized n T →
      (∀ N' t : ℕ, N' ≤ n → t ≤ N' → CR.rows N' t ≤ (n + 2) ^ (⌈K⌉₊ + 7)) →
      synLen CR T ≤ Node.nodeCount T * hintBlk K n := by
  intro T
  induction T with
  | store N =>
      intro h hCR
      have hN : N ≤ n := h
      have h1 : N ≤ hintBlk K n := le_trans (by omega : N ≤ n + 2) (le_hintBlk K n)
      simpa only [synLen, Node.nodeCount, Nat.one_mul] using h1
  | cr N t =>
      intro h hCR
      have h1 : CR.rows N t ≤ hintBlk K n :=
        le_trans (hCR N t h.1 h.2) (pow_le_hintBlk K n)
      simpa only [synLen, Node.nodeCount, Nat.one_mul] using h1
  | direct sch t =>
      intro h hCR
      obtain ⟨hN, ht, hm, hℓ⟩ := h
      have h1 : sch.m * sch.ℓ ≤ (n + 2) ^ 11 := by
        have ha : sch.m * sch.ℓ ≤ n * (n + 2) ^ 10 := Nat.mul_le_mul hm hℓ
        have hb : n * (n + 2) ^ 10 ≤ (n + 2) * (n + 2) ^ 10 :=
          Nat.mul_le_mul_right _ (by omega)
        have hc : (n + 2) * (n + 2) ^ 10 = (n + 2) ^ 11 := by ring
        rw [hc] at hb
        exact le_trans ha hb
      have h2 : CR.rows sch.N t ≤ (n + 2) ^ (⌈K⌉₊ + 7) := hCR sch.N t hN ht
      have h3 : sch.m * sch.ℓ + CR.rows sch.N t ≤
          (n + 2) ^ 11 + (n + 2) ^ (⌈K⌉₊ + 7) := Nat.add_le_add h1 h2
      have h4 : (n + 2) ^ 11 + (n + 2) ^ (⌈K⌉₊ + 7) ≤ hintBlk K n := by
        unfold hintBlk
        omega
      have h5 : sch.m * sch.ℓ + CR.rows sch.N t ≤ hintBlk K n := le_trans h3 h4
      simpa only [synLen, Node.nodeCount, Nat.one_mul] using h5
  | recursive sch t Xs Ys child ih =>
      intro h hCR
      obtain ⟨hN, ht, hm, hℓ, hsmall⟩ := h
      have hchild : ∀ s, synLen CR (child s) ≤ Node.nodeCount (child s) * hintBlk K n :=
        fun s => ih s (hsmall s) hCR
      have h1 : (∑ s : Fin sch.ℓ, synLen CR (child s)) ≤
          (∑ s : Fin sch.ℓ, Node.nodeCount (child s)) * hintBlk K n := by
        rw [Finset.sum_mul]
        exact Finset.sum_le_sum fun s _ => hchild s
      have h2 : CR.rows sch.N t ≤ hintBlk K n :=
        le_trans (hCR sch.N t hN ht) (pow_le_hintBlk K n)
      have h3 : (1 + ∑ s : Fin sch.ℓ, Node.nodeCount (child s)) * hintBlk K n =
          (∑ s : Fin sch.ℓ, Node.nodeCount (child s)) * hintBlk K n + hintBlk K n := by
        rw [Nat.add_mul, Nat.one_mul, Nat.add_comm]
      show (∑ s : Fin sch.ℓ, synLen CR (child s)) + CR.rows sch.N t ≤
        (1 + ∑ s : Fin sch.ℓ, Node.nodeCount (child s)) * hintBlk K n
      rw [h3]
      exact Nat.add_le_add h1 h2

/-- Proposition 2.3's row bound, in the form the length analysis uses: with `t ≤ N' ≤ n` the residual
CR sketch has at most `(n+2)^(⌈K⌉₊+7)` rows. -/
lemma hintLenCR_le_pow {K KCR : ℝ} (hKCR : KCR ≤ K) {n : ℕ} (hn : 2 ≤ n) {CR : CRFamily}
    (hrows : ∀ N' t : ℕ, t ≤ N' → (CR.rows N' t : ℝ) ≤ KCR * ((t : ℝ) * lg ((N' : ℝ) + 2) ^ 2)) :
    ∀ N' t : ℕ, N' ≤ n → t ≤ N' → CR.rows N' t ≤ (n + 2) ^ (⌈K⌉₊ + 7) := by
  intro N' t hN' ht
  have hx1 : (1 : ℝ) ≤ (N' : ℝ) + 2 := by
    have h0 : (0 : ℝ) ≤ (N' : ℝ) := by positivity
    linarith
  have hlg0 : (0 : ℝ) ≤ lg ((N' : ℝ) + 2) := lg_nonneg_of_one_le hx1
  have ht'n : (t : ℝ) ≤ (n : ℝ) := by
    have h : t ≤ n := le_trans ht hN'
    exact_mod_cast h
  have hlg2 : lg ((N' : ℝ) + 2) ≤ 2 * ((n : ℝ) + 2) := by
    have h1 : lg ((N' : ℝ) + 2) ≤ 2 * ((N' : ℝ) + 2) := lg_le_two_mul _ hx1
    have h2 : (N' : ℝ) + 2 ≤ (n : ℝ) + 2 := by
      have h3 : (N' : ℝ) ≤ (n : ℝ) := by exact_mod_cast hN'
      linarith
    linarith
  have hsq : lg ((N' : ℝ) + 2) ^ 2 ≤ (2 * ((n : ℝ) + 2)) ^ 2 :=
    pow_le_pow_left₀ hlg0 hlg2 2
  have hx0 : (0 : ℝ) ≤ (t : ℝ) * lg ((N' : ℝ) + 2) ^ 2 := by positivity
  have h1 := hrows N' t ht
  have h2 : KCR * ((t : ℝ) * lg ((N' : ℝ) + 2) ^ 2) ≤
      K * ((t : ℝ) * lg ((N' : ℝ) + 2) ^ 2) :=
    mul_le_mul_of_nonneg_right hKCR hx0
  have h3 : K * ((t : ℝ) * lg ((N' : ℝ) + 2) ^ 2) ≤
      (⌈K⌉₊ : ℝ) * ((t : ℝ) * lg ((N' : ℝ) + 2) ^ 2) :=
    mul_le_mul_of_nonneg_right (Nat.le_ceil K) hx0
  have h4 : (t : ℝ) * lg ((N' : ℝ) + 2) ^ 2 ≤ (n : ℝ) * (2 * ((n : ℝ) + 2)) ^ 2 :=
    mul_le_mul ht'n hsq (by positivity) (by positivity)
  have h5 : (CR.rows N' t : ℝ) ≤ (⌈K⌉₊ : ℝ) * ((n : ℝ) * (2 * ((n : ℝ) + 2)) ^ 2) := by
    have h34 : K * ((t : ℝ) * lg ((N' : ℝ) + 2) ^ 2) ≤
        (⌈K⌉₊ : ℝ) * ((n : ℝ) * (2 * ((n : ℝ) + 2)) ^ 2) := by
      refine le_trans h3 ?_
      exact mul_le_mul_of_nonneg_left h4 (by positivity)
    linarith [h1, h2, h34]
  have heq : (⌈K⌉₊ : ℝ) * ((n : ℝ) * (2 * ((n : ℝ) + 2)) ^ 2) =
      ((⌈K⌉₊ * n * 4 * (n + 2) ^ 2 : ℕ) : ℝ) := by
    push_cast
    ring
  rw [heq] at h5
  have hnat : CR.rows N' t ≤ ⌈K⌉₊ * n * 4 * (n + 2) ^ 2 := by exact_mod_cast h5
  refine le_trans hnat ?_
  have ha : ⌈K⌉₊ ≤ (n + 2) ^ ⌈K⌉₊ := by
    calc ⌈K⌉₊ ≤ 2 ^ ⌈K⌉₊ := le_of_lt Nat.lt_two_pow_self
      _ ≤ (n + 2) ^ ⌈K⌉₊ := Nat.pow_le_pow_left (by omega) _
  have key : ⌈K⌉₊ * n * 4 * (n + 2) ^ 2 ≤ (n + 2) ^ (⌈K⌉₊ + 4) := by
    have hb2 : n ≤ (n + 2) ^ 1 := by rw [Nat.pow_one]; omega
    have hb3 : 4 ≤ (n + 2) ^ 1 := by rw [Nat.pow_one]; omega
    have s1 : ⌈K⌉₊ * n ≤ (n + 2) ^ ⌈K⌉₊ * (n + 2) ^ 1 := Nat.mul_le_mul ha hb2
    have s2 : ⌈K⌉₊ * n * 4 ≤ ((n + 2) ^ ⌈K⌉₊ * (n + 2) ^ 1) * (n + 2) ^ 1 :=
      Nat.mul_le_mul s1 hb3
    have s3 : ⌈K⌉₊ * n * 4 * (n + 2) ^ 2 ≤
        (((n + 2) ^ ⌈K⌉₊ * (n + 2) ^ 1) * (n + 2) ^ 1) * (n + 2) ^ 2 :=
      Nat.mul_le_mul s2 (le_refl _)
    have he : (((n + 2) ^ ⌈K⌉₊ * (n + 2) ^ 1) * (n + 2) ^ 1) * (n + 2) ^ 2 =
        (n + 2) ^ (⌈K⌉₊ + 4) := by
      rw [← Nat.pow_add, ← Nat.pow_add, ← Nat.pow_add]
    rw [he] at s3
    exact s3
  exact le_trans key (Nat.pow_le_pow_right (by omega) (by omega))

/-- `nodeCount · Blk ≤ (n+2)^(2⌈K⌉₊+73) ≤ 2^W`: the final length budget of §5.4. -/
lemma hintBlk_mul_le_two_pow {K : ℝ} {n : ℕ} (hn : 2 ≤ n) :
    (n + 2) ^ (⌈K⌉₊ + 61) * hintBlk K n ≤ 2 ^ hintW K n := by
  have hb : 4 ≤ n + 2 := by omega
  have hblk : hintBlk K n ≤ 3 * (n + 2) ^ (⌈K⌉₊ + 11) := by
    unfold hintBlk
    have e1 : (n + 2) ^ 11 ≤ (n + 2) ^ (⌈K⌉₊ + 11) :=
      Nat.pow_le_pow_right (by omega) (by omega)
    have e2 : (n + 2) ^ (⌈K⌉₊ + 7) ≤ (n + 2) ^ (⌈K⌉₊ + 11) :=
      Nat.pow_le_pow_right (by omega) (by omega)
    have e3 : (n + 2) ≤ (n + 2) ^ (⌈K⌉₊ + 11) := by
      calc (n + 2) = (n + 2) ^ 1 := (Nat.pow_one (n + 2)).symm
        _ ≤ (n + 2) ^ (⌈K⌉₊ + 11) := Nat.pow_le_pow_right (by omega) (by omega)
    omega
  have h3 : (n + 2) ^ (⌈K⌉₊ + 61) * (n + 2) ^ (⌈K⌉₊ + 11) = (n + 2) ^ (2 * ⌈K⌉₊ + 72) := by
    rw [← Nat.pow_add]
    congr 1
    omega
  have h5 : (n + 2) * (n + 2) ^ (2 * ⌈K⌉₊ + 72) = (n + 2) ^ (2 * ⌈K⌉₊ + 73) := by
    rw [Nat.mul_comm, ← Nat.pow_succ]
  calc (n + 2) ^ (⌈K⌉₊ + 61) * hintBlk K n
      ≤ (n + 2) ^ (⌈K⌉₊ + 61) * (3 * (n + 2) ^ (⌈K⌉₊ + 11)) := Nat.mul_le_mul_left _ hblk
    _ = 3 * ((n + 2) ^ (⌈K⌉₊ + 61) * (n + 2) ^ (⌈K⌉₊ + 11)) := by ring
    _ = 3 * (n + 2) ^ (2 * ⌈K⌉₊ + 72) := by rw [h3]
    _ ≤ (n + 2) * (n + 2) ^ (2 * ⌈K⌉₊ + 72) := Nat.mul_le_mul_right _ (by omega)
    _ = (n + 2) ^ (2 * ⌈K⌉₊ + 73) := h5
    _ ≤ 2 ^ hintW K n := pow_le_two_pow_hintW K n (2 * ⌈K⌉₊ + 73) (by omega)

/-- Theorem 5.1, conjunct 3, at the tree Lemma 5.10 produces: with Proposition 2.3's row bound
(`KCR ≤ K`, the same `K` as in `hintW`) the payload is `Len ≤ (n+2)^(2⌈K⌉₊+73) ≤ 2^W` bits, hence at
most `2^W` words; as in the paper, `Len = O(N log²N)` per node and there are `O(A log²⁷n)` nodes. -/
theorem hintWords_tree {K : ℝ} (hK : 1 ≤ K) {P : HintParams} (hA : P.A = hintA) (hn : 2 ≤ P.n)
    {fuel N X Y : ℕ} {T : Node} (hargs : P.NodeArgs N X Y) (hT : P.tree fuel N X Y = some T)
    (hnc : (T.nodeCount : ℝ) ≤ K * (P.A : ℝ) * P.lgn ^ 27)
    {KCR : ℝ} (hKCR : KCR ≤ K) {CR : CRFamily}
    (hrows : ∀ N' t : ℕ, t ≤ N' → (CR.rows N' t : ℝ) ≤ KCR * ((t : ℝ) * lg ((N' : ℝ) + 2) ^ 2)) :
    HintWordsOK K P.n CR T := by
  obtain ⟨-, -, -, hNn, hXN, hYN⟩ := hargs
  have hsmall : NodeSized P.n T := tree_sized P fuel N X Y T hT hNn hXN hYN hn hA
  have hCR := hintLenCR_le_pow hKCR hn hrows
  have hsyn := hintLen_le_block CR K P.n T hsmall hCR
  have hnode := nodeCount_le_pow hK hA hn hnc
  have hmul : T.nodeCount * hintBlk K P.n ≤ 2 ^ hintW K P.n :=
    le_trans (Nat.mul_le_mul_right _ hnode) (hintBlk_mul_le_two_pow hn)
  unfold HintWordsOK
  exact le_trans (wordsOf_le_self (one_le_hintW K P.n)) (le_trans hsyn hmul)

/-! ## 9. Conjunct 4: the length bound of `eq:hint-forest-length`

The paper's Theorem 5.1 (`thm:hint-forest`), length part, is

  `Len ≤ (1 + C₁/log n)(X + α h_N(N,Y)) + C₂N/log⁸n + C₃λ log^{p₁}n`,

and its proof is the accounting of §5.4 (`sec:hint-forest-cost`): every node's stored bits are bounded
per rule, the `direct`/`cheap` leaves are charged to the paper's *charge* `X + α h_N(N,Y)` (which
contracts down the recursion tree by Lemma 5.9), and the residual cost of the `recursive` nodes is
paid by the additive `λ log^{p₁}n` term, once per node.

This section proves it: §9a–9e supply the toolkit (`h_N` calculus, the stopping-rule thresholds read
off `P.rule`, the sharp `ℓ_v` bound of equation (16) `eq:hint-cap-choices`, the `direct` leaf's
`m_v·ℓ_v` bound), and §9f–9g supply the per-rule cost estimates, the `fuel`-induction on the length
invariant, and the assembly into `HintLengthOK` (`hintLengthOK`). -/

/-! ### 9a. The `h_N` calculus -/

/-- The defining equation of `h_N` away from `z = 0`. -/
lemma hN_of_ne {N : ℕ} {z : ℝ} (hz : z ≠ 0) :
    hN N z = z * lg (Real.exp 1 * (N : ℝ) / z) := by
  unfold hN
  rw [if_neg hz]

/-- `h_N(N,0) = 0` (PDF p.10). -/
@[simp] lemma hN_zero (N : ℕ) : hN N 0 = 0 := by
  unfold hN
  simp

/-- `h_N ≥ 0` on `[0, eN]`. -/
lemma hN_nonneg {N : ℕ} {z : ℝ} (hz : 0 ≤ z) (hzN : z ≤ Real.exp 1 * (N : ℝ)) : 0 ≤ hN N z := by
  rcases eq_or_lt_of_le hz with h0 | hpos
  · rw [← h0, hN_zero]
  · rw [hN_of_ne (ne_of_gt hpos)]
    refine mul_nonneg (le_of_lt hpos) (lg_nonneg_of_one_le ?_)
    rw [le_div_iff₀ hpos]
    simpa using hzN

/-- `0 ≤ h_N(N,Y)` for a valid pair `0 ≤ Y ≤ N`. -/
lemma hN_nonneg_of_le {N : ℕ} {z : ℝ} (hz : 0 ≤ z) (hzN : z ≤ (N : ℝ)) : 0 ≤ hN N z := by
  refine hN_nonneg hz ?_
  have hN0 : (0 : ℝ) ≤ (N : ℝ) := le_trans hz hzN
  have he : (1 : ℝ) ≤ Real.exp 1 := Real.one_le_exp (by norm_num)
  nlinarith

/-- `z ≤ h_N(N,z)` for `0 < z ≤ N`: the paper's `h_N(Y) ≥ Y`. -/
lemma le_hN {N : ℕ} {z : ℝ} (hz : 0 < z) (hzN : z ≤ (N : ℝ)) : z ≤ hN N z := by
  rw [hN_of_ne (ne_of_gt hz)]
  have harg : Real.exp 1 ≤ Real.exp 1 * (N : ℝ) / z := by
    rw [le_div_iff₀ hz]
    exact mul_le_mul_of_nonneg_left hzN (le_of_lt (Real.exp_pos 1))
  have h1 : (1 : ℝ) ≤ lg (Real.exp 1 * (N : ℝ) / z) :=
    le_trans one_le_lg_exp
      (Real.logb_le_logb_of_le (b := 2) (by norm_num) (Real.exp_pos 1) harg)
  calc z = z * 1 := (mul_one z).symm
    _ ≤ z * lg (Real.exp 1 * (N : ℝ) / z) := mul_le_mul_of_nonneg_left h1 (le_of_lt hz)

/-- `h_N` is monotone in `N` (for `0 ≤ z ≤ eN`). -/
lemma hN_mono_N {N N' : ℕ} (hNN' : N ≤ N') {z : ℝ} (hz : 0 ≤ z)
    (hzN : z ≤ Real.exp 1 * (N : ℝ)) : hN N z ≤ hN N' z := by
  rcases eq_or_lt_of_le hz with h0 | hpos
  · rw [← h0, hN_zero, hN_zero]
  · rw [hN_of_ne (ne_of_gt hpos), hN_of_ne (ne_of_gt hpos)]
    have hle : Real.exp 1 * (N : ℝ) ≤ Real.exp 1 * (N' : ℝ) := by
      have hcast : (N : ℝ) ≤ (N' : ℝ) := by exact_mod_cast hNN'
      exact mul_le_mul_of_nonneg_left hcast (le_of_lt (Real.exp_pos 1))
    have h2 : Real.exp 1 * (N : ℝ) / z ≤ Real.exp 1 * (N' : ℝ) / z :=
      div_le_div_of_nonneg_right hle (le_of_lt hpos)
    have hx : (0 : ℝ) < Real.exp 1 * (N : ℝ) / z := div_pos (lt_of_lt_of_le hpos hzN) hpos
    exact mul_le_mul_of_nonneg_left (Real.logb_le_logb_of_le (b := 2) (by norm_num) hx h2) hz

/-- `h_N(N,z) ≤ z(2 + lg N)` for `1 ≤ z ≤ N`: the paper's `h_N(z) = O(z log N)`. -/
lemma hN_le {N : ℕ} {z : ℝ} (hz : 1 ≤ z) (hzN : z ≤ (N : ℝ)) :
    hN N z ≤ z * (2 + lg (N : ℝ)) := by
  have hz0 : (0 : ℝ) < z := lt_of_lt_of_le zero_lt_one hz
  have hN1 : (1 : ℝ) ≤ (N : ℝ) := le_trans hz hzN
  have hN0 : (0 : ℝ) < (N : ℝ) := by linarith
  rw [hN_of_ne (ne_of_gt hz0)]
  have hdiv : Real.exp 1 * (N : ℝ) / z ≤ Real.exp 1 * (N : ℝ) :=
    div_le_self (by positivity) hz
  have hx : (0 : ℝ) < Real.exp 1 * (N : ℝ) / z := div_pos (by positivity) hz0
  have hlg1 : lg (Real.exp 1 * (N : ℝ) / z) ≤ lg (Real.exp 1 * (N : ℝ)) :=
    Real.logb_le_logb_of_le (b := 2) (by norm_num) hx hdiv
  have hlg2 : lg (Real.exp 1 * (N : ℝ)) = lg (Real.exp 1) + lg (N : ℝ) :=
    lg_mul_pos (Real.exp_pos 1) hN0
  have hlg3 : lg (Real.exp 1) ≤ 2 := lg_exp_one_le_two
  have hstep : lg (Real.exp 1 * (N : ℝ) / z) ≤ 2 + lg (N : ℝ) := by
    rw [hlg2] at hlg1
    linarith only [hlg1, hlg3]
  exact mul_le_mul_of_nonneg_left hstep (le_of_lt hz0)

/-! ### 9b. The charge `X + α h_N(N,Y)` contracts

Lemma 5.9's first conclusion is `∑_s X_s ≤ X + K·C·h_N(N,Y)` and its second is
`∑_s h_N(Y,Y_s) ≤ h_N(N,Y)/4`.  With `α = (K+C)²` this makes the *charge*
`X + α h_N(N,Y)` contract: `∑_s (X_s + α h_N(Y,Y_s)) ≤ X + α h_N(N,Y)`, which is what the length
induction uses (the paper's "the inductive step makes the children's total charge at most the
parent's"). -/

/-- The paper's charge of a node: `X + α h_N(N,Y)`. -/
def hintCharge (K : ℝ) (N X Y : ℕ) : ℝ := (X : ℝ) + hintAlpha K * hN N Y

/-- `K·C + α/4 ≤ α` for `0 ≤ C ≤ 40`: the inequality that makes the charge contract (it uses only
`C ≤ C = 40` and `α = (K+C)² ≥ 2KC`). -/
lemma charge_alpha {K C : ℝ} (hK : 0 ≤ K) (hC : C ≤ (hintC : ℝ)) :
    K * C + hintAlpha K / 4 ≤ hintAlpha K := by
  have h40 : (hintC : ℝ) = 40 := by norm_num [hintC]
  rw [h40] at hC
  have h1 : K * C ≤ K * 40 := mul_le_mul_of_nonneg_left hC hK
  unfold hintAlpha
  rw [h40]
  nlinarith [h1, sq_nonneg K, sq_nonneg (K + 40)]

/-! ### 9c. The stopping rules of §5.2, read off `P.rule`

`HintParams.D` does not depend on `P`, so it is written `HintParams.D` and not `P.D`. -/

/-- A `cheap` leaf: `D ≤ N/log^{10}n`. -/
lemma rule_cheap_spec {P : HintParams} {N X Y : ℕ} (h : P.rule N X Y = .cheap) :
    (HintParams.D N X Y : ℝ) ≤ (N : ℝ) / P.lgn ^ 10 := by
  by_contra hc
  have hlt : (N : ℝ) / P.lgn ^ 10 < (HintParams.D N X Y : ℝ) := not_le.mp hc
  unfold HintParams.rule at h
  rw [if_neg (not_le.mpr hlt)] at h
  by_cases h2 : (HintParams.D N X Y : ℝ) ≤
      (P.C : ℝ) ^ 3 * (P.lamStar : ℝ) * P.lgn ^ 6 / P.eta ^ 2
  · rw [if_pos h2] at h
    exact absurd h (by decide)
  · rw [if_neg h2] at h
    by_cases h3 : P.rows X Y = Y
    · rw [if_pos h3] at h
      exact absurd h (by decide)
    · rw [if_neg h3] at h
      exact absurd h (by decide)

/-- A `small` leaf: `D ≤ C³λ_*log⁶n/η²`. -/
lemma rule_small_spec {P : HintParams} {N X Y : ℕ} (h : P.rule N X Y = .small) :
    (HintParams.D N X Y : ℝ) ≤ (P.C : ℝ) ^ 3 * (P.lamStar : ℝ) * P.lgn ^ 6 / P.eta ^ 2 := by
  by_contra hc
  have hlt : (P.C : ℝ) ^ 3 * (P.lamStar : ℝ) * P.lgn ^ 6 / P.eta ^ 2 <
      (HintParams.D N X Y : ℝ) := not_le.mp hc
  unfold HintParams.rule at h
  by_cases h1 : (HintParams.D N X Y : ℝ) ≤ (N : ℝ) / P.lgn ^ 10
  · rw [if_pos h1] at h
    exact absurd h (by decide)
  · rw [if_neg h1, if_neg (not_le.mpr hlt)] at h
    by_cases h3 : P.rows X Y = Y
    · rw [if_pos h3] at h
      exact absurd h (by decide)
    · rw [if_neg h3] at h
      exact absurd h (by decide)

/-- A `direct` node: both leaf rules have failed (`D` is above both thresholds) and `m ≠ Y`. -/
lemma rule_direct_spec {P : HintParams} {N X Y : ℕ} (h : P.rule N X Y = .direct) :
    (N : ℝ) / P.lgn ^ 10 < (HintParams.D N X Y : ℝ) ∧
      (P.C : ℝ) ^ 3 * (P.lamStar : ℝ) * P.lgn ^ 6 / P.eta ^ 2 < (HintParams.D N X Y : ℝ) ∧
      P.rows X Y ≠ Y := by
  unfold HintParams.rule at h
  by_cases h1 : (HintParams.D N X Y : ℝ) ≤ (N : ℝ) / P.lgn ^ 10
  · rw [if_pos h1] at h
    exact absurd h (by decide)
  · rw [if_neg h1] at h
    by_cases h2 : (HintParams.D N X Y : ℝ) ≤
        (P.C : ℝ) ^ 3 * (P.lamStar : ℝ) * P.lgn ^ 6 / P.eta ^ 2
    · rw [if_pos h2] at h
      exact absurd h (by decide)
    · rw [if_neg h2] at h
      by_cases h3 : P.rows X Y = Y
      · rw [if_pos h3] at h
        exact absurd h (by decide)
      · rw [if_neg h3] at h
        exact ⟨not_le.mp h1, not_le.mp h2, h3⟩

/-- A `recursive` node: both leaf rules have failed and `m = Y`. -/
lemma rule_recursive_spec {P : HintParams} {N X Y : ℕ} (h : P.rule N X Y = .recursive) :
    ¬ ((HintParams.D N X Y : ℝ) ≤ (N : ℝ) / P.lgn ^ 10) ∧
      ¬ ((HintParams.D N X Y : ℝ) ≤
        (P.C : ℝ) ^ 3 * (P.lamStar : ℝ) * P.lgn ^ 6 / P.eta ^ 2) ∧
      P.rows X Y = Y := by
  unfold HintParams.rule at h
  by_cases h1 : (HintParams.D N X Y : ℝ) ≤ (N : ℝ) / P.lgn ^ 10
  · rw [if_pos h1] at h
    exact absurd h (by decide)
  · rw [if_neg h1] at h
    by_cases h2 : (HintParams.D N X Y : ℝ) ≤
        (P.C : ℝ) ^ 3 * (P.lamStar : ℝ) * P.lgn ^ 6 / P.eta ^ 2
    · rw [if_pos h2] at h
      exact absurd h (by decide)
    · rw [if_neg h2] at h
      by_cases h3 : P.rows X Y = Y
      · exact ⟨h1, h2, h3⟩
      · rw [if_neg h3] at h
        exact absurd h (by decide)

/-! ### 9d. Elementary facts about the tree -/

/-- Every tree has at least one node. -/
lemma one_le_nodeCount (T : Node) : 1 ≤ T.nodeCount := by
  induction T with
  | store N => simp [Node.nodeCount]
  | cr N t => simp [Node.nodeCount]
  | direct sch t => simp [Node.nodeCount]
  | recursive sch t Xs Ys child ih => simp only [Node.nodeCount]; omega

/-- Every tree has at least one level. -/
lemma one_le_depth (T : Node) : 1 ≤ T.depth := by
  induction T with
  | store N => simp [Node.depth]
  | cr N t => simp [Node.depth]
  | direct sch t => simp [Node.depth]
  | recursive sch t Xs Ys child ih => simp only [Node.depth]; omega

/-- `allSome f = some g` as soon as `f` is pointwise `some (g ·)` (the converse of `allSome_spec`). -/
lemma allSome_some {α : Type 1} {k : ℕ} (f : Fin k → Option α) (g : Fin k → α)
    (h : ∀ s, f s = some (g s)) : HintParams.allSome f = some g := by
  have hsome : ∀ s, (f s).isSome := fun s => by rw [h s]; rfl
  unfold HintParams.allSome
  rw [dif_pos hsome]
  have hfun : (fun s => (f s).get (hsome s)) = g := by
    funext s
    simp only [h s]
    rfl
  rw [hfun]

/-- `P.tree` is monotone in the fuel: once it produces a tree, a larger fuel produces the same one.
This is what lets Lemma 5.10's depth and node-count bounds be applied at the arbitrary `fuel` of the
statement of conjunct 4. -/
lemma tree_mono (P : HintParams) :
    ∀ (fuel N X Y : ℕ) {T : Node}, P.tree fuel N X Y = some T →
      ∀ g, fuel ≤ g → P.tree g N X Y = some T := by
  intro fuel
  induction fuel with
  | zero =>
      intro N X Y T h
      simp only [HintParams.tree] at h
      exact absurd h (by simp)
  | succ f ih =>
      intro N X Y T h g hg
      cases g with
      | zero => omega
      | succ g' =>
        have hg' : f ≤ g' := by omega
        simp only [HintParams.tree] at h ⊢
        cases hr : P.rule N X Y
        · simp only [hr] at h ⊢
          exact h
        · simp only [hr] at h ⊢
          exact h
        · simp only [hr] at h ⊢
          have hex : ∃ child : Fin (P.scheme N X Y).ℓ → Node,
              HintParams.allSome (fun s : Fin (P.scheme N X Y).ℓ =>
                P.tree f Y (P.capX N X Y s.val) (P.capY N X Y s.val)) = some child ∧
              (fun child : Fin (P.scheme N X Y).ℓ → Node =>
                Node.recursive (P.scheme N X Y) (P.resid N X Y)
                  (fun s => P.capX N X Y s.val) (fun s => P.capY N X Y s.val) child) child = T :=
            Option.map_eq_some_iff.mp h
          obtain ⟨chi, hsome, hT⟩ := hex
          have hstep : ∀ s : Fin (P.scheme N X Y).ℓ,
              P.tree g' Y (P.capX N X Y s.val) (P.capY N X Y s.val) = some (chi s) :=
            fun s => ih Y (P.capX N X Y s.val) (P.capY N X Y s.val)
              (allSome_spec _ _ hsome s) g' hg'
          have hsome' : HintParams.allSome (fun s : Fin (P.scheme N X Y).ℓ =>
              P.tree g' Y (P.capX N X Y s.val) (P.capY N X Y s.val)) = some chi :=
            allSome_some _ _ hstep
          refine Option.map_eq_some_iff.mpr ⟨chi, hsome', ?_⟩
          exact hT
        · simp only [hr] at h ⊢
          exact h

/-! ### 9e. The pieces of the sharp `ℓ_v` bound of equation (16)

`eq:hint-cap-choices` is
`ℓ = B_X + B_Y⌈log(eN_max)⌉ + B_Y + ⌈log(16/η²)⌉ + 10` with
`B_X = min{N_max, ⌈log³n + C log²n⌉}` and `B_Y = min{N_max, ⌈C log(log n + 2)⌉ + 4}`.
The two `min`s are what makes `m_v·ℓ_v ≤ X_v + O(C X_v/log n) + O(C log³n)`:
`B_X ≼ log³n + Clog²n` and `B_Y ≼ Clog log n`, which is `\log^{13}n` *without* using `ell_le`. -/

/-- `log n ≥ 0` (it is `0` for `n ≤ 1`). -/
lemma lgn_nonneg (P : HintParams) : 0 ≤ P.lgn := by
  rcases Nat.eq_zero_or_pos P.n with h | h
  · rw [HintParams.lgn, h]
    simp [lg_eq_log_div]
  · exact lg_nonneg_of_one_le (by exact_mod_cast h)

/-- `B_X ≤ log³n + C log²n + 1` (equation (16)). -/
lemma BX_le_sharp (P : HintParams) (N X Y : ℕ) :
    (P.BX N X Y : ℝ) ≤ P.lgn ^ 3 + (P.C : ℝ) * P.lgn ^ 2 + 1 := by
  have h0 : (0 : ℝ) ≤ P.lgn ^ 3 + (P.C : ℝ) * P.lgn ^ 2 := by
    have h1 := lgn_nonneg P
    positivity
  have h1 : P.BX N X Y ≤ ⌈P.lgn ^ 3 + (P.C : ℝ) * P.lgn ^ 2⌉₊ := by
    unfold HintParams.BX
    exact min_le_right _ _
  have h2 : (P.BX N X Y : ℝ) ≤ ((⌈P.lgn ^ 3 + (P.C : ℝ) * P.lgn ^ 2⌉₊ : ℕ) : ℝ) := by
    exact_mod_cast h1
  have h3 := Nat.ceil_lt_add_one h0
  linarith only [h2, h3]

/-- `B_Y ≤ C log(log n + 2) + 5` (equation (16)). -/
lemma BY_le_sharp (P : HintParams) (N X Y : ℕ) :
    (P.BY N X Y : ℝ) ≤ (P.C : ℝ) * lg (P.lgn + 2) + 5 := by
  have hmin : P.BY N X Y ≤ ⌈(P.C : ℝ) * lg (P.lgn + 2)⌉₊ + 4 := by
    unfold HintParams.BY
    exact min_le_right _ _
  have hcast : (P.BY N X Y : ℝ) ≤ ((⌈(P.C : ℝ) * lg (P.lgn + 2)⌉₊ : ℕ) : ℝ) + 4 := by
    exact_mod_cast hmin
  have h0 : (0 : ℝ) ≤ (P.C : ℝ) * lg (P.lgn + 2) := by
    have h1 := lgn_nonneg P
    have h2 : (0 : ℝ) ≤ lg (P.lgn + 2) := lg_nonneg_of_one_le (by linarith)
    positivity
  have hlt := Nat.ceil_lt_add_one h0
  linarith only [hcast, hlt]

/-- `⌈log(eN_max)⌉ ≤ log N_max + 3` (the per-column coefficient count of a node).  The `+3` rather
than `+2` costs nothing: it is an additive constant below, absorbed by the `λ log^{p₁}n` term. -/
lemma ceil_lg_exp_Nmax_le (P : HintParams) (N X Y : ℕ) (hNmax : 1 ≤ P.Nmax N X Y) :
    (⌈lg (Real.exp 1 * (P.Nmax N X Y : ℝ))⌉₊ : ℝ) ≤ lg ((P.Nmax N X Y : ℝ)) + 3 := by
  have hNpos : (0 : ℝ) < (P.Nmax N X Y : ℝ) := by exact_mod_cast hNmax
  have hx0 : (0 : ℝ) ≤ lg (Real.exp 1 * (P.Nmax N X Y : ℝ)) := by
    apply lg_nonneg_of_one_le
    have h1 : (1 : ℝ) ≤ (P.Nmax N X Y : ℝ) := by exact_mod_cast hNmax
    nlinarith [Real.one_le_exp (by norm_num : (0 : ℝ) ≤ 1)]
  have hlt := Nat.ceil_lt_add_one hx0
  have hmul : lg (Real.exp 1 * (P.Nmax N X Y : ℝ)) =
      lg (Real.exp 1) + lg (P.Nmax N X Y : ℝ) := lg_mul_pos (Real.exp_pos 1) hNpos
  have hexp := lg_exp_one_le_two
  linarith only [hlt, hmul, hexp]

/-- `⌈log(16/η²)⌉ ≤ 5 + 2A log log n` (the `small` rule's residual factor). -/
lemma ceil_lg_eta_inv_sq_le {P : HintParams} (hn : 2 ≤ P.n) :
    (⌈lg (16 / P.eta ^ 2)⌉₊ : ℝ) ≤ 5 + 2 * (P.A : ℝ) * lg (P.lgn) := by
  have hL1 : (1 : ℝ) ≤ P.lgn := one_le_lg hn
  have hlgn : (0 : ℝ) < P.lgn := by linarith
  have hpos : (0 : ℝ) < P.lgn ^ (2 * P.A) := by positivity
  have heta : (16 : ℝ) / P.eta ^ 2 = 16 * P.lgn ^ (2 * P.A) := by
    rw [div_eq_mul_inv, inv_eta_sq]
  have hx0 : (0 : ℝ) ≤ lg (16 / P.eta ^ 2) := by
    rw [heta]
    apply lg_nonneg_of_one_le
    have h1 : (1 : ℝ) ≤ P.lgn ^ (2 * P.A) := one_le_pow₀ hL1
    nlinarith
  have hlt := Nat.ceil_lt_add_one hx0
  have hlog : lg (16 / P.eta ^ 2) = 4 + 2 * (P.A : ℝ) * lg (P.lgn) := by
    rw [heta, lg_mul_pos (by norm_num) hpos, lg_sixteen, lg_pow_pos hlgn]
    push_cast
    ring
  linarith only [hlt, hlog]

/-! ### 3d. The sharp `ℓ_v` bound, without `(n+2)^10`

Equation (16) is `ℓ = B_X + B_Y⌈log(eN_max)⌉ + B_Y + ⌈log(16/η²)⌉ + 10` with
`B_X ≤ log³n + Clog²n + 1`, `B_Y ≤ Clog(logn+2) + 5`, `⌈log(eN_max)⌉ ≤ log N_max + 3` and
`⌈log(16/η²)⌉ ≤ 5 + 2A log log n`.  Hence `ℓ ≤ log³n + E log²n` with `E = 32(A+C+2)` — this is the
bound the length induction uses; `ell_le`'s `(n+2)^10` is far too weak. -/

theorem ell_le_four {KCR : ℝ} {P : HintParams}
    (hA : P.A = hintLenA KCR) (hC : P.C = hintLenC KCR)
    (hn : 2 ≤ P.n) {N X Y : ℕ} (hN1 : 1 ≤ N) (hNn : N ≤ P.n) (hXN : X ≤ N) (hYN : Y ≤ N)
    (hm1 : 1 ≤ P.rows X Y) :
    (P.ell N X Y : ℝ) ≤ P.lgn ^ 3 + (hintLenE KCR : ℝ) * P.lgn ^ 2 := by
  have hL1 : 1 ≤ P.lgn := one_le_lg hn
  have hL0 : 0 < P.lgn := by linarith
  have hA0 : (0 : ℝ) ≤ (P.A : ℝ) := by positivity
  have hC0 : (0 : ℝ) ≤ (P.C : ℝ) := by positivity
  have hAr : (P.A : ℝ) = (hintLenA KCR : ℝ) := by rw [hA]
  have hCr : (P.C : ℝ) = (hintLenC KCR : ℝ) := by rw [hC]
  have hL2 : P.lgn ≤ P.lgn ^ 2 := by nlinarith only [hL1]
  have hrowsle : P.rows X Y ≤ N := rows_le_N hL1 hXN hYN
  have hm0 : (0 : ℝ) < (P.rows X Y : ℝ) := by exact_mod_cast hm1
  have hNmax1 : 1 ≤ P.Nmax N X Y := by
    unfold HintParams.Nmax
    have h2 : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN1
    have h3 : (1 : ℝ) ≤ (N : ℝ) / (P.rows X Y : ℝ) := by
      rw [le_div_iff₀ hm0]
      have h4 : (P.rows X Y : ℝ) ≤ (N : ℝ) := by exact_mod_cast hrowsle
      linarith
    have h5 := Nat.le_ceil ((N : ℝ) / (P.rows X Y : ℝ))
    have h6 : (1 : ℝ) ≤ ((⌈(N : ℝ) / (P.rows X Y : ℝ)⌉₊ : ℕ) : ℝ) := le_trans h3 h5
    exact_mod_cast h6
  have hNmaxN : P.Nmax N X Y ≤ N := Nmax_le_N
  have hlgNmax : lg ((P.Nmax N X Y : ℕ) : ℝ) ≤ P.lgn := by
    have hcast : ((P.Nmax N X Y : ℕ) : ℝ) ≤ ((P.n : ℕ) : ℝ) := by
      exact_mod_cast le_trans hNmaxN hNn
    have hpos : (0 : ℝ) < ((P.Nmax N X Y : ℕ) : ℝ) := by
      have h : (1 : ℝ) ≤ ((P.Nmax N X Y : ℕ) : ℝ) := by exact_mod_cast hNmax1
      linarith
    exact Real.logb_le_logb_of_le (by norm_num) hpos hcast
  have hce : (⌈lg (Real.exp 1 * (P.Nmax N X Y : ℝ))⌉₊ : ℝ) ≤ 4 * P.lgn := by
    have h := ceil_lg_exp_Nmax_le P N X Y hNmax1
    linarith only [h, hlgNmax, hL1]
  have hBX := BX_le_sharp P N X Y
  have hBY := BY_le_sharp P N X Y
  have hBY2 : (P.BY N X Y : ℝ) ≤ 6 * (P.C : ℝ) * P.lgn + 5 := by
    have hlgL2 : lg (P.lgn + 2) ≤ 2 * (P.lgn + 2) := lg_le_two_mul _ (by linarith)
    have h2 : (P.C : ℝ) * lg (P.lgn + 2) ≤ (P.C : ℝ) * (2 * (P.lgn + 2)) :=
      mul_le_mul_of_nonneg_left hlgL2 hC0
    have h4 : (4 : ℝ) * (P.C : ℝ) ≤ 4 * (P.C : ℝ) * P.lgn := by nlinarith only [hC0, hL1]
    nlinarith only [hBY, h2, h4]
  have hBYce : (P.BY N X Y : ℝ) * (⌈lg (Real.exp 1 * (P.Nmax N X Y : ℝ))⌉₊ : ℝ)
      ≤ (24 * (P.C : ℝ) + 20) * P.lgn ^ 2 := by
    have hpos : (0 : ℝ) ≤ (⌈lg (Real.exp 1 * (P.Nmax N X Y : ℝ))⌉₊ : ℝ) := by positivity
    have hnn : (0 : ℝ) ≤ 6 * (P.C : ℝ) * P.lgn + 5 := by nlinarith only [hC0, hL1]
    have h1 : (P.BY N X Y : ℝ) * (⌈lg (Real.exp 1 * (P.Nmax N X Y : ℝ))⌉₊ : ℝ)
        ≤ (6 * (P.C : ℝ) * P.lgn + 5) * (4 * P.lgn) := mul_le_mul hBY2 hce hpos hnn
    have h3 : (20 : ℝ) * P.lgn ≤ 20 * P.lgn ^ 2 := by nlinarith only [hL1]
    nlinarith only [h1, h3]
  have h7 : (P.BY N X Y : ℝ) ≤ (6 * (P.C : ℝ) + 5) * P.lgn ^ 2 := by
    have h6 : (P.BY N X Y : ℝ) ≤ (6 * (P.C : ℝ) + 5) * P.lgn := by nlinarith only [hBY2, hL1]
    nlinarith only [h6, hL2]
  have heta := ceil_lg_eta_inv_sq_le (P := P) hn
  have hlgL : lg P.lgn ≤ 2 * P.lgn := lg_le_two_mul P.lgn hL1
  have heta2 : (⌈lg (16 / P.eta ^ 2)⌉₊ : ℝ) ≤ (4 * (P.A : ℝ) + 5) * P.lgn ^ 2 := by
    have h3 : (5 : ℝ) + 2 * (P.A : ℝ) * lg P.lgn ≤ 5 + 4 * (P.A : ℝ) * P.lgn := by
      nlinarith only [hA0, hlgL]
    have h4 : (5 : ℝ) + 4 * (P.A : ℝ) * P.lgn ≤ (4 * (P.A : ℝ) + 5) * P.lgn ^ 2 := by
      nlinarith only [hA0, hL1, hL2]
    linarith only [heta, h3, h4]
  have hell : (P.ell N X Y : ℝ) = (P.BX N X Y : ℝ) +
      (P.BY N X Y : ℝ) * (⌈lg (Real.exp 1 * (P.Nmax N X Y : ℝ))⌉₊ : ℝ) +
      (P.BY N X Y : ℝ) + (⌈lg (16 / P.eta ^ 2)⌉₊ : ℝ) + 10 := by
    unfold HintParams.ell
    push_cast
    ring
  have hE : (31 * (P.C : ℝ) + 4 * (P.A : ℝ) + 41) ≤ (hintLenE KCR : ℝ) := by
    unfold hintLenE
    rw [hAr, hCr]
    push_cast
    linarith only []
  have h1 : (1 : ℝ) ≤ P.lgn ^ 2 := one_le_pow₀ hL1
  have hB : (P.BX N X Y : ℝ) +
      (P.BY N X Y : ℝ) * (⌈lg (Real.exp 1 * (P.Nmax N X Y : ℝ))⌉₊ : ℝ) +
      (P.BY N X Y : ℝ) + (⌈lg (16 / P.eta ^ 2)⌉₊ : ℝ) + 10
      ≤ P.lgn ^ 3 + (hintLenE KCR : ℝ) * P.lgn ^ 2 := by
    have h1' : (P.BX N X Y : ℝ) ≤ P.lgn ^ 3 + (P.C : ℝ) * P.lgn ^ 2 + 1 := hBX
    have h8 : (10 : ℝ) ≤ 10 * P.lgn ^ 2 := by linarith only [h1]
    nlinarith only [h1', hBYce, h7, heta2, h8, hE, h1]
  linarith only [hell, hB]

/-! ### 3e. The `direct` leaf: `m_v·ℓ_v ≤ (1 + C₁/(2log n))·X + C₃·λ·log^q n`

This is the only place where the *sharp* equation (16) is needed: `m ≤ X/log³n + 1` (because the node
is `direct`, so `m = ⌈X/log³n⌉ ≠ Y`), and `ℓ ≤ log³n + E log²n`, so the product is
`X + X·E/log n + log³n + E log²n` — exactly the shape of `HintLengthOK`. -/
theorem rows_mul_ell_le {KCR : ℝ} {K : ℝ} {P : HintParams}
    (hA : P.A = hintLenA KCR) (hC : P.C = hintLenC KCR) (hK : 0 < K)
    (hn : 2 ≤ P.n) (hlam : 1 ≤ P.lam) {N X Y : ℕ} (hN1 : 1 ≤ N) (hNn : N ≤ P.n)
    (hXN : X ≤ N) (hYN : Y ≤ N) (hdir : P.rows X Y ≠ Y) :
    (P.rows X Y : ℝ) * (P.ell N X Y : ℝ) ≤
      (1 + hintLenC₁ KCR K / (2 * P.lgn)) * (X : ℝ) +
        hintLenC₃ KCR K * (P.lam : ℝ) * P.lgn ^ hintLenQ KCR := by
  have hL1 : 1 ≤ P.lgn := one_le_lg hn
  have hL0 : 0 < P.lgn := by linarith
  set c : ℕ := ⌈(X : ℝ) / P.lgn ^ 3⌉₊ with hc
  have hrows : P.rows X Y = max Y c := by rw [hc]; rfl
  have hcY : Y < c := by
    rcases lt_or_ge Y c with h | h
    · exact h
    · exfalso
      rw [hrows, max_eq_left h] at hdir
      exact hdir rfl
  have hmc : P.rows X Y = c := by rw [hrows, max_eq_right (le_of_lt hcY)]
  have hc1 : 1 ≤ c := by omega
  have hm1 : 1 ≤ P.rows X Y := by rw [hmc]; exact hc1
  have hm : (P.rows X Y : ℝ) ≤ (X : ℝ) / P.lgn ^ 3 + 1 := by
    rw [hmc]
    have h0 : (0 : ℝ) ≤ (X : ℝ) / P.lgn ^ 3 := by positivity
    have h := Nat.ceil_lt_add_one h0
    linarith only [h]
  have hell : (P.ell N X Y : ℝ) ≤ P.lgn ^ 3 + (hintLenE KCR : ℝ) * P.lgn ^ 2 :=
    ell_le_four hA hC hn hN1 hNn hXN hYN hm1
  set E : ℝ := (hintLenE KCR : ℝ) with hEdef
  have hE0 : (0 : ℝ) ≤ E := by positivity
  have hell' : (P.ell N X Y : ℝ) ≤ P.lgn ^ 3 + E * P.lgn ^ 2 := hell
  have hmul : (P.rows X Y : ℝ) * (P.ell N X Y : ℝ)
      ≤ ((X : ℝ) / P.lgn ^ 3 + 1) * (P.lgn ^ 3 + E * P.lgn ^ 2) := by
    have h1 : (0 : ℝ) ≤ (P.ell N X Y : ℝ) := by positivity
    have h2 : (0 : ℝ) ≤ (X : ℝ) / P.lgn ^ 3 + 1 := by positivity
    exact mul_le_mul hm hell' h1 h2
  have hC1 : 2 * E ≤ hintLenC₁ KCR K := two_E_le_C₁ hK
  have hC3 : E + 1 ≤ hintLenC₃ KCR K := E_add_one_le_C₃ KCR hK
  have hLq3 : P.lgn ^ 3 ≤ P.lgn ^ hintLenQ KCR :=
    pow_three_le_pow_q hL1 (three_le_hintLenQ KCR)
  have hLq2 : P.lgn ^ 2 ≤ P.lgn ^ hintLenQ KCR :=
    pow_two_le_pow_q hL1 (by have := three_le_hintLenQ KCR; omega)
  have hX0 : (0 : ℝ) ≤ (X : ℝ) := by positivity
  have hC30 : (0 : ℝ) ≤ hintLenC₃ KCR K := hintLenC₃_nonneg KCR hK
  have hlam1 : (1 : ℝ) ≤ (P.lam : ℝ) := by exact_mod_cast hlam
  have hLqnn : (0 : ℝ) ≤ P.lgn ^ hintLenQ KCR := by positivity
  have hexp : ((X : ℝ) / P.lgn ^ 3 + 1) * (P.lgn ^ 3 + E * P.lgn ^ 2)
      = (X : ℝ) + (X : ℝ) * E / P.lgn + (P.lgn ^ 3 + E * P.lgn ^ 2) := by
    field_simp
  have ha : (X : ℝ) * E / P.lgn ≤ (X : ℝ) * (hintLenC₁ KCR K / (2 * P.lgn)) := by
    have hstep1 : (X : ℝ) * E / P.lgn ≤ (X : ℝ) * (hintLenC₁ KCR K / 2) / P.lgn := by
      refine div_le_div_of_nonneg_right ?_ (le_of_lt hL0)
      have h2 : (X : ℝ) * (2 * E) ≤ (X : ℝ) * hintLenC₁ KCR K :=
        mul_le_mul_of_nonneg_left hC1 hX0
      nlinarith only [h2]
    have hstep2 : (X : ℝ) * (hintLenC₁ KCR K / 2) / P.lgn
        = (X : ℝ) * (hintLenC₁ KCR K / (2 * P.lgn)) := by
      field_simp
    linarith only [hstep1, hstep2]
  have hb : P.lgn ^ 3 + E * P.lgn ^ 2
      ≤ hintLenC₃ KCR K * (P.lam : ℝ) * P.lgn ^ hintLenQ KCR := by
    have h2 : E * P.lgn ^ 2 ≤ E * P.lgn ^ hintLenQ KCR :=
      mul_le_mul_of_nonneg_left hLq2 hE0
    have h3 : P.lgn ^ 3 + E * P.lgn ^ 2 ≤ (E + 1) * P.lgn ^ hintLenQ KCR := by
      nlinarith only [hLq3, h2, hLqnn]
    have h4 : (E + 1) * P.lgn ^ hintLenQ KCR
        ≤ hintLenC₃ KCR K * P.lgn ^ hintLenQ KCR :=
      mul_le_mul_of_nonneg_right hC3 hLqnn
    have h5 : hintLenC₃ KCR K * P.lgn ^ hintLenQ KCR
        ≤ hintLenC₃ KCR K * (P.lam : ℝ) * P.lgn ^ hintLenQ KCR := by
      have h0 : (0 : ℝ) ≤ hintLenC₃ KCR K * P.lgn ^ hintLenQ KCR := mul_nonneg hC30 hLqnn
      calc hintLenC₃ KCR K * P.lgn ^ hintLenQ KCR
          = hintLenC₃ KCR K * P.lgn ^ hintLenQ KCR * 1 := (mul_one _).symm
        _ ≤ hintLenC₃ KCR K * P.lgn ^ hintLenQ KCR * (P.lam : ℝ) :=
            mul_le_mul_of_nonneg_left hlam1 h0
        _ = hintLenC₃ KCR K * (P.lam : ℝ) * P.lgn ^ hintLenQ KCR := by ring
    linarith only [h3, h4, h5]
  have hfac : (1 + hintLenC₁ KCR K / (2 * P.lgn)) * (X : ℝ)
      = (X : ℝ) + (X : ℝ) * (hintLenC₁ KCR K / (2 * P.lgn)) := by ring
  linarith only [hmul, hexp, ha, hb, hfac]

/-! ### 9f. The per-rule cost estimates of `sec:hint-forest-cost`

The induction invariant of §5.4 is

  `Len(T) ≤ (1 + C₁/log n)·(X + α h_N(N,Y)) + C₂·N/log⁸n + C₃·λ·log^q n·nodeCount T`,

and the four rules of §5.2 are estimated separately.  Two accounting remarks, both as in the paper:

* the `N/log⁸n` bucket is spent at the node where it occurs — the residual `CR` sketch of a
  `direct`/`recursive` node has `t_v = min{N_v, ⌈2η(D_v+1)⌉}`, hence
  `Len_CR(v) = O(η log²n·D_v + log²n)`, and `η log²n = log^{-(A-2)}n ≤ log⁻⁸n` with `A ≥ 100`.  The
  `+1` is harmless because the small-instance rule has failed, so `N_v ≥ D_v > log^{6+2A}n`, i.e.
  `log²n ≤ N_v/log⁸n`.  No depth factor is needed;
* the residual `C₂·∑_s N_s/log⁸n` of the children (`N_s = Y_s`'s universe, which is `Y` at a
  `recursive` node, so the sum is `ℓ_v·Y`) is paid by the relative overhead: `Y ≤ h_N(N,Y)` and
  `ℓ_v = O(log³n)` make it `≤ C₁/(2log n)·α h_N(N,Y)`, exactly the slack that Lemma 5.9's density
  contraction `∑_s h_N(Y_s) ≤ h_N(N,Y)/4` leaves over. -/

/-- The row bound of Proposition 2.3 with `KCR` replaced by `max KCR 0`: free, since a negative `KCR`
forces every residual sketch to vanish. -/
lemma rows_bound_nonneg {KCR : ℝ} {CR : CRFamily}
    (hrows : ∀ N' t : ℕ, t ≤ N' →
      (CR.rows N' t : ℝ) ≤ KCR * ((t : ℝ) * lg ((N' : ℝ) + 2) ^ 2)) :
    ∀ N' t : ℕ, t ≤ N' →
      (CR.rows N' t : ℝ) ≤ max KCR 0 * ((t : ℝ) * lg ((N' : ℝ) + 2) ^ 2) := by
  intro N' t ht
  have h := hrows N' t ht
  have hA : (0 : ℝ) ≤ (t : ℝ) * lg ((N' : ℝ) + 2) ^ 2 := by positivity
  rcases lt_or_ge KCR 0 with h0 | h0
  · have hneg : KCR * ((t : ℝ) * lg ((N' : ℝ) + 2) ^ 2) ≤ 0 := by nlinarith only [h0, hA]
    have hz : (CR.rows N' t : ℝ) = 0 := le_antisymm (le_trans h hneg) (by positivity)
    rw [hz, max_eq_right (le_of_lt h0)]
    simp
  · rw [max_eq_left h0]; exact h

/-- `(L+1)² ≤ 4L²` for `L ≥ 1`. -/
lemma sq_add_one_le_four_sq {L : ℝ} (hL : 1 ≤ L) : (L + 1) ^ 2 ≤ 4 * L ^ 2 := by
  nlinarith only [hL, sq_nonneg (L - 1)]

/-- `log(N+2) ≤ log n + 1` for `N ≤ n` (a node's universe never exceeds `n`). -/
lemma lg_add_two_le_of_le {N n : ℕ} (hNn : N ≤ n) (hn : 2 ≤ n) :
    lg ((N : ℝ) + 2) ≤ lg (n : ℝ) + 1 := by
  have hpos : (0 : ℝ) < (N : ℝ) + 2 := by positivity
  have hmono : lg ((N : ℝ) + 2) ≤ lg ((n : ℝ) + 2) := by
    refine Real.logb_le_logb_of_le (by norm_num) hpos ?_
    have h2 : (N : ℝ) ≤ (n : ℝ) := by exact_mod_cast hNn
    linarith
  have h3 := lg_add_two_le hn
  linarith only [hmono, h3]

/-- `log²(N+2) ≤ 4log²n` for `N ≤ n`, `n ≥ 2`. -/
lemma lg_add_two_sq_le {N n : ℕ} (hNn : N ≤ n) (hn : 2 ≤ n) :
    lg ((N : ℝ) + 2) ^ 2 ≤ 4 * lg (n : ℝ) ^ 2 := by
  have h1 : lg ((N : ℝ) + 2) ≤ lg (n : ℝ) + 1 := lg_add_two_le_of_le hNn hn
  have h0 : (0 : ℝ) ≤ lg ((N : ℝ) + 2) :=
    lg_nonneg_of_one_le (by linarith [Nat.cast_nonneg (α := ℝ) N])
  have hL1 : (1 : ℝ) ≤ lg (n : ℝ) := one_le_lg hn
  have h3 : lg ((N : ℝ) + 2) ^ 2 ≤ (lg (n : ℝ) + 1) ^ 2 := pow_le_pow_left₀ h0 h1 2
  have h4 : (lg (n : ℝ) + 1) ^ 2 ≤ 4 * lg (n : ℝ) ^ 2 := sq_add_one_le_four_sq hL1
  linarith only [h3, h4]

/-- `L^a·L^b·L^c·L^d ≤ L^q` when `a+b+c+d ≤ q` and `L ≥ 1`: the exponent bookkeeping of §5.4. -/
lemma pow_mul_pow_four {L : ℝ} (hL : 1 ≤ L) {a b c d q : ℕ} (h : a + b + c + d ≤ q) :
    L ^ a * L ^ b * L ^ c * L ^ d ≤ L ^ q := by
  have h1 : L ^ a * L ^ b * L ^ c * L ^ d = L ^ (a + b + c + d) := by
    rw [← pow_add, ← pow_add, ← pow_add]
  have hsplit : L ^ q = L ^ (a + b + c + d) * L ^ (q - (a + b + c + d)) := by
    rw [← pow_add]
    congr 1
    omega
  rw [h1, hsplit]
  have h2 : (1 : ℝ) ≤ L ^ (q - (a + b + c + d)) := one_le_pow₀ hL
  have h3 : (0 : ℝ) ≤ L ^ (a + b + c + d) := pow_nonneg (by linarith only [hL]) _
  nlinarith only [h2, h3]

/-- `z ≤ h_N(N,z)` for `z ≤ N`, `z = 0` included (the paper's `h_N(Y) ≥ Y`). -/
lemma nat_le_hN {N z : ℕ} (hzN : z ≤ N) : (z : ℝ) ≤ hN N z := by
  rcases Nat.eq_zero_or_pos z with h | h
  · rw [h]; simp
  · exact le_hN (by exact_mod_cast h) (by exact_mod_cast hzN)

/-- `0 ≤ h_N(N,z)` for `z ≤ N`. -/
lemma hN_nonneg_nat {N z : ℕ} (hzN : z ≤ N) : (0 : ℝ) ≤ hN N z :=
  le_trans (by positivity) (nat_le_hN hzN)

/-- `η log²n ≤ log⁻⁸n` for `A ≥ 100`: the residual `CR` sketches are `O(N/log⁸n)`, as in the paper
(`t_v = O(ηD_v)` gives `Len_CR(v) = O(ηD_v log²n) = O(D_v/log^{A-2}n)`). -/
lemma eta_lgn_sq_le {KCR : ℝ} {P : HintParams} (hA : P.A = hintLenA KCR) (hn : 2 ≤ P.n) :
    P.eta * P.lgn ^ 2 ≤ (P.lgn ^ 8)⁻¹ := by
  have hL1 : (1 : ℝ) ≤ P.lgn := one_le_lg hn
  have hL0 : (0 : ℝ) < P.lgn := by linarith only [hL1]
  have hA100 : 100 ≤ P.A := by rw [hA]; exact le_max_right _ _
  have hkey : P.eta * P.lgn ^ 2 = (P.lgn ^ (P.A - 2))⁻¹ := by
    have hsplit : P.lgn ^ P.A = P.lgn ^ (P.A - 2) * P.lgn ^ 2 := by
      rw [← pow_add]
      congr 1
      omega
    rw [HintParams.eta, hsplit, mul_inv]
    have h2 : (P.lgn ^ 2) ≠ 0 := ne_of_gt (pow_pos hL0 2)
    field_simp
  rw [hkey]
  have h8 : (0 : ℝ) < P.lgn ^ 8 := pow_pos hL0 8
  have hexp : (0 : ℝ) < P.lgn ^ (P.A - 2) := pow_pos hL0 _
  refine (inv_le_inv₀ hexp h8).mpr ?_
  have hsplit2 : P.lgn ^ (P.A - 2) = P.lgn ^ 8 * P.lgn ^ (P.A - 2 - 8) := by
    rw [← pow_add]
    congr 1
    omega
  rw [hsplit2]
  have h1 : (1 : ℝ) ≤ P.lgn ^ (P.A - 2 - 8) := one_le_pow₀ hL1
  have h2 : (0 : ℝ) ≤ P.lgn ^ 8 := pow_nonneg (le_of_lt hL0) 8
  nlinarith only [h1, h2]

/-- `4·max KCR 0 ≤ C₂` (the `cheap` leaf's residual rows). -/
theorem four_max_le_C₂ {KCR : ℝ} {K : ℝ} (hK0 : 0 < K) :
    4 * max KCR 0 ≤ hintLenC₂ KCR K := by
  have hmax0 : (0 : ℝ) ≤ max KCR 0 := le_max_right _ _
  have h1 : (0 : ℝ) ≤ 64 * (K + 1) * ((hintLenC KCR : ℝ) + 1) :=
    mul_nonneg (mul_nonneg (by norm_num) (by linarith)) (by positivity)
  unfold hintLenC₂
  linarith only [hmax0, h1]

/-- `20·max KCR 0 ≤ C₂` (the `direct`/`recursive` residual `8ηDlog²n + 8ηlog²n + 4log²n`). -/
theorem twenty_max_le_C₂ {KCR : ℝ} {K : ℝ} (hK0 : 0 < K) :
    20 * max KCR 0 ≤ hintLenC₂ KCR K := by
  have hmax0 : (0 : ℝ) ≤ max KCR 0 := le_max_right _ _
  have h1 : (0 : ℝ) ≤ 64 * (K + 1) * ((hintLenC KCR : ℝ) + 1) :=
    mul_nonneg (mul_nonneg (by norm_num) (by linarith)) (by positivity)
  unfold hintLenC₂
  linarith only [hmax0, h1]

/-- `32·max KCR 0·(C+1)⁴ ≤ C₃` (the `small` leaf's `4KCR·C³λ_*log^{6+2A+2}n`). -/
theorem charge_C₄_le_C₃ {KCR : ℝ} {K : ℝ} (hK0 : 0 < K) (hKCR : KCR ≤ K) :
    32 * max KCR 0 * ((hintLenC KCR : ℝ) + 1) ^ 4 ≤ hintLenC₃ KCR K := by
  have hmax0 : (0 : ℝ) ≤ max KCR 0 := le_max_right _ _
  have hK0' : (0 : ℝ) ≤ K := le_of_lt hK0
  have hmaxK : max KCR 0 ≤ K + 1 := by
    have h1 : max KCR 0 ≤ K := max_le hKCR hK0'
    linarith only [h1]
  have hKp : (0 : ℝ) ≤ K + 1 := by linarith only [hK0]
  have hC0 : (0 : ℝ) ≤ ((hintLenC KCR : ℝ) + 1) ^ 4 := by positivity
  have hA1 : (1 : ℝ) ≤ (hintLenA KCR : ℝ) + 1 := by
    have h : (0 : ℝ) ≤ (hintLenA KCR : ℝ) := by positivity
    linarith only [h]
  have hstep1 : (32 : ℝ) * max KCR 0 ≤ 32 * (K + 1) := by nlinarith only [hmaxK, hmax0]
  have h4 : (K + 1) ≤ (K + 1) ^ 8 := by
    have h5 : (1 : ℝ) ≤ K + 1 := by linarith only [hK0]
    have h6 : (1 : ℝ) ≤ (K + 1) ^ 7 := one_le_pow₀ h5
    have h8 : (K + 1) ^ 8 = (K + 1) ^ 7 * (K + 1) := by ring
    rw [h8]
    calc (K + 1) = 1 * (K + 1) := (one_mul _).symm
      _ ≤ (K + 1) ^ 7 * (K + 1) := mul_le_mul_of_nonneg_right h6 hKp
  have hstep2 : (32 : ℝ) * (K + 1) ≤ (2 : ℝ) ^ 30 * (K + 1) ^ 8 := by
    have h3 : (32 : ℝ) ≤ (2 : ℝ) ^ 30 := by norm_num
    have h5 : (0 : ℝ) ≤ (K + 1) := hKp
    have h6 : (0 : ℝ) ≤ (2 : ℝ) ^ 30 := by norm_num
    calc (32 : ℝ) * (K + 1) ≤ (2 : ℝ) ^ 30 * (K + 1) :=
          mul_le_mul_of_nonneg_right h3 h5
      _ ≤ (2 : ℝ) ^ 30 * (K + 1) ^ 8 := mul_le_mul_of_nonneg_left h4 h6
  have hstep3 : (32 : ℝ) * (K + 1)
      ≤ (2 : ℝ) ^ 30 * (K + 1) ^ 8 * ((hintLenA KCR : ℝ) + 1) := by
    have h6 : (0 : ℝ) ≤ (2 : ℝ) ^ 30 * (K + 1) ^ 8 := by positivity
    calc (32 : ℝ) * (K + 1) ≤ (2 : ℝ) ^ 30 * (K + 1) ^ 8 := hstep2
      _ = (2 : ℝ) ^ 30 * (K + 1) ^ 8 * 1 := (mul_one _).symm
      _ ≤ (2 : ℝ) ^ 30 * (K + 1) ^ 8 * ((hintLenA KCR : ℝ) + 1) :=
          mul_le_mul_of_nonneg_left hA1 h6
  have hstep4 : (32 : ℝ) * max KCR 0 * ((hintLenC KCR : ℝ) + 1) ^ 4
      ≤ (2 : ℝ) ^ 30 * (K + 1) ^ 8 * ((hintLenC KCR : ℝ) + 1) ^ 4 *
          ((hintLenA KCR : ℝ) + 1) := by
    have h7 : (32 : ℝ) * max KCR 0
        ≤ (2 : ℝ) ^ 30 * (K + 1) ^ 8 * ((hintLenA KCR : ℝ) + 1) := le_trans hstep1 hstep3
    calc (32 : ℝ) * max KCR 0 * ((hintLenC KCR : ℝ) + 1) ^ 4
        ≤ ((2 : ℝ) ^ 30 * (K + 1) ^ 8 * ((hintLenA KCR : ℝ) + 1)) *
            ((hintLenC KCR : ℝ) + 1) ^ 4 := mul_le_mul_of_nonneg_right h7 hC0
      _ = (2 : ℝ) ^ 30 * (K + 1) ^ 8 * ((hintLenC KCR : ℝ) + 1) ^ 4 *
            ((hintLenA KCR : ℝ) + 1) := by ring
  unfold hintLenC₃
  linarith only [hstep4]

/-- `λ_* = λ + C⌈log log(n+2)⌉ + C ≤ 8Cλ log n`: the paper's `λ_* = O(Cλ log n)`. -/
lemma lamStar_le {P : HintParams} (hn : 2 ≤ P.n) (hlam : 1 ≤ P.lam) (hC : 1 ≤ P.C) :
    (P.lamStar : ℝ) ≤ 8 * (P.C : ℝ) * (P.lam : ℝ) * P.lgn := by
  have hL1 : (1 : ℝ) ≤ P.lgn := one_le_lg hn
  have hL0 : (0 : ℝ) ≤ P.lgn := le_of_lt (by linarith only [hL1] : (0 : ℝ) < P.lgn)
  have hC1 : (1 : ℝ) ≤ (P.C : ℝ) := by exact_mod_cast hC
  have hlam1 : (1 : ℝ) ≤ (P.lam : ℝ) := by exact_mod_cast hlam
  have hz1 : (1 : ℝ) ≤ lg ((P.n : ℝ) + 2) := by
    have h2 : ((P.n + 2 : ℕ) : ℝ) = (P.n : ℝ) + 2 := by push_cast; ring
    rw [← h2]
    exact one_le_lg (by omega : 2 ≤ P.n + 2)
  have hzle : lg ((P.n : ℝ) + 2) ≤ P.lgn + 1 := lg_add_two_le hn
  have hylog : lg (lg ((P.n : ℝ) + 2)) ≤ 2 * (P.lgn + 1) := by
    have h := lg_le_two_mul (lg ((P.n : ℝ) + 2)) hz1
    linarith only [h, hzle]
  have hy0 : (0 : ℝ) ≤ lg (lg ((P.n : ℝ) + 2)) := lg_nonneg_of_one_le hz1
  have hceil : (⌈lg (lg ((P.n : ℝ) + 2))⌉₊ : ℝ) ≤ 2 * P.lgn + 3 := by
    have hlt := Nat.ceil_lt_add_one hy0
    linarith only [hlt, hylog]
  have hCL : (1 : ℝ) ≤ (P.C : ℝ) * P.lgn := by nlinarith only [hC1, hL1]
  have hlamL : (1 : ℝ) ≤ (P.lam : ℝ) * P.lgn := by nlinarith only [hlam1, hL1]
  have h1 : (P.lam : ℝ) ≤ (P.C : ℝ) * (P.lam : ℝ) * P.lgn := by
    have h0 : (0 : ℝ) ≤ (P.lam : ℝ) := by linarith only [hlam1]
    have h5 := mul_le_mul_of_nonneg_left hCL h0
    nlinarith only [h5]
  have h2 : (P.C : ℝ) * (2 * P.lgn) ≤ 2 * ((P.C : ℝ) * (P.lam : ℝ) * P.lgn) := by
    have h0 : (0 : ℝ) ≤ (P.C : ℝ) * (2 * P.lgn) := by nlinarith only [hC1, hL0]
    have h5 := mul_le_mul_of_nonneg_left hlam1 h0
    nlinarith only [h5]
  have h3 : (P.C : ℝ) * 3 + (P.C : ℝ) ≤ 4 * ((P.C : ℝ) * (P.lam : ℝ) * P.lgn) := by
    have h0 : (0 : ℝ) ≤ 4 * (P.C : ℝ) := by linarith only [hC1]
    have h5 := mul_le_mul_of_nonneg_left hlamL h0
    nlinarith only [h5]
  have h4 : (P.lamStar : ℝ) =
      (P.lam : ℝ) + (P.C : ℝ) * (⌈lg (lg ((P.n : ℝ) + 2))⌉₊ : ℝ) + (P.C : ℝ) := by
    unfold HintParams.lamStar
    push_cast
    ring
  have hC0 : (0 : ℝ) ≤ (P.C : ℝ) := by linarith only [hC1]
  have hk : (P.C : ℝ) * (⌈lg (lg ((P.n : ℝ) + 2))⌉₊ : ℝ) ≤ (P.C : ℝ) * (2 * P.lgn + 3) :=
    mul_le_mul_of_nonneg_left hceil hC0
  have hpos : (0 : ℝ) ≤ (P.C : ℝ) * (P.lam : ℝ) * P.lgn :=
    mul_nonneg (mul_nonneg hC0 (by linarith only [hlam1])) hL0
  rw [h4]
  linarith only [h1, h2, h3, hk, hpos]

/-- `ℓ_v ≤ (E+1)log³n` (the sharp `ℓ_v` bound of equation (16), in the form the recursion uses). -/
lemma ell_le_cubic {KCR : ℝ} {P : HintParams}
    (hA : P.A = hintLenA KCR) (hC : P.C = hintLenC KCR) (hn : 2 ≤ P.n) {N X Y : ℕ}
    (hN1 : 1 ≤ N) (hNn : N ≤ P.n) (hXN : X ≤ N) (hYN : Y ≤ N) (hm1 : 1 ≤ P.rows X Y) :
    (P.ell N X Y : ℝ) ≤ ((hintLenE KCR : ℝ) + 1) * P.lgn ^ 3 := by
  have hL1 : (1 : ℝ) ≤ P.lgn := one_le_lg hn
  have hL0 : (0 : ℝ) ≤ P.lgn := le_of_lt (by linarith only [hL1] : (0 : ℝ) < P.lgn)
  have hell := ell_le_four hA hC hn hN1 hNn hXN hYN hm1
  have hE0 : (0 : ℝ) ≤ (hintLenE KCR : ℝ) := by positivity
  have hL2 : P.lgn ^ 2 ≤ P.lgn ^ 3 := by
    have h0 : (0 : ℝ) ≤ P.lgn ^ 2 := pow_nonneg hL0 2
    nlinarith only [hL1, h0]
  have hE1 : (0 : ℝ) ≤ ((hintLenE KCR : ℝ) + 1) * P.lgn ^ 3 :=
    mul_nonneg (by linarith only [hE0]) (pow_nonneg hL0 3)
  nlinarith only [hell, hE0, hL2, hL1, hE1]

/-- The paper's step 2 (`cheap`): `Len_CR(v) = CR.rows N_v D_v ≤ C₂·N_v/log⁸n`, because
`D_v ≤ N_v/log^{10}n` and `log(N_v+2)² ≤ 4log²n`. -/
lemma len_cheap_le {KCR K : ℝ} {P : HintParams} {CR : CRFamily} {N X Y : ℕ}
    (hK0 : 0 < K) (hn : 2 ≤ P.n) (hNn : N ≤ P.n) (hYN : Y ≤ N)
    (hc : P.rule N X Y = .cheap)
    (hrows : ∀ N' t : ℕ, t ≤ N' →
      (CR.rows N' t : ℝ) ≤ max KCR 0 * ((t : ℝ) * lg ((N' : ℝ) + 2) ^ 2)) :
    (synLen CR (.cr N (HintParams.D N X Y)) : ℝ) ≤
      (1 + hintLenC₁ KCR K / P.lgn) * ((X : ℝ) + hintLenAlpha KCR K * hN N Y) +
        hintLenC₂ KCR K * ((N : ℝ) / P.lgn ^ 8) +
          hintLenC₃ KCR K * (P.lam : ℝ) * P.lgn ^ hintLenQ KCR := by
  have hL1 : (1 : ℝ) ≤ P.lgn := one_le_lg hn
  have hL0 : (0 : ℝ) < P.lgn := by linarith only [hL1]
  have hLn : (0 : ℝ) ≤ P.lgn := le_of_lt hL0
  have hL8 : (0 : ℝ) < P.lgn ^ 8 := pow_pos hL0 8
  have hL10 : (0 : ℝ) < P.lgn ^ 10 := pow_pos hL0 10
  have hDN : HintParams.D N X Y ≤ N := min_le_left _ _
  have h1 : (CR.rows N (HintParams.D N X Y) : ℝ) ≤
      max KCR 0 * ((HintParams.D N X Y : ℝ) * lg ((N : ℝ) + 2) ^ 2) := hrows N _ hDN
  have hspec : (HintParams.D N X Y : ℝ) ≤ (N : ℝ) * (P.lgn ^ 10)⁻¹ := by
    have h := rule_cheap_spec hc
    rw [div_eq_mul_inv] at h
    exact h
  have hlg : lg ((N : ℝ) + 2) ^ 2 ≤ 4 * P.lgn ^ 2 := lg_add_two_sq_le hNn hn
  have hA2 : (0 : ℝ) ≤ (P.lgn ^ 10)⁻¹ := (inv_pos.mpr (pow_pos hL0 10)).le
  have hmul : (HintParams.D N X Y : ℝ) * lg ((N : ℝ) + 2) ^ 2 ≤
      ((N : ℝ) * (P.lgn ^ 10)⁻¹) * (4 * P.lgn ^ 2) := by
    calc (HintParams.D N X Y : ℝ) * lg ((N : ℝ) + 2) ^ 2
        ≤ ((N : ℝ) * (P.lgn ^ 10)⁻¹) * lg ((N : ℝ) + 2) ^ 2 :=
          mul_le_mul_of_nonneg_right hspec (by positivity)
      _ ≤ ((N : ℝ) * (P.lgn ^ 10)⁻¹) * (4 * P.lgn ^ 2) :=
          mul_le_mul_of_nonneg_left hlg (mul_nonneg (by positivity) hA2)
  have hkey : ((N : ℝ) * (P.lgn ^ 10)⁻¹) * (4 * P.lgn ^ 2)
      = 4 * ((N : ℝ) * (P.lgn ^ 8)⁻¹) := by
    have hpow : P.lgn ^ 10 = P.lgn ^ 8 * P.lgn ^ 2 := by ring
    have h2 : (P.lgn ^ 2) ≠ 0 := ne_of_gt (pow_pos hL0 2)
    calc ((N : ℝ) * (P.lgn ^ 10)⁻¹) * (4 * P.lgn ^ 2)
        = ((N : ℝ) * (P.lgn ^ 8 * P.lgn ^ 2)⁻¹) * (4 * P.lgn ^ 2) := by rw [hpow]
      _ = (N * ((P.lgn ^ 8)⁻¹ * (P.lgn ^ 2)⁻¹)) * (4 * P.lgn ^ 2) := by rw [mul_inv]
      _ = 4 * (N * ((P.lgn ^ 8)⁻¹ * (P.lgn ^ 2)⁻¹ * P.lgn ^ 2)) := by ring
      _ = 4 * (N * (P.lgn ^ 8)⁻¹) := by
            rw [mul_assoc ((P.lgn ^ 8)⁻¹) ((P.lgn ^ 2)⁻¹) (P.lgn ^ 2),
              inv_mul_cancel₀ h2, mul_one]
  have hK0' : (0 : ℝ) ≤ max KCR 0 := le_max_right _ _
  have hNinv0 : (0 : ℝ) ≤ (N : ℝ) * (P.lgn ^ 8)⁻¹ :=
    mul_nonneg (by positivity) (inv_nonneg.mpr (pow_nonneg hLn 8))
  have h4 : 4 * max KCR 0 ≤ hintLenC₂ KCR K := four_max_le_C₂ hK0
  have hfin : (CR.rows N (HintParams.D N X Y) : ℝ) ≤
      hintLenC₂ KCR K * ((N : ℝ) * (P.lgn ^ 8)⁻¹) := by
    have h2 : max KCR 0 * ((HintParams.D N X Y : ℝ) * lg ((N : ℝ) + 2) ^ 2)
        ≤ max KCR 0 * (4 * ((N : ℝ) * (P.lgn ^ 8)⁻¹)) := by
      rw [← hkey]
      exact mul_le_mul_of_nonneg_left hmul hK0'
    have h3 : max KCR 0 * (4 * ((N : ℝ) * (P.lgn ^ 8)⁻¹))
        ≤ hintLenC₂ KCR K * ((N : ℝ) * (P.lgn ^ 8)⁻¹) := by
      have h5 : (4 : ℝ) * max KCR 0 * ((N : ℝ) * (P.lgn ^ 8)⁻¹)
          ≤ hintLenC₂ KCR K * ((N : ℝ) * (P.lgn ^ 8)⁻¹) :=
        mul_le_mul_of_nonneg_right h4 hNinv0
      linarith only [h5]
    linarith only [h1, h2, h3]
  have hcharge : (0 : ℝ) ≤ (X : ℝ) + hintLenAlpha KCR K * hN N Y := by
    have h2 : (0 : ℝ) ≤ hN N Y := hN_nonneg_nat hYN
    have h3 : (0 : ℝ) ≤ hintLenAlpha KCR K := le_of_lt (hintLenAlpha_pos KCR hK0)
    have h4 : (0 : ℝ) ≤ (X : ℝ) := by positivity
    nlinarith only [h2, h3, h4]
  have hC1 : (0 : ℝ) ≤ 1 + hintLenC₁ KCR K / P.lgn := by
    have h2 : (0 : ℝ) ≤ hintLenC₁ KCR K / P.lgn :=
      div_nonneg (hintLenC₁_nonneg hK0) hLn
    linarith only [h2]
  have hC3 : (0 : ℝ) ≤ hintLenC₃ KCR K * (P.lam : ℝ) * P.lgn ^ hintLenQ KCR :=
    mul_nonneg (mul_nonneg (hintLenC₃_nonneg KCR hK0) (by positivity))
      (pow_nonneg hLn _)
  have hprod1 : (0 : ℝ) ≤
      (1 + hintLenC₁ KCR K / P.lgn) * ((X : ℝ) + hintLenAlpha KCR K * hN N Y) :=
    mul_nonneg hC1 hcharge
  have hNdiv : hintLenC₂ KCR K * ((N : ℝ) / P.lgn ^ 8)
      = hintLenC₂ KCR K * ((N : ℝ) * (P.lgn ^ 8)⁻¹) := by rw [div_eq_mul_inv]
  have hlen : (synLen CR (.cr N (HintParams.D N X Y)) : ℝ) =
      (CR.rows N (HintParams.D N X Y) : ℝ) := rfl
  rw [hlen, hNdiv]
  linarith only [hfin, hprod1, hC3]

/-- The paper's step 3 (`small`): `D_v ≤ C³λ_*log⁶n/η²` gives
`Len_CR(v) ≤ KCR·C³λ_*log^{6+2A}n·log²n ≤ C₃λlog^q n`. -/
lemma len_small_le {KCR K : ℝ} {P : HintParams} {CR : CRFamily} {N X Y : ℕ}
    (hA : P.A = hintLenA KCR) (hC : P.C = hintLenC KCR) (hK0 : 0 < K) (hKCR : KCR ≤ K)
    (hn : 2 ≤ P.n) (hlam : 1 ≤ P.lam) (hNn : N ≤ P.n) (hYN : Y ≤ N)
    (hs : P.rule N X Y = .small)
    (hrows : ∀ N' t : ℕ, t ≤ N' →
      (CR.rows N' t : ℝ) ≤ max KCR 0 * ((t : ℝ) * lg ((N' : ℝ) + 2) ^ 2)) :
    (synLen CR (.cr N (HintParams.D N X Y)) : ℝ) ≤
      (1 + hintLenC₁ KCR K / P.lgn) * ((X : ℝ) + hintLenAlpha KCR K * hN N Y) +
        hintLenC₂ KCR K * ((N : ℝ) / P.lgn ^ 8) +
          hintLenC₃ KCR K * (P.lam : ℝ) * P.lgn ^ hintLenQ KCR := by
  have hL1 : (1 : ℝ) ≤ P.lgn := one_le_lg hn
  have hL0 : (0 : ℝ) < P.lgn := by linarith only [hL1]
  have hLn : (0 : ℝ) ≤ P.lgn := le_of_lt hL0
  have hCn : 1 ≤ P.C := by rw [hC]; exact le_trans (by norm_num) (forty_le_hintLenC KCR)
  have hDN : HintParams.D N X Y ≤ N := min_le_left _ _
  have h1 : (CR.rows N (HintParams.D N X Y) : ℝ) ≤
      max KCR 0 * ((HintParams.D N X Y : ℝ) * lg ((N : ℝ) + 2) ^ 2) := hrows N _ hDN
  have hD : (HintParams.D N X Y : ℝ) ≤ (P.C : ℝ) ^ 3 * (P.lamStar : ℝ) * P.lgn ^ (6 + 2 * P.A) := by
    have h := rule_small_spec hs
    rw [div_eq_mul_inv, inv_eta_sq] at h
    have hpow : P.lgn ^ (6 + 2 * P.A) = P.lgn ^ 6 * P.lgn ^ (2 * P.A) := by rw [pow_add]
    calc (HintParams.D N X Y : ℝ)
        ≤ (P.C : ℝ) ^ 3 * (P.lamStar : ℝ) * P.lgn ^ 6 * P.lgn ^ (2 * P.A) := h
      _ = (P.C : ℝ) ^ 3 * (P.lamStar : ℝ) * (P.lgn ^ 6 * P.lgn ^ (2 * P.A)) := by ring
      _ = (P.C : ℝ) ^ 3 * (P.lamStar : ℝ) * P.lgn ^ (6 + 2 * P.A) := by rw [hpow]
  have hlg : lg ((N : ℝ) + 2) ^ 2 ≤ 4 * P.lgn ^ 2 := lg_add_two_sq_le hNn hn
  have hls : (P.lamStar : ℝ) ≤ 8 * (P.C : ℝ) * (P.lam : ℝ) * P.lgn := lamStar_le hn hlam hCn
  have hD0 : (0 : ℝ) ≤ (HintParams.D N X Y : ℝ) := by positivity
  have hlg0 : (0 : ℝ) ≤ lg ((N : ℝ) + 2) ^ 2 := by positivity
  have hD' : (0 : ℝ) ≤ (P.C : ℝ) ^ 3 * (P.lamStar : ℝ) * P.lgn ^ (6 + 2 * P.A) :=
    mul_nonneg (mul_nonneg (by positivity) (by positivity)) (pow_nonneg hLn _)
  have hstep : (HintParams.D N X Y : ℝ) * lg ((N : ℝ) + 2) ^ 2 ≤
      ((P.C : ℝ) ^ 3 * (P.lamStar : ℝ) * P.lgn ^ (6 + 2 * P.A)) * (4 * P.lgn ^ 2) := by
    calc (HintParams.D N X Y : ℝ) * lg ((N : ℝ) + 2) ^ 2
        ≤ ((P.C : ℝ) ^ 3 * (P.lamStar : ℝ) * P.lgn ^ (6 + 2 * P.A)) * lg ((N : ℝ) + 2) ^ 2 :=
          mul_le_mul_of_nonneg_right hD hlg0
      _ ≤ ((P.C : ℝ) ^ 3 * (P.lamStar : ℝ) * P.lgn ^ (6 + 2 * P.A)) * (4 * P.lgn ^ 2) :=
          mul_le_mul_of_nonneg_left hlg hD'
  have hlam0 : (0 : ℝ) ≤ (P.C : ℝ) ^ 3 * P.lgn ^ (6 + 2 * P.A) :=
    mul_nonneg (by positivity) (pow_nonneg hLn _)
  have hstep2 : (P.C : ℝ) ^ 3 * (P.lamStar : ℝ) * P.lgn ^ (6 + 2 * P.A)
      ≤ (P.C : ℝ) ^ 3 * (8 * (P.C : ℝ) * (P.lam : ℝ) * P.lgn) * P.lgn ^ (6 + 2 * P.A) := by
    have h5 := mul_le_mul_of_nonneg_left hls hlam0
    calc (P.C : ℝ) ^ 3 * (P.lamStar : ℝ) * P.lgn ^ (6 + 2 * P.A)
        = ((P.C : ℝ) ^ 3 * P.lgn ^ (6 + 2 * P.A)) * (P.lamStar : ℝ) := by ring
      _ ≤ ((P.C : ℝ) ^ 3 * P.lgn ^ (6 + 2 * P.A)) *
            (8 * (P.C : ℝ) * (P.lam : ℝ) * P.lgn) := h5
      _ = (P.C : ℝ) ^ 3 * (8 * (P.C : ℝ) * (P.lam : ℝ) * P.lgn) * P.lgn ^ (6 + 2 * P.A) := by ring
  have hstep3 : (P.C : ℝ) ^ 3 * (8 * (P.C : ℝ) * (P.lam : ℝ) * P.lgn) * P.lgn ^ (6 + 2 * P.A)
      * (4 * P.lgn ^ 2)
      = 32 * ((P.C : ℝ) ^ 4) * (P.lam : ℝ) * (P.lgn ^ (6 + 2 * P.A) * P.lgn * P.lgn ^ 2) := by ring
  have hmain : (HintParams.D N X Y : ℝ) * lg ((N : ℝ) + 2) ^ 2
      ≤ 32 * ((P.C : ℝ) ^ 4) * (P.lam : ℝ) * (P.lgn ^ (6 + 2 * P.A) * P.lgn * P.lgn ^ 2) := by
    calc (HintParams.D N X Y : ℝ) * lg ((N : ℝ) + 2) ^ 2
        ≤ ((P.C : ℝ) ^ 3 * (P.lamStar : ℝ) * P.lgn ^ (6 + 2 * P.A)) * (4 * P.lgn ^ 2) := hstep
      _ ≤ ((P.C : ℝ) ^ 3 * (8 * (P.C : ℝ) * (P.lam : ℝ) * P.lgn) * P.lgn ^ (6 + 2 * P.A))
            * (4 * P.lgn ^ 2) := by
          refine mul_le_mul_of_nonneg_right hstep2 (mul_nonneg (by norm_num) (pow_nonneg hLn 2))
      _ = 32 * ((P.C : ℝ) ^ 4) * (P.lam : ℝ) *
            (P.lgn ^ (6 + 2 * P.A) * P.lgn * P.lgn ^ 2) := hstep3
  have hC4 : (P.C : ℝ) ^ 4 ≤ ((hintLenC KCR : ℝ) + 1) ^ 4 := by
    have hPC : (P.C : ℝ) = (hintLenC KCR : ℝ) := by rw [hC]
    have h0' : (0 : ℝ) ≤ (P.C : ℝ) := by positivity
    have h0 : (0 : ℝ) ≤ (hintLenC KCR : ℝ) := by positivity
    have h2 : (P.C : ℝ) ≤ (hintLenC KCR : ℝ) + 1 := by rw [hPC]; linarith only [h0]
    exact pow_le_pow_left₀ h0' h2 4
  have hpowq : P.lgn ^ (6 + 2 * P.A) * P.lgn * P.lgn ^ 2 ≤ P.lgn ^ hintLenQ KCR := by
    have hq : 6 + 2 * P.A + 1 + 2 + 0 ≤ hintLenQ KCR := by
      have h := hintLenQ_ge KCR
      omega
    have h := pow_mul_pow_four (L := P.lgn) hL1 (a := 6 + 2 * P.A) (b := 1) (c := 2) (d := 0)
      (q := hintLenQ KCR) hq
    simpa using h
  have hlam1 : (0 : ℝ) ≤ (P.lam : ℝ) := by positivity
  have hK0' : (0 : ℝ) ≤ max KCR 0 := le_max_right _ _
  have hfin : (CR.rows N (HintParams.D N X Y) : ℝ) ≤
      hintLenC₃ KCR K * (P.lam : ℝ) * P.lgn ^ hintLenQ KCR := by
    have h2 : max KCR 0 * ((HintParams.D N X Y : ℝ) * lg ((N : ℝ) + 2) ^ 2)
        ≤ max KCR 0 * (32 * ((P.C : ℝ) ^ 4) * (P.lam : ℝ) *
            (P.lgn ^ (6 + 2 * P.A) * P.lgn * P.lgn ^ 2)) :=
      mul_le_mul_of_nonneg_left hmain hK0'
    have h4 : 32 * ((P.C : ℝ) ^ 4) ≤ 32 * ((hintLenC KCR : ℝ) + 1) ^ 4 := by
      nlinarith only [hC4]
    have h5 : 32 * ((P.C : ℝ) ^ 4) * (P.lam : ℝ)
        ≤ 32 * ((hintLenC KCR : ℝ) + 1) ^ 4 * (P.lam : ℝ) :=
      mul_le_mul_of_nonneg_right h4 hlam1
    have h6 : 32 * ((P.C : ℝ) ^ 4) * (P.lam : ℝ) * (P.lgn ^ (6 + 2 * P.A) * P.lgn * P.lgn ^ 2)
        ≤ 32 * ((hintLenC KCR : ℝ) + 1) ^ 4 * (P.lam : ℝ) * P.lgn ^ hintLenQ KCR := by
      have h7 : (0 : ℝ) ≤ P.lgn ^ (6 + 2 * P.A) * P.lgn * P.lgn ^ 2 := by
        have h1 : (0 : ℝ) ≤ P.lgn ^ (6 + 2 * P.A) := pow_nonneg hLn _
        have h2 : (0 : ℝ) ≤ P.lgn := hLn
        have h3 : (0 : ℝ) ≤ P.lgn ^ 2 := pow_nonneg hLn 2
        exact mul_nonneg (mul_nonneg h1 h2) h3
      calc 32 * ((P.C : ℝ) ^ 4) * (P.lam : ℝ) * (P.lgn ^ (6 + 2 * P.A) * P.lgn * P.lgn ^ 2)
          ≤ 32 * ((hintLenC KCR : ℝ) + 1) ^ 4 * (P.lam : ℝ) *
              (P.lgn ^ (6 + 2 * P.A) * P.lgn * P.lgn ^ 2) :=
            mul_le_mul_of_nonneg_right h5 h7
        _ ≤ 32 * ((hintLenC KCR : ℝ) + 1) ^ 4 * (P.lam : ℝ) * P.lgn ^ hintLenQ KCR := by
            have h8 : (0 : ℝ) ≤ 32 * ((hintLenC KCR : ℝ) + 1) ^ 4 * (P.lam : ℝ) := by positivity
            exact mul_le_mul_of_nonneg_left hpowq h8
    have h3 : max KCR 0 * (32 * ((P.C : ℝ) ^ 4) * (P.lam : ℝ) *
          (P.lgn ^ (6 + 2 * P.A) * P.lgn * P.lgn ^ 2))
        ≤ max KCR 0 * (32 * ((hintLenC KCR : ℝ) + 1) ^ 4 * (P.lam : ℝ) * P.lgn ^ hintLenQ KCR) :=
      mul_le_mul_of_nonneg_left h6 hK0'
    have h9 : max KCR 0 * (32 * ((hintLenC KCR : ℝ) + 1) ^ 4 * (P.lam : ℝ) * P.lgn ^ hintLenQ KCR)
        ≤ hintLenC₃ KCR K * (P.lam : ℝ) * P.lgn ^ hintLenQ KCR := by
      have h32 : 32 * max KCR 0 * ((hintLenC KCR : ℝ) + 1) ^ 4 ≤ hintLenC₃ KCR K :=
        charge_C₄_le_C₃ hK0 hKCR
      have hLq0 : (0 : ℝ) ≤ P.lgn ^ hintLenQ KCR := pow_nonneg hLn _
      have h10 : (32 * max KCR 0 * ((hintLenC KCR : ℝ) + 1) ^ 4) * ((P.lam : ℝ) * P.lgn ^ hintLenQ KCR)
          ≤ hintLenC₃ KCR K * ((P.lam : ℝ) * P.lgn ^ hintLenQ KCR) :=
        mul_le_mul_of_nonneg_right h32 (mul_nonneg hlam1 hLq0)
      linarith only [h10]
    linarith only [h1, h2, h3, h9]
  have hcharge : (0 : ℝ) ≤ (X : ℝ) + hintLenAlpha KCR K * hN N Y := by
    have h2 : (0 : ℝ) ≤ hN N Y := hN_nonneg_nat hYN
    have h3 : (0 : ℝ) ≤ hintLenAlpha KCR K := le_of_lt (hintLenAlpha_pos KCR hK0)
    have h4 : (0 : ℝ) ≤ (X : ℝ) := by positivity
    nlinarith only [h2, h3, h4]
  have hC1 : (0 : ℝ) ≤ 1 + hintLenC₁ KCR K / P.lgn := by
    have h2 : (0 : ℝ) ≤ hintLenC₁ KCR K / P.lgn :=
      div_nonneg (hintLenC₁_nonneg hK0) hLn
    linarith only [h2]
  have hC2 : (0 : ℝ) ≤ hintLenC₂ KCR K * ((N : ℝ) / P.lgn ^ 8) := by
    rw [div_eq_mul_inv]
    exact mul_nonneg (hintLenC₂_nonneg hK0) (mul_nonneg (by positivity) (inv_nonneg.mpr (pow_nonneg hLn 8)))
  have hprod1 : (0 : ℝ) ≤
      (1 + hintLenC₁ KCR K / P.lgn) * ((X : ℝ) + hintLenAlpha KCR K * hN N Y) :=
    mul_nonneg hC1 hcharge
  have hlen : (synLen CR (.cr N (HintParams.D N X Y)) : ℝ) =
      (CR.rows N (HintParams.D N X Y) : ℝ) := rfl
  rw [hlen]
  linarith only [hfin, hprod1, hC2]

/-- The residual `CR` sketch of a `direct`/`recursive` node is `O(N/log⁸n)`: with
`t_v = min{N_v, ⌈2η(D_v+1)⌉}` and `ηlog²n = log^{-(A-2)}n`,
`Len_CR(v) ≤ KCR(2η(D_v+1)+1)4log²n ≤ 20KCR·N_v/log⁸n`.  The `+1` is harmless because the
small-instance rule has failed, hence `N_v ≥ D_v > log^{6+2A}n`, so `log²n ≤ N_v/log⁸n`. -/
lemma resid_rows_le {KCR K : ℝ} {P : HintParams} {CR : CRFamily} {N X Y : ℕ}
    (hA : P.A = hintLenA KCR) (hK0 : 0 < K) (hn : 2 ≤ P.n)
    (hN10 : P.lgn ^ 10 ≤ (N : ℝ)) (hNn : N ≤ P.n)
    (hrows : ∀ N' t : ℕ, t ≤ N' →
      (CR.rows N' t : ℝ) ≤ max KCR 0 * ((t : ℝ) * lg ((N' : ℝ) + 2) ^ 2)) :
    (CR.rows N (P.resid N X Y) : ℝ) ≤ hintLenC₂ KCR K * ((N : ℝ) * (P.lgn ^ 8)⁻¹) := by
  have hL1 : (1 : ℝ) ≤ P.lgn := one_le_lg hn
  have hL0 : (0 : ℝ) < P.lgn := by linarith only [hL1]
  have hLn : (0 : ℝ) ≤ P.lgn := le_of_lt hL0
  have hL8 : (0 : ℝ) < P.lgn ^ 8 := pow_pos hL0 8
  have htN : P.resid N X Y ≤ N := min_le_left _ _
  have hrows' := hrows N (P.resid N X Y) htN
  have heta0 : (0 : ℝ) ≤ 2 * P.eta * ((HintParams.D N X Y : ℝ) + 1) := by
    have h1 : (0 : ℝ) < P.eta := by
      rw [HintParams.eta]
      exact inv_pos.mpr (pow_pos hL0 _)
    have h2 : (0 : ℝ) ≤ (HintParams.D N X Y : ℝ) := by positivity
    nlinarith only [h1, h2]
  have ht : (P.resid N X Y : ℝ) ≤ 2 * P.eta * ((HintParams.D N X Y : ℝ) + 1) + 1 := by
    have h1n : P.resid N X Y ≤ ⌈2 * P.eta * ((HintParams.D N X Y : ℝ) + 1)⌉₊ := min_le_right _ _
    have h1 : (P.resid N X Y : ℝ) ≤ ((⌈2 * P.eta * ((HintParams.D N X Y : ℝ) + 1)⌉₊ : ℕ) : ℝ) := by
      exact_mod_cast h1n
    have h2 := Nat.ceil_lt_add_one heta0
    linarith only [h1, h2]
  have hlg : lg ((N : ℝ) + 2) ^ 2 ≤ 4 * P.lgn ^ 2 := lg_add_two_sq_le hNn hn
  have hb1 : (0 : ℝ) ≤ 2 * P.eta * ((HintParams.D N X Y : ℝ) + 1) + 1 := by linarith only [heta0]
  have hstep : (CR.rows N (P.resid N X Y) : ℝ) ≤
      max KCR 0 * ((2 * P.eta * ((HintParams.D N X Y : ℝ) + 1) + 1) * (4 * P.lgn ^ 2)) := by
    have h2 : (P.resid N X Y : ℝ) * lg ((N : ℝ) + 2) ^ 2
        ≤ (2 * P.eta * ((HintParams.D N X Y : ℝ) + 1) + 1) * (4 * P.lgn ^ 2) := by
      calc (P.resid N X Y : ℝ) * lg ((N : ℝ) + 2) ^ 2
          ≤ (2 * P.eta * ((HintParams.D N X Y : ℝ) + 1) + 1) * lg ((N : ℝ) + 2) ^ 2 :=
            mul_le_mul_of_nonneg_right ht (by positivity)
        _ ≤ (2 * P.eta * ((HintParams.D N X Y : ℝ) + 1) + 1) * (4 * P.lgn ^ 2) :=
            mul_le_mul_of_nonneg_left hlg hb1
    calc (CR.rows N (P.resid N X Y) : ℝ)
        ≤ max KCR 0 * ((P.resid N X Y : ℝ) * lg ((N : ℝ) + 2) ^ 2) := hrows'
      _ ≤ max KCR 0 * ((2 * P.eta * ((HintParams.D N X Y : ℝ) + 1) + 1) * (4 * P.lgn ^ 2)) :=
          mul_le_mul_of_nonneg_left h2 (le_max_right _ _)
  have hN1 : (1 : ℝ) ≤ (N : ℝ) := by
    have h2 : (1 : ℝ) ≤ P.lgn ^ 10 := by
      calc (1 : ℝ) = 1 ^ 10 := by norm_num
        _ ≤ P.lgn ^ 10 := pow_le_pow_left₀ (by norm_num) hL1 10
    linarith only [h2, hN10]
  have hLinv0 : (0 : ℝ) ≤ (P.lgn ^ 8)⁻¹ := (inv_pos.mpr hL8).le
  have hetaL : P.eta * P.lgn ^ 2 ≤ (P.lgn ^ 8)⁻¹ := eta_lgn_sq_le hA hn
  have hDle : (HintParams.D N X Y : ℝ) ≤ (N : ℝ) := by
    have h : HintParams.D N X Y ≤ N := min_le_left _ _
    exact_mod_cast h
  have hterm2 : P.eta * P.lgn ^ 2 ≤ (N : ℝ) * (P.lgn ^ 8)⁻¹ := by
    have h : (1 : ℝ) * (P.lgn ^ 8)⁻¹ ≤ (N : ℝ) * (P.lgn ^ 8)⁻¹ :=
      mul_le_mul_of_nonneg_right hN1 hLinv0
    linarith only [hetaL, h]
  have hterm1 : (HintParams.D N X Y : ℝ) * (P.eta * P.lgn ^ 2) ≤ (N : ℝ) * (P.lgn ^ 8)⁻¹ := by
    have h2 : (HintParams.D N X Y : ℝ) * (P.eta * P.lgn ^ 2)
        ≤ (HintParams.D N X Y : ℝ) * (P.lgn ^ 8)⁻¹ :=
      mul_le_mul_of_nonneg_left hetaL (by positivity)
    have h3 : (HintParams.D N X Y : ℝ) * (P.lgn ^ 8)⁻¹ ≤ (N : ℝ) * (P.lgn ^ 8)⁻¹ :=
      mul_le_mul_of_nonneg_right hDle hLinv0
    linarith only [h2, h3]
  have hL2eq : P.lgn ^ 10 * (P.lgn ^ 8)⁻¹ = P.lgn ^ 2 := by
    have h10 : P.lgn ^ 10 = P.lgn ^ 2 * P.lgn ^ 8 := by ring
    rw [h10, mul_assoc, mul_inv_cancel₀ (ne_of_gt hL8), mul_one]
  have hterm3 : (4 : ℝ) * P.lgn ^ 2 ≤ 4 * ((N : ℝ) * (P.lgn ^ 8)⁻¹) := by
    have h2 : P.lgn ^ 2 ≤ (N : ℝ) * (P.lgn ^ 8)⁻¹ := by
      rw [← hL2eq]
      exact mul_le_mul_of_nonneg_right hN10 hLinv0
    nlinarith only [h2]
  have hmain : (2 * P.eta * ((HintParams.D N X Y : ℝ) + 1) + 1) * (4 * P.lgn ^ 2)
      ≤ 20 * ((N : ℝ) * (P.lgn ^ 8)⁻¹) := by
    have hexp : (2 * P.eta * ((HintParams.D N X Y : ℝ) + 1) + 1) * (4 * P.lgn ^ 2)
        = 8 * ((HintParams.D N X Y : ℝ) * (P.eta * P.lgn ^ 2)) + 8 * (P.eta * P.lgn ^ 2)
          + 4 * P.lgn ^ 2 := by ring
    nlinarith only [hexp, hterm1, hterm2, hterm3]
  have hK0' : (0 : ℝ) ≤ max KCR 0 := le_max_right _ _
  have hNinv0 : (0 : ℝ) ≤ (N : ℝ) * (P.lgn ^ 8)⁻¹ := mul_nonneg (by positivity) hLinv0
  have h20 : 20 * max KCR 0 ≤ hintLenC₂ KCR K := twenty_max_le_C₂ hK0
  have h5 : (20 : ℝ) * max KCR 0 * ((N : ℝ) * (P.lgn ^ 8)⁻¹)
      ≤ hintLenC₂ KCR K * ((N : ℝ) * (P.lgn ^ 8)⁻¹) :=
    mul_le_mul_of_nonneg_right h20 hNinv0
  calc (CR.rows N (P.resid N X Y) : ℝ)
      ≤ max KCR 0 * ((2 * P.eta * ((HintParams.D N X Y : ℝ) + 1) + 1) * (4 * P.lgn ^ 2)) := hstep
    _ ≤ max KCR 0 * (20 * ((N : ℝ) * (P.lgn ^ 8)⁻¹)) := mul_le_mul_of_nonneg_left hmain hK0'
    _ ≤ hintLenC₂ KCR K * ((N : ℝ) * (P.lgn ^ 8)⁻¹) := by linarith only [h5]


/-! ### 9g. The length invariant and conjunct 4 -/

/-- The `HintParams` of conjunct 4: at the extracted witnesses `A = hintLenA KCR`,
`C = hintLenC KCR`. -/
noncomputable def hintP (KCR : ℝ) (n lam : ℕ) : HintParams := ⟨hintLenA KCR, hintLenC KCR, n, lam⟩

/-- Lemma 5.9's first two conclusions at a general `P` with `P.A = hintLenA KCR`,
`P.C = hintLenC KCR` (the paper's child-space and density-contraction bounds). -/
theorem lemma_5_9_first_two {KCR : ℝ} {P : HintParams} {N X Y : ℕ} {CR : CRFamily}
    (hA : P.A = hintLenA KCR) (hC : P.C = hintLenC KCR)
    (hrows : ∀ N' t : ℕ, t ≤ N' →
      (CR.rows N' t : ℝ) ≤ KCR * ((t : ℝ) * lg ((N' : ℝ) + 2) ^ 2))
    (hargs : P.NodeArgs N X Y) (hrec : P.rule N X Y = .recursive) :
    ((∑ s ∈ range (P.ell N X Y), (P.capX N X Y s : ℝ))
        ≤ (X : ℝ) + hintLenK₅₉ KCR * ((hintLenC KCR : ℝ) * hN N Y)) ∧
      ((∑ s ∈ range (P.ell N X Y), hN Y (P.capY N X Y s)) ≤ hN N Y / 4) := by
  obtain ⟨A, C, n, lam⟩ := P
  subst hA
  subst hC
  have h509 := lemma_5_9_at (KCR := KCR) (n := n) (lam := lam) hrows hargs hrec
  simp only [Hint509] at h509
  obtain ⟨h1, h2, -, -⟩ := h509
  exact ⟨h1, h2⟩

/-- The small-instance rule failing forces `N ≥ D > log^{6+2A}n ≥ log^{10}n`: this makes the `+1` of
`t_v = min{N_v, ⌈2η(D_v+1)⌉}` an `O(N_v/log⁸n)`. -/
lemma lgn_pow_le_N {KCR : ℝ} {P : HintParams} {N X Y : ℕ}
    (hA : P.A = hintLenA KCR) (hC : P.C = hintLenC KCR) (hn : 2 ≤ P.n) (hlam : 1 ≤ P.lam)
    (hfail : ¬ ((HintParams.D N X Y : ℝ) ≤
      (P.C : ℝ) ^ 3 * (P.lamStar : ℝ) * P.lgn ^ 6 / P.eta ^ 2)) :
    P.lgn ^ 10 ≤ (N : ℝ) := by
  have hL1 : (1 : ℝ) ≤ P.lgn := one_le_lg hn
  have hL0 : (0 : ℝ) < P.lgn := by linarith only [hL1]
  have hCn : 1 ≤ P.C := by rw [hC]; exact le_trans (by norm_num) (forty_le_hintLenC KCR)
  have hC1 : (1 : ℝ) ≤ (P.C : ℝ) := by exact_mod_cast hCn
  have hlam1 : (1 : ℝ) ≤ (P.lam : ℝ) := by exact_mod_cast hlam
  have hstar1 : (1 : ℝ) ≤ (P.lamStar : ℝ) := by
    have h : P.lam ≤ P.lamStar := by unfold HintParams.lamStar; omega
    exact le_trans hlam1 (by exact_mod_cast h)
  have hC3 : (1 : ℝ) ≤ (P.C : ℝ) ^ 3 := one_le_pow₀ hC1
  have hprod : (1 : ℝ) ≤ (P.C : ℝ) ^ 3 * (P.lamStar : ℝ) := by
    have h := mul_le_mul hC3 hstar1 (by norm_num : (0 : ℝ) ≤ 1)
      (by positivity : (0 : ℝ) ≤ (P.C : ℝ) ^ 3)
    simpa using h
  have hA100 : 100 ≤ P.A := by rw [hA]; exact le_max_right _ _
  have h10 : 10 ≤ 6 + 2 * P.A := by omega
  have hLpart : P.lgn ^ 10 ≤ P.lgn ^ 6 * P.lgn ^ (2 * P.A) := by
    have hl : P.lgn ^ 6 * P.lgn ^ (2 * P.A) = P.lgn ^ (6 + 2 * P.A) := by rw [← pow_add]
    have hsplit : P.lgn ^ (6 + 2 * P.A) = P.lgn ^ 10 * P.lgn ^ (6 + 2 * P.A - 10) := by
      have hr : P.lgn ^ 10 * P.lgn ^ (6 + 2 * P.A - 10) = P.lgn ^ (10 + (6 + 2 * P.A - 10)) := by
        rw [← pow_add]
      rw [hr]
      congr 1
      omega
    rw [hl, hsplit]
    have h1 : (1 : ℝ) ≤ P.lgn ^ (6 + 2 * P.A - 10) := one_le_pow₀ hL1
    have h2 : (0 : ℝ) ≤ P.lgn ^ 10 := by positivity
    nlinarith only [h1, h2]
  have h4 : P.lgn ^ 10 ≤ (P.C : ℝ) ^ 3 * (P.lamStar : ℝ) * (P.lgn ^ 6 * P.lgn ^ (2 * P.A)) := by
    have h0 : (0 : ℝ) ≤ P.lgn ^ 6 * P.lgn ^ (2 * P.A) := by positivity
    calc P.lgn ^ 10 ≤ P.lgn ^ 6 * P.lgn ^ (2 * P.A) := hLpart
      _ = 1 * (P.lgn ^ 6 * P.lgn ^ (2 * P.A)) := (one_mul _).symm
      _ ≤ ((P.C : ℝ) ^ 3 * (P.lamStar : ℝ)) * (P.lgn ^ 6 * P.lgn ^ (2 * P.A)) :=
          mul_le_mul_of_nonneg_right hprod h0
      _ = (P.C : ℝ) ^ 3 * (P.lamStar : ℝ) * (P.lgn ^ 6 * P.lgn ^ (2 * P.A)) := by ring
  have hthr : P.lgn ^ 10 ≤ (P.C : ℝ) ^ 3 * (P.lamStar : ℝ) * P.lgn ^ 6 / P.eta ^ 2 := by
    rw [div_eq_mul_inv, inv_eta_sq]
    calc P.lgn ^ 10 ≤ (P.C : ℝ) ^ 3 * (P.lamStar : ℝ) * (P.lgn ^ 6 * P.lgn ^ (2 * P.A)) := h4
      _ = (P.C : ℝ) ^ 3 * (P.lamStar : ℝ) * P.lgn ^ 6 * P.lgn ^ (2 * P.A) := by ring
  have hD : (HintParams.D N X Y : ℝ) ≤ (N : ℝ) := by
    have h : HintParams.D N X Y ≤ N := min_le_left _ _
    exact_mod_cast h
  have hlt : (P.C : ℝ) ^ 3 * (P.lamStar : ℝ) * P.lgn ^ 6 / P.eta ^ 2 < (HintParams.D N X Y : ℝ) :=
    not_le.mp hfail
  linarith only [hthr, hlt, hD]

/-- At a `recursive` node `Y ≥ 1`: the small rule failed, so `D ≥ 1`, and `D ≤ X + Y`; `Y = 0` would
force `X = 0` because `m_v = max{Y, ⌈X/log³n⌉} = Y`. -/
lemma one_le_Y_of_recursive {P : HintParams} {N X Y : ℕ} (hL1 : 1 ≤ P.lgn)
    (hcf : ¬ ((HintParams.D N X Y : ℝ) ≤ (N : ℝ) / P.lgn ^ 10))
    (hrowsY : P.rows X Y = Y) : 1 ≤ Y := by
  have hL0 : (0 : ℝ) < P.lgn := by linarith only [hL1]
  have hLn : (0 : ℝ) ≤ P.lgn := le_of_lt hL0
  have hD1 : (1 : ℝ) ≤ (HintParams.D N X Y : ℝ) := by
    have h0 : (0 : ℝ) ≤ (N : ℝ) / P.lgn ^ 10 := div_nonneg (by positivity) (pow_nonneg hLn 10)
    have h1 : (N : ℝ) / P.lgn ^ 10 < (HintParams.D N X Y : ℝ) := not_le.mp hcf
    have h2 : (0 : ℝ) < (HintParams.D N X Y : ℝ) := lt_of_le_of_lt h0 h1
    have h3 : (0 : ℕ) < HintParams.D N X Y := by exact_mod_cast h2
    exact_mod_cast h3
  rcases Nat.eq_zero_or_pos Y with h0 | hpos
  · exfalso
    -- `Y = 0` forces `X ≥ 1` (because `D ≥ 1`), hence `⌈X/log³n⌉ ≥ 1 ≠ Y`
    have hX1 : (1 : ℝ) ≤ (X : ℝ) := by
      have hDle : (HintParams.D N X Y : ℝ) ≤ (X : ℝ) + (Y : ℝ) := by
        have h : HintParams.D N X Y ≤ X + Y := min_le_right _ _
        exact_mod_cast h
      rw [h0] at hD1 hDle
      push_cast at hDle
      linarith only [hD1, hDle]
    have hc1 : 1 ≤ ⌈(X : ℝ) / P.lgn ^ 3⌉₊ := by
      have h3 : (0 : ℝ) < P.lgn ^ 3 := pow_pos hL0 3
      have hpos2 : (0 : ℝ) < (X : ℝ) / P.lgn ^ 3 := div_pos (by linarith only [hX1]) h3
      have h := Nat.le_ceil ((X : ℝ) / P.lgn ^ 3)
      have h2 : (0 : ℝ) < ((⌈(X : ℝ) / P.lgn ^ 3⌉₊ : ℕ) : ℝ) := lt_of_lt_of_le hpos2 h
      exact_mod_cast h2
    have hc0 : ⌈(X : ℝ) / P.lgn ^ 3⌉₊ = 0 := by
      have h : P.rows X 0 = 0 := by rw [← h0]; exact hrowsY
      unfold HintParams.rows at h
      have h' : ⌈(X : ℝ) / P.lgn ^ 3⌉₊ ≤ 0 := by
        calc ⌈(X : ℝ) / P.lgn ^ 3⌉₊ ≤ max 0 ⌈(X : ℝ) / P.lgn ^ 3⌉₊ := le_max_right _ _
          _ = 0 := h
      omega
    omega
  · exact hpos

/-- The paper's step 1 (`direct`): `Len_direct(v) = m_v·ℓ_v + Len_CR(v) ≤ (1 + C₁/log n)(X_v + αh_N)
+ C₂N_v/log⁸n + C₃λlog^q n`, the columns by `rows_mul_ell_le` and the residual by `resid_rows_le`. -/
lemma len_direct_le {KCR K : ℝ} {P : HintParams} {CR : CRFamily} {N X Y : ℕ}
    (hA : P.A = hintLenA KCR) (hC : P.C = hintLenC KCR) (hK : 0 < K) (hKCR : KCR ≤ K)
    (hn : 2 ≤ P.n) (hlam : 1 ≤ P.lam) (hN1 : 1 ≤ N) (hNn : N ≤ P.n) (hXN : X ≤ N) (hYN : Y ≤ N)
    (hd : P.rule N X Y = .direct)
    (hrows : ∀ N' t : ℕ, t ≤ N' →
      (CR.rows N' t : ℝ) ≤ max KCR 0 * ((t : ℝ) * lg ((N' : ℝ) + 2) ^ 2)) :
    (synLen CR (.direct (P.scheme N X Y) (P.resid N X Y)) : ℝ) ≤
      (1 + hintLenC₁ KCR K / P.lgn) * ((X : ℝ) + hintLenAlpha KCR K * hN N Y) +
        hintLenC₂ KCR K * ((N : ℝ) / P.lgn ^ 8) +
          hintLenC₃ KCR K * (P.lam : ℝ) * P.lgn ^ hintLenQ KCR := by
  have hL1 : (1 : ℝ) ≤ P.lgn := one_le_lg hn
  have hL0 : (0 : ℝ) < P.lgn := by linarith only [hL1]
  obtain ⟨-, hsmall, hmne⟩ := rule_direct_spec hd
  have hcols := rows_mul_ell_le (KCR := KCR) (K := K) (P := P) hA hC hK hn hlam hN1 hNn hXN hYN hmne
  have hres : (CR.rows N (P.resid N X Y) : ℝ) ≤ hintLenC₂ KCR K * ((N : ℝ) * (P.lgn ^ 8)⁻¹) :=
    resid_rows_le (KCR := KCR) (K := K) (P := P) hA hK hn
      (lgn_pow_le_N hA hC hn hlam (not_le.mpr hsmall)) hNn hrows
  have hres' : (CR.rows N (P.resid N X Y) : ℝ) ≤ hintLenC₂ KCR K * ((N : ℝ) / P.lgn ^ 8) := by
    rw [div_eq_mul_inv]
    exact hres
  have hXle : (X : ℝ) ≤ (X : ℝ) + hintLenAlpha KCR K * hN N Y := by
    have h1 : (0 : ℝ) ≤ hN N Y := hN_nonneg_nat hYN
    have h2 : (0 : ℝ) ≤ hintLenAlpha KCR K := le_of_lt (hintLenAlpha_pos KCR hK)
    nlinarith only [h1, h2]
  have hC10 : (0 : ℝ) ≤ hintLenC₁ KCR K := hintLenC₁_nonneg hK
  have hstep1 : (1 + hintLenC₁ KCR K / (2 * P.lgn)) * (X : ℝ)
      ≤ (1 + hintLenC₁ KCR K / P.lgn) * ((X : ℝ) + hintLenAlpha KCR K * hN N Y) := by
    have hX0 : (0 : ℝ) ≤ (X : ℝ) := by positivity
    have hdiv : hintLenC₁ KCR K / (2 * P.lgn) ≤ hintLenC₁ KCR K / P.lgn := by
      have h2L : (0 : ℝ) < 2 * P.lgn := by linarith only [hL0]
      have hinv : (2 * P.lgn)⁻¹ ≤ P.lgn⁻¹ := (inv_le_inv₀ h2L hL0).mpr (by linarith only [hL0])
      calc hintLenC₁ KCR K / (2 * P.lgn) = hintLenC₁ KCR K * (2 * P.lgn)⁻¹ := div_eq_mul_inv _ _
        _ ≤ hintLenC₁ KCR K * P.lgn⁻¹ := mul_le_mul_of_nonneg_left hinv hC10
        _ = hintLenC₁ KCR K / P.lgn := (div_eq_mul_inv _ _).symm
    have hcoef : (1 + hintLenC₁ KCR K / (2 * P.lgn)) ≤ (1 + hintLenC₁ KCR K / P.lgn) := by
      linarith only [hdiv]
    have hcoef0 : (0 : ℝ) ≤ 1 + hintLenC₁ KCR K / P.lgn := by
      have h : (0 : ℝ) ≤ hintLenC₁ KCR K / P.lgn := div_nonneg hC10 (le_of_lt hL0)
      linarith only [h]
    calc (1 + hintLenC₁ KCR K / (2 * P.lgn)) * (X : ℝ)
        ≤ (1 + hintLenC₁ KCR K / P.lgn) * (X : ℝ) := mul_le_mul_of_nonneg_right hcoef hX0
      _ ≤ (1 + hintLenC₁ KCR K / P.lgn) * ((X : ℝ) + hintLenAlpha KCR K * hN N Y) :=
          mul_le_mul_of_nonneg_left hXle hcoef0
  have hlen : (synLen CR (.direct (P.scheme N X Y) (P.resid N X Y)) : ℝ)
      = (P.rows X Y : ℝ) * (P.ell N X Y : ℝ) + (CR.rows N (P.resid N X Y) : ℝ) := by
    simp only [synLen, HintParams.scheme, Nat.cast_mul, Nat.cast_add]
  rw [hlen]
  linarith only [hcols, hres', hstep1]

/-- The paper's step 2 (`recursive`): the children's charges contract (`Lemma 5.9`), their
`C₂N_s/log⁸n` overflow is paid by the relative overhead (`Y ≤ h_N` and `ℓ_v = O(log³n)`), and the
node's own residual goes into `C₂N_v/log⁸n`; the extra `λlog^q n` per node is what `nodeCount` counts. -/
lemma len_recursive_le {KCR K : ℝ} {P : HintParams} {CR : CRFamily} {N X Y : ℕ}
    (hA : P.A = hintLenA KCR) (hC : P.C = hintLenC KCR) (hK : 0 < K) (hKCR : KCR ≤ K)
    (hK₅₉ : hintLenK₅₉ KCR ≤ K) (hn : 2 ≤ P.n) (hlam : 1 ≤ P.lam)
    (hN1 : 1 ≤ N) (hNn : N ≤ P.n) (hXN : X ≤ N) (hYN : Y ≤ N)
    (hrec : P.rule N X Y = .recursive)
    (hrows : ∀ N' t : ℕ, t ≤ N' → (CR.rows N' t : ℝ) ≤ KCR * ((t : ℝ) * lg ((N' : ℝ) + 2) ^ 2))
    (chi : Fin (P.ell N X Y) → Node)
    (hih : ∀ s : Fin (P.ell N X Y), (synLen CR (chi s) : ℝ) ≤
      (1 + hintLenC₁ KCR K / P.lgn) *
          ((P.capX N X Y s.val : ℝ) + hintLenAlpha KCR K * hN Y (P.capY N X Y s.val)) +
        hintLenC₂ KCR K * ((Y : ℝ) / P.lgn ^ 8) +
          hintLenC₃ KCR K * (P.lam : ℝ) * P.lgn ^ hintLenQ KCR * ((chi s).nodeCount : ℝ)) :
    (synLen CR (.recursive (P.scheme N X Y) (P.resid N X Y)
        (fun s => P.capX N X Y s.val) (fun s => P.capY N X Y s.val) chi) : ℝ) ≤
      (1 + hintLenC₁ KCR K / P.lgn) * ((X : ℝ) + hintLenAlpha KCR K * hN N Y) +
        hintLenC₂ KCR K * ((N : ℝ) / P.lgn ^ 8) +
          hintLenC₃ KCR K * (P.lam : ℝ) * P.lgn ^ hintLenQ KCR *
            ((Node.recursive (P.scheme N X Y) (P.resid N X Y)
              (fun s => P.capX N X Y s.val) (fun s => P.capY N X Y s.val) chi).nodeCount : ℝ) := by
  have hL1 : (1 : ℝ) ≤ P.lgn := one_le_lg hn
  have hL0 : (0 : ℝ) < P.lgn := by linarith only [hL1]
  have hLn : (0 : ℝ) ≤ P.lgn := le_of_lt hL0
  have hC20 : (0 : ℝ) ≤ hintLenC₂ KCR K := hintLenC₂_nonneg hK
  have hC30 : (0 : ℝ) ≤ hintLenC₃ KCR K := hintLenC₃_nonneg KCR hK
  have hC10 : (0 : ℝ) ≤ hintLenC₁ KCR K := hintLenC₁_nonneg hK
  have hα0 : (0 : ℝ) ≤ hintLenAlpha KCR K := le_of_lt (hintLenAlpha_pos KCR hK)
  have hlam0 : (0 : ℝ) ≤ (P.lam : ℝ) := by positivity
  have hLq0 : (0 : ℝ) ≤ P.lgn ^ hintLenQ KCR := pow_nonneg hLn _
  obtain ⟨hcf, hsf, hrowsY⟩ := rule_recursive_spec hrec
  have hY1 : 1 ≤ Y := one_le_Y_of_recursive hL1 hcf hrowsY
  have hYn : Y ≤ P.n := le_trans hYN hNn
  have hsum : (∑ s : Fin (P.ell N X Y), (synLen CR (chi s) : ℝ)) ≤
      (1 + hintLenC₁ KCR K / P.lgn) *
          (∑ s : Fin (P.ell N X Y),
            ((P.capX N X Y s.val : ℝ) + hintLenAlpha KCR K * hN Y (P.capY N X Y s.val))) +
        (P.ell N X Y : ℝ) * (hintLenC₂ KCR K * ((Y : ℝ) / P.lgn ^ 8)) +
          hintLenC₃ KCR K * (P.lam : ℝ) * P.lgn ^ hintLenQ KCR *
            (∑ s : Fin (P.ell N X Y), ((chi s).nodeCount : ℝ)) := by
    have h1 := Finset.sum_le_sum (s := Finset.univ)
      (f := fun s : Fin (P.ell N X Y) => (synLen CR (chi s) : ℝ))
      (g := fun s : Fin (P.ell N X Y) =>
        (1 + hintLenC₁ KCR K / P.lgn) *
            ((P.capX N X Y s.val : ℝ) + hintLenAlpha KCR K * hN Y (P.capY N X Y s.val)) +
          hintLenC₂ KCR K * ((Y : ℝ) / P.lgn ^ 8) +
            hintLenC₃ KCR K * (P.lam : ℝ) * P.lgn ^ hintLenQ KCR * ((chi s).nodeCount : ℝ))
      (fun s _ => hih s)
    have h2 : (∑ s : Fin (P.ell N X Y),
        ((1 + hintLenC₁ KCR K / P.lgn) *
            ((P.capX N X Y s.val : ℝ) + hintLenAlpha KCR K * hN Y (P.capY N X Y s.val)) +
          hintLenC₂ KCR K * ((Y : ℝ) / P.lgn ^ 8) +
            hintLenC₃ KCR K * (P.lam : ℝ) * P.lgn ^ hintLenQ KCR * ((chi s).nodeCount : ℝ)))
        = (1 + hintLenC₁ KCR K / P.lgn) *
            (∑ s : Fin (P.ell N X Y),
              ((P.capX N X Y s.val : ℝ) + hintLenAlpha KCR K * hN Y (P.capY N X Y s.val))) +
          (P.ell N X Y : ℝ) * (hintLenC₂ KCR K * ((Y : ℝ) / P.lgn ^ 8)) +
            hintLenC₃ KCR K * (P.lam : ℝ) * P.lgn ^ hintLenQ KCR *
              (∑ s : Fin (P.ell N X Y), ((chi s).nodeCount : ℝ)) := by
      simp only [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_const, Finset.card_univ,
        Fintype.card_fin, nsmul_eq_mul]
      ring
    rw [h2] at h1
    exact h1
  obtain ⟨h509a, h509b⟩ := lemma_5_9_first_two hA hC hrows
    ⟨hn, hlam, hN1, hNn, hXN, hYN⟩ hrec
  have hcharge : (∑ s : Fin (P.ell N X Y),
        ((P.capX N X Y s.val : ℝ) + hintLenAlpha KCR K * hN Y (P.capY N X Y s.val))) +
      (hintLenAlpha KCR K / 2) * hN N Y ≤ (X : ℝ) + hintLenAlpha KCR K * hN N Y := by
    have hsum2 : (∑ s : Fin (P.ell N X Y),
          ((P.capX N X Y s.val : ℝ) + hintLenAlpha KCR K * hN Y (P.capY N X Y s.val)))
        = (∑ s : Fin (P.ell N X Y), (P.capX N X Y s.val : ℝ)) +
          hintLenAlpha KCR K * (∑ s : Fin (P.ell N X Y), hN Y (P.capY N X Y s.val)) := by
      rw [Finset.sum_add_distrib, Finset.mul_sum]
    have h1 : (∑ s : Fin (P.ell N X Y), (P.capX N X Y s.val : ℝ))
        ≤ (X : ℝ) + hintLenK₅₉ KCR * ((hintLenC KCR : ℝ) * hN N Y) := by
      simpa only [Finset.sum_range] using h509a
    have h2 : (∑ s : Fin (P.ell N X Y), hN Y (P.capY N X Y s.val)) ≤ hN N Y / 4 := by
      simpa only [Finset.sum_range] using h509b
    have hKC : hintLenK₅₉ KCR * (hintLenC KCR : ℝ) ≤ hintLenAlpha KCR K / 4 := by
      have h0 : (0 : ℝ) ≤ (hintLenC KCR : ℝ) := by positivity
      have h1' : hintLenK₅₉ KCR * (hintLenC KCR : ℝ) ≤ K * (hintLenC KCR : ℝ) :=
        mul_le_mul_of_nonneg_right hK₅₉ h0
      have h2' : K * (hintLenC KCR : ℝ) ≤ (K + (hintLenC KCR : ℝ)) ^ 2 / 4 := by
        nlinarith only [sq_nonneg (K - (hintLenC KCR : ℝ))]
      have h3' : hintLenAlpha KCR K = (K + (hintLenC KCR : ℝ)) ^ 2 := rfl
      linarith only [h1', h2', h3']
    have hhN : (0 : ℝ) ≤ hN N Y := hN_nonneg_nat hYN
    rw [hsum2]
    nlinarith only [h1, h2, hKC, hhN, hα0]
  have hover : (P.ell N X Y : ℝ) * (hintLenC₂ KCR K * ((Y : ℝ) / P.lgn ^ 8))
      ≤ (hintLenC₁ KCR K / P.lgn) * ((hintLenAlpha KCR K / 2) * hN N Y) := by
    have hE1 : (0 : ℝ) < (hintLenE KCR : ℝ) + 1 := by positivity
    have hYle : (Y : ℝ) ≤ hN N Y := nat_le_hN hYN
    have hell : (P.ell N X Y : ℝ) ≤ ((hintLenE KCR : ℝ) + 1) * P.lgn ^ 3 :=
      ell_le_cubic hA hC hn hN1 hNn hXN hYN (by rw [hrowsY]; exact hY1)
    have h1 : (P.ell N X Y : ℝ) * hintLenC₂ KCR K * (Y : ℝ)
        ≤ (((hintLenE KCR : ℝ) + 1) * P.lgn ^ 3) * hintLenC₂ KCR K * hN N Y := by
      have h2 : (P.ell N X Y : ℝ) * hintLenC₂ KCR K
          ≤ (((hintLenE KCR : ℝ) + 1) * P.lgn ^ 3) * hintLenC₂ KCR K :=
        mul_le_mul_of_nonneg_right hell hC20
      have h3 : (P.ell N X Y : ℝ) * hintLenC₂ KCR K * (Y : ℝ)
          ≤ (((hintLenE KCR : ℝ) + 1) * P.lgn ^ 3) * hintLenC₂ KCR K * (Y : ℝ) :=
        mul_le_mul_of_nonneg_right h2 (by positivity)
      have h4 : (((hintLenE KCR : ℝ) + 1) * P.lgn ^ 3) * hintLenC₂ KCR K * (Y : ℝ)
          ≤ (((hintLenE KCR : ℝ) + 1) * P.lgn ^ 3) * hintLenC₂ KCR K * hN N Y :=
        mul_le_mul_of_nonneg_left hYle (by positivity)
      linarith only [h3, h4]
    have hbase : 2 * hintLenC₂ KCR K * ((hintLenE KCR : ℝ) + 1)
        ≤ hintLenC₁ KCR K * hintLenAlpha KCR K := two_C₂_E_le_C₁_alpha hK
    have h2 : ((hintLenE KCR : ℝ) + 1) * P.lgn ^ 3 * hintLenC₂ KCR K
        ≤ (hintLenC₁ KCR K / P.lgn) * (hintLenAlpha KCR K / 2) * P.lgn ^ 8 := by
      have h3 : 2 * hintLenC₂ KCR K * ((hintLenE KCR : ℝ) + 1) * P.lgn ^ 3
          ≤ hintLenC₁ KCR K * hintLenAlpha KCR K * P.lgn ^ 3 :=
        mul_le_mul_of_nonneg_right hbase (pow_nonneg hLn 3)
      have h4 : hintLenC₁ KCR K * hintLenAlpha KCR K * P.lgn ^ 3
          ≤ hintLenC₁ KCR K * hintLenAlpha KCR K * P.lgn ^ 7 := by
        have h37 : P.lgn ^ 3 ≤ P.lgn ^ 7 := by
          have hsplit : P.lgn ^ 7 = P.lgn ^ 3 * P.lgn ^ 4 := by ring
          have hL4 : (1 : ℝ) ≤ P.lgn ^ 4 := one_le_pow₀ hL1
          have h0 : (0 : ℝ) ≤ P.lgn ^ 3 := pow_nonneg hLn 3
          rw [hsplit]
          nlinarith only [hL4, h0]
        exact mul_le_mul_of_nonneg_left h37 (mul_nonneg hC10 hα0)
      have h5 : 2 * hintLenC₂ KCR K * ((hintLenE KCR : ℝ) + 1) * P.lgn ^ 3
          ≤ hintLenC₁ KCR K * hintLenAlpha KCR K * P.lgn ^ 7 := le_trans h3 h4
      have h6 : ((hintLenE KCR : ℝ) + 1) * P.lgn ^ 3 * hintLenC₂ KCR K
          ≤ hintLenC₁ KCR K * hintLenAlpha KCR K * P.lgn ^ 7 / 2 := by
        nlinarith only [h5]
      have h7 : hintLenC₁ KCR K * hintLenAlpha KCR K * P.lgn ^ 7 / 2
          = (hintLenC₁ KCR K / P.lgn) * (hintLenAlpha KCR K / 2) * P.lgn ^ 8 := by
        have hL0ne : P.lgn ≠ 0 := ne_of_gt hL0
        field_simp
        try ring
      rw [h7] at h6
      exact h6
    have hL8ne : (P.lgn ^ 8) ≠ 0 := ne_of_gt (pow_pos hL0 8)
    calc (P.ell N X Y : ℝ) * (hintLenC₂ KCR K * ((Y : ℝ) / P.lgn ^ 8))
        = ((P.ell N X Y : ℝ) * hintLenC₂ KCR K * (Y : ℝ)) * (P.lgn ^ 8)⁻¹ := by
          rw [div_eq_mul_inv]; ring
      _ ≤ ((((hintLenE KCR : ℝ) + 1) * P.lgn ^ 3) * hintLenC₂ KCR K * hN N Y) *
            (P.lgn ^ 8)⁻¹ := by
          refine mul_le_mul_of_nonneg_right h1 ?_
          exact (inv_pos.mpr (pow_pos hL0 8)).le
      _ = ((((hintLenE KCR : ℝ) + 1) * P.lgn ^ 3) * hintLenC₂ KCR K) * (hN N Y / P.lgn ^ 8) := by
          rw [div_eq_mul_inv]; ring
      _ ≤ ((hintLenC₁ KCR K / P.lgn) * (hintLenAlpha KCR K / 2) * P.lgn ^ 8) *
            (hN N Y / P.lgn ^ 8) := by
          refine mul_le_mul_of_nonneg_right h2 ?_
          have h0 : (0 : ℝ) ≤ hN N Y := hN_nonneg_nat hYN
          exact div_nonneg h0 (pow_nonneg hLn 8)
      _ = (hintLenC₁ KCR K / P.lgn) * ((hintLenAlpha KCR K / 2) * hN N Y) := by
          field_simp
          try ring
  have hres : (CR.rows N (P.resid N X Y) : ℝ) ≤ hintLenC₂ KCR K * ((N : ℝ) * (P.lgn ^ 8)⁻¹) :=
    resid_rows_le (KCR := KCR) (K := K) (P := P) hA hK hn
      (lgn_pow_le_N hA hC hn hlam hsf) hNn (rows_bound_nonneg hrows)
  have hres' : (CR.rows N (P.resid N X Y) : ℝ) ≤ hintLenC₂ KCR K * ((N : ℝ) / P.lgn ^ 8) := by
    rw [div_eq_mul_inv]
    exact hres
  have hcoef : (0 : ℝ) ≤ 1 + hintLenC₁ KCR K / P.lgn := by
    have h2 : (0 : ℝ) ≤ hintLenC₁ KCR K / P.lgn := div_nonneg hC10 hLn
    linarith only [h2]
  have hs : (0 : ℝ) ≤ (hintLenAlpha KCR K / 2) * hN N Y :=
    mul_nonneg (by linarith only [hα0]) (hN_nonneg_nat hYN)
  have hmain : (1 + hintLenC₁ KCR K / P.lgn) *
        (∑ s : Fin (P.ell N X Y),
          ((P.capX N X Y s.val : ℝ) + hintLenAlpha KCR K * hN Y (P.capY N X Y s.val))) +
      (P.ell N X Y : ℝ) * (hintLenC₂ KCR K * ((Y : ℝ) / P.lgn ^ 8))
      ≤ (1 + hintLenC₁ KCR K / P.lgn) * ((X : ℝ) + hintLenAlpha KCR K * hN N Y) := by
    have hA1 : (1 + hintLenC₁ KCR K / P.lgn) *
          (∑ s : Fin (P.ell N X Y),
            ((P.capX N X Y s.val : ℝ) + hintLenAlpha KCR K * hN Y (P.capY N X Y s.val))) +
        (1 + hintLenC₁ KCR K / P.lgn) * ((hintLenAlpha KCR K / 2) * hN N Y)
        ≤ (1 + hintLenC₁ KCR K / P.lgn) * ((X : ℝ) + hintLenAlpha KCR K * hN N Y) := by
      have h := mul_le_mul_of_nonneg_left hcharge hcoef
      have he : (1 + hintLenC₁ KCR K / P.lgn) *
            (∑ s : Fin (P.ell N X Y),
              ((P.capX N X Y s.val : ℝ) + hintLenAlpha KCR K * hN Y (P.capY N X Y s.val))) +
          (1 + hintLenC₁ KCR K / P.lgn) * ((hintLenAlpha KCR K / 2) * hN N Y)
          = (1 + hintLenC₁ KCR K / P.lgn) *
              ((∑ s : Fin (P.ell N X Y),
                ((P.capX N X Y s.val : ℝ) + hintLenAlpha KCR K * hN Y (P.capY N X Y s.val))) +
                (hintLenAlpha KCR K / 2) * hN N Y) := by ring
      linarith only [h, he]
    have hA2 : (P.ell N X Y : ℝ) * (hintLenC₂ KCR K * ((Y : ℝ) / P.lgn ^ 8))
        ≤ (1 + hintLenC₁ KCR K / P.lgn) * ((hintLenAlpha KCR K / 2) * hN N Y) := by
      have h2 : (1 + hintLenC₁ KCR K / P.lgn) * ((hintLenAlpha KCR K / 2) * hN N Y)
          = (hintLenAlpha KCR K / 2) * hN N Y +
            (hintLenC₁ KCR K / P.lgn) * ((hintLenAlpha KCR K / 2) * hN N Y) := by ring
      linarith only [hover, h2, hs]
    linarith only [hA1, hA2]
  have hlen : (synLen CR (.recursive (P.scheme N X Y) (P.resid N X Y)
        (fun s => P.capX N X Y s.val) (fun s => P.capY N X Y s.val) chi) : ℝ)
      = (∑ s : Fin (P.ell N X Y), (synLen CR (chi s) : ℝ)) + (CR.rows N (P.resid N X Y) : ℝ) := by
    simp only [synLen, HintParams.scheme, Nat.cast_add, Nat.cast_sum]
    try rfl
  have hnc : ((Node.recursive (P.scheme N X Y) (P.resid N X Y)
        (fun s => P.capX N X Y s.val) (fun s => P.capY N X Y s.val) chi).nodeCount : ℝ)
      = 1 + ∑ s : Fin (P.ell N X Y), ((chi s).nodeCount : ℝ) := by
    simp only [Node.nodeCount, HintParams.scheme, Nat.cast_add, Nat.cast_one, Nat.cast_sum]
    try rfl
  have hb : (0 : ℝ) ≤ hintLenC₃ KCR K * (P.lam : ℝ) * P.lgn ^ hintLenQ KCR :=
    mul_nonneg (mul_nonneg hC30 hlam0) hLq0
  rw [hlen, hnc]
  nlinarith only [hsum, hmain, hres', hb]

/-- The length invariant of §5.4, by induction on the fuel of `P.tree`:

  `Len(T) ≤ (1 + C₁/log n)(X + αh_N(N,Y)) + C₂N/log⁸n + C₃λlog^q n·nodeCount T`.

The induction is on `fuel`, not on `IsSchemeTree`: `IsSchemeTree.cr` accepts an arbitrary `t`, so its
constructors do not distinguish `cheap` from `small`. -/
theorem len_le_charge {KCR K : ℝ} (hK : 0 < K) (hKCR : KCR ≤ K) (hK₅₉ : hintLenK₅₉ KCR ≤ K)
    {CR : CRFamily}
    (hrows : ∀ N' t : ℕ, t ≤ N' → (CR.rows N' t : ℝ) ≤ KCR * ((t : ℝ) * lg ((N' : ℝ) + 2) ^ 2))
    (P : HintParams) (hA : P.A = hintLenA KCR) (hC : P.C = hintLenC KCR)
    (hn : 2 ≤ P.n) (hlam : 1 ≤ P.lam) :
    ∀ (fuel N X Y : ℕ) (T : Node), P.tree fuel N X Y = some T →
      1 ≤ N → N ≤ P.n → X ≤ N → Y ≤ N →
      (synLen CR T : ℝ) ≤
        (1 + hintLenC₁ KCR K / P.lgn) * ((X : ℝ) + hintLenAlpha KCR K * hN N Y) +
          hintLenC₂ KCR K * ((N : ℝ) / P.lgn ^ 8) +
            hintLenC₃ KCR K * (P.lam : ℝ) * P.lgn ^ hintLenQ KCR * (T.nodeCount : ℝ) := by
  have hrows0 := rows_bound_nonneg hrows
  intro fuel
  induction fuel with
  | zero =>
      intro N X Y T hT
      simp only [HintParams.tree] at hT
      exact absurd hT (by simp)
  | succ f ih =>
      intro N X Y T hT hN1 hNn hXN hYN
      cases hr : P.rule N X Y with
      | cheap =>
          simp only [HintParams.tree, hr] at hT
          have hTe : T = .cr N (HintParams.D N X Y) := Option.some.inj hT.symm
          rw [hTe]
          simpa only [Node.nodeCount, Nat.cast_one, mul_one] using
            len_cheap_le (KCR := KCR) (K := K) (P := P) hK hn hNn hYN hr hrows0
      | small =>
          simp only [HintParams.tree, hr] at hT
          have hTe : T = .cr N (HintParams.D N X Y) := Option.some.inj hT.symm
          rw [hTe]
          simpa only [Node.nodeCount, Nat.cast_one, mul_one] using
            len_small_le (KCR := KCR) (K := K) (P := P) hA hC hK hKCR hn hlam hNn hYN hr hrows0
      | direct =>
          simp only [HintParams.tree, hr] at hT
          have hTe : T = .direct (P.scheme N X Y) (P.resid N X Y) := Option.some.inj hT.symm
          rw [hTe]
          simpa only [Node.nodeCount, Nat.cast_one, mul_one] using
            len_direct_le (KCR := KCR) (K := K) (P := P) hA hC hK hKCR hn hlam hN1 hNn hXN hYN
              hr hrows0
      | recursive =>
          simp only [HintParams.tree, hr] at hT
          obtain ⟨chi, hsome, hT'⟩ := Option.map_eq_some_iff.mp hT
          rw [← hT']
          have hY1 : 1 ≤ Y :=
            one_le_Y_of_recursive (one_le_lg hn) (rule_recursive_spec hr).1 (rule_recursive_spec hr).2.2
          refine len_recursive_le (KCR := KCR) (K := K) (P := P) hA hC hK hKCR hK₅₉ hn hlam
            hN1 hNn hXN hYN hr hrows chi ?_
          intro s
          exact ih Y (P.capX N X Y s.val) (P.capY N X Y s.val) (chi s)
            (allSome_spec _ _ hsome s) hY1 (le_trans hYN hNn) (min_le_left _ _) (min_le_left _ _)

/-- `hintLenK` dominates Lemma 5.9's hidden constant. -/
theorem hintLenK₅₉_le (KCR : ℝ) : hintLenK₅₉ KCR ≤ hintLenK KCR := by
  have h1 : (0 : ℝ) < hintLenK₅₉ KCR := (Classical.choose_spec (LinearSetReconciliation327.Main.HintUpstream59.lemma_5_9 KCR)).1
  have h2 : (0 : ℝ) < hintLenK₁₀ := (Classical.choose_spec LinearSetReconciliation327.Main.HintUpstream510.lemma_5_10).1
  have h3 : (0 : ℝ) ≤ max KCR 0 := le_max_right _ _
  unfold hintLenK
  linarith only [h2, h3]

/-- `hintLenK` dominates Lemma 5.10's hidden constant. -/
theorem hintLenK₁₀_le (KCR : ℝ) : hintLenK₁₀ ≤ hintLenK KCR := by
  have h1 : (0 : ℝ) < hintLenK₅₉ KCR := (Classical.choose_spec (LinearSetReconciliation327.Main.HintUpstream59.lemma_5_9 KCR)).1
  have h3 : (0 : ℝ) ≤ max KCR 0 := le_max_right _ _
  unfold hintLenK
  linarith only [h1, h3]

/-- Theorem 5.1, conjunct 4, as in the paper (`eq:hint-forest-length`):

  `Len ≤ (1 + C₁/log n)(X + αh_N(Y)) + C₂N/log⁸n + C₃λlog^{p₁}n`. -/
theorem hintLengthOK {KCR : ℝ} :
    ∃ K : ℝ, 0 < K ∧ KCR ≤ K ∧
      ∀ (n lam N X Y : ℕ) (CR : CRFamily),
        (∀ N' t : ℕ, t ≤ N' → (CR.rows N' t : ℝ) ≤ KCR * ((t : ℝ) * lg ((N' : ℝ) + 2) ^ 2)) →
        (hintP KCR n lam).NodeArgs N X Y →
        ∀ (fuel : ℕ) (T : Node), (hintP KCR n lam).tree fuel N X Y = some T →
          HintLengthOK (hintLenK KCR) KCR CR T n lam N X Y := by
  refine ⟨hintLenK KCR, hintLenK_pos KCR, KCR_le_hintLenK KCR, ?_⟩
  intro n lam N X Y CR hrows hargs fuel T hT
  have hargs' := hargs
  obtain ⟨hn, hlam, hN1, hNn, hXN, hYN⟩ := hargs
  have hinv := len_le_charge (KCR := KCR) (K := hintLenK KCR) (hintLenK_pos KCR)
    (KCR_le_hintLenK KCR) (hintLenK₅₉_le KCR) hrows (hintP KCR n lam) rfl rfl hn hlam
    fuel N X Y T hT hN1 hNn hXN hYN
  -- Lemma 5.10's node count, moved to this `fuel` by `tree_mono`
  obtain ⟨f₀, T₀, hT₀, -, -, -, hnc₀⟩ := lemma_5_10_at (KCR := KCR) n lam N X Y hargs'
  have hmax : (hintP KCR n lam).tree (max fuel f₀) N X Y = some T :=
    tree_mono (hintP KCR n lam) fuel N X Y hT (max fuel f₀) (le_max_left _ _)
  have hmax0 : (hintP KCR n lam).tree (max fuel f₀) N X Y = some T₀ :=
    tree_mono (hintP KCR n lam) f₀ N X Y hT₀ (max fuel f₀) (le_max_right _ _)
  have hTT : T = T₀ := Option.some.inj (by rw [← hmax, ← hmax0])
  have hnc : (T.nodeCount : ℝ) ≤ hintLenK₁₀ * (hintLenA KCR : ℝ) * lg n ^ 27 := by
    rw [hTT]
    exact hnc₀
  -- the `nodeCount` factor is absorbed by `hintLenC₃'` and `hintLenP₁ = q + 27`
  have hK10 : hintLenK₁₀ ≤ ((⌈hintLenK KCR⌉₊ : ℕ) : ℝ) + 1 := by
    have h1 : hintLenK₁₀ ≤ hintLenK KCR := hintLenK₁₀_le KCR
    have h2 : hintLenK KCR ≤ ((⌈hintLenK KCR⌉₊ : ℕ) : ℝ) := Nat.le_ceil _
    linarith only [h1, h2]
  have hA1 : (hintLenA KCR : ℝ) ≤ (hintLenA KCR : ℝ) + 1 := by linarith only []
  have hKA : hintLenK₁₀ * (hintLenA KCR : ℝ)
      ≤ (((⌈hintLenK KCR⌉₊ : ℕ) : ℝ) + 1) * ((hintLenA KCR : ℝ) + 1) := by
    have h0 : (0 : ℝ) ≤ (hintLenA KCR : ℝ) := by positivity
    have h1 : (0 : ℝ) ≤ ((⌈hintLenK KCR⌉₊ : ℕ) : ℝ) + 1 := by
      have hc : (0 : ℝ) ≤ ((⌈hintLenK KCR⌉₊ : ℕ) : ℝ) := by positivity
      linarith only [hc]
    calc hintLenK₁₀ * (hintLenA KCR : ℝ)
        ≤ (((⌈hintLenK KCR⌉₊ : ℕ) : ℝ) + 1) * (hintLenA KCR : ℝ) :=
          mul_le_mul_of_nonneg_right hK10 h0
      _ ≤ (((⌈hintLenK KCR⌉₊ : ℕ) : ℝ) + 1) * ((hintLenA KCR : ℝ) + 1) :=
          mul_le_mul_of_nonneg_left hA1 h1
  have hbucket : hintLenC₃ KCR (hintLenK KCR) * (lam : ℝ) * lg n ^ hintLenQ KCR * (T.nodeCount : ℝ)
      ≤ hintLenC₃' KCR (hintLenK KCR) * (lam : ℝ) * lg n ^ hintLenP₁ KCR := by
    have hL1 : (1 : ℝ) ≤ lg n := one_le_lg hn
    have hL0 : (0 : ℝ) < lg n := by linarith only [hL1]
    have hLn : (0 : ℝ) ≤ lg n := le_of_lt hL0
    have hC30 : (0 : ℝ) ≤ hintLenC₃ KCR (hintLenK KCR) :=
      hintLenC₃_nonneg KCR (hintLenK_pos KCR)
    have hlam0 : (0 : ℝ) ≤ (lam : ℝ) := by positivity
    have hLq0 : (0 : ℝ) ≤ lg n ^ hintLenQ KCR := pow_nonneg hLn _
    have hL27 : (0 : ℝ) ≤ lg n ^ 27 := pow_nonneg hLn 27
    have h0 : (0 : ℝ) ≤ hintLenC₃ KCR (hintLenK KCR) * (lam : ℝ) * lg n ^ hintLenQ KCR :=
      mul_nonneg (mul_nonneg hC30 hlam0) hLq0
    have h1 : hintLenC₃ KCR (hintLenK KCR) * (lam : ℝ) * lg n ^ hintLenQ KCR * (T.nodeCount : ℝ)
        ≤ hintLenC₃ KCR (hintLenK KCR) * (lam : ℝ) * lg n ^ hintLenQ KCR *
            (hintLenK₁₀ * (hintLenA KCR : ℝ) * lg n ^ 27) := mul_le_mul_of_nonneg_left hnc h0
    have h2 : hintLenC₃ KCR (hintLenK KCR) * (lam : ℝ) * lg n ^ hintLenQ KCR *
          (hintLenK₁₀ * (hintLenA KCR : ℝ) * lg n ^ 27)
        ≤ hintLenC₃ KCR (hintLenK KCR) * (lam : ℝ) * lg n ^ hintLenQ KCR *
            ((((⌈hintLenK KCR⌉₊ : ℕ) : ℝ) + 1) * ((hintLenA KCR : ℝ) + 1) * lg n ^ 27) := by
      have hk : hintLenK₁₀ * (hintLenA KCR : ℝ) * lg n ^ 27
          ≤ (((⌈hintLenK KCR⌉₊ : ℕ) : ℝ) + 1) * ((hintLenA KCR : ℝ) + 1) * lg n ^ 27 := by
        calc hintLenK₁₀ * (hintLenA KCR : ℝ) * lg n ^ 27
            ≤ ((((⌈hintLenK KCR⌉₊ : ℕ) : ℝ) + 1) * ((hintLenA KCR : ℝ) + 1)) * lg n ^ 27 :=
              mul_le_mul_of_nonneg_right hKA hL27
          _ = (((⌈hintLenK KCR⌉₊ : ℕ) : ℝ) + 1) * ((hintLenA KCR : ℝ) + 1) * lg n ^ 27 := by ring
      exact mul_le_mul_of_nonneg_left hk h0
    have h3 : hintLenC₃ KCR (hintLenK KCR) * (lam : ℝ) * lg n ^ hintLenQ KCR *
          ((((⌈hintLenK KCR⌉₊ : ℕ) : ℝ) + 1) * ((hintLenA KCR : ℝ) + 1) * lg n ^ 27)
        = hintLenC₃' KCR (hintLenK KCR) * (lam : ℝ) * (lg n ^ hintLenQ KCR * lg n ^ 27) := by
      unfold hintLenC₃'
      push_cast
      try ring
    have h4 : lg n ^ hintLenQ KCR * lg n ^ 27 = lg n ^ hintLenP₁ KCR := by
      rw [← pow_add, hintLenP₁]
    rw [h3, h4] at h2
    exact le_trans h1 h2
  have hgoal := hinv
  simp only [hintP, HintParams.lgn, HintLengthOK] at hgoal ⊢
  linarith only [hgoal, hbucket]

/-! ## 9h. Conjunct 5: polylogarithmic column locality

A toggle `e_i` is stored as the column `H e_i` of the flat sketch.  Walking down the recursion tree,
the input of a node is always either empty or a singleton (the row that contains the toggled
coordinate): a row whose row-local image is empty has `code j β ∅ s = 0` by linearity, and only the
row containing the coordinate can have a nonempty image.  So at each node the toggle hits

* at most `ℓ_v` of the node's own stored column bits (only one row can be nonzero, and a row has `ℓ_v`
  columns), and
* at most `|CR.col N_v t_v i|` residual `CR` rows,

and each child of a recursive node receives a set of at most one row, so the induction applies to the
children.  Summing over all `nodeCount T` nodes and using the sharp `ℓ_v ≤ (E+1)log³n` of equation
(16) together with the *column* sparsity of Proposition 2.3 (`|CR.col N t i| ≤ KCR log²(N+2)`) gives
`O(log³⁰ n)`, hence `≤ Cu log^{pu} n` with `Cu = 2^30(K+1)^4` and `pu = 1024`.

No `depth` factor is needed here: the `nodeCount ≤ K·A·log²⁷n` bound of Lemma 5.10 is already
polylogarithmic, so the `log log n` of the depth never appears (the path-sum formulation would waste it,
but `pu = 1024` absorbs it anyway). -/

/-! ### 9h.1 The counted object: the flat sketch of a set -/

/-- The support of a single coordinate. -/
lemma support_single {N : ℕ} (i : Fin N) :
    support (Pi.single i (1 : ZMod 2)) = ({i.val} : Finset ℕ) := by
  ext a
  simp only [support, mem_image, mem_filter, mem_univ, true_and, mem_singleton]
  constructor
  · rintro ⟨j, hj, rfl⟩
    by_contra h
    have hne : j ≠ i := fun he => h (by rw [he])
    rw [Pi.single_eq_of_ne hne] at hj
    exact zero_ne_one hj
  · intro h
    exact ⟨i, Pi.single_eq_same i 1, h.symm⟩
/-- The stored bits of the tree that are `1` on the input `x`. -/
noncomputable def colSupp (CR : CRFamily) (T : Node) (r : Node.Seed T) (x : Finset ℕ) :
    Finset (Fin (synLen CR T)) :=
  univ.filter fun p => bitVal CR T r p x = 1

/-- The weight of the sketch column indexed by `x`: the number of stored bits it toggles.  For the
singleton `{i}` this is the weight of the column `H e_i`. -/
noncomputable def colWeight (CR : CRFamily) (T : Node) (r : Node.Seed T) (x : Finset ℕ) : ℕ :=
  ∑ p : Fin (synLen CR T), (bitVal CR T r p x).val

/-- The value of an indicator is the indicator. -/
lemma val_ite_one (c : Prop) [Decidable c] :
    ((if c then (1 : ZMod 2) else 0)).val = if c then 1 else 0 := by
  by_cases h : c
  · rw [if_pos h, if_pos h]
    exact ZMod.val_one 2
  · rw [if_neg h, if_neg h]
    exact ZMod.val_zero

/-- A `ZMod 2` element is determined by its value. -/
lemma zmod2_val_eq_ite (a : ZMod 2) : a.val = if a = 1 then 1 else 0 := by
  rcases zmod2_eq_zero_or_one a with h | h
  · rw [h]
    rw [if_neg zero_ne_one]
    exact ZMod.val_zero
  · rw [h]
    rw [if_pos rfl]
    exact ZMod.val_one 2

/-- `a.val ≤ 1` for `a : ZMod 2`. -/
lemma zmod2_val_le_one (a : ZMod 2) : a.val ≤ 1 := by
  have h := ZMod.val_lt a
  omega

/-- `colWeight` is the cardinality of `colSupp`. -/
lemma colWeight_eq_card (CR : CRFamily) (T : Node) (r : Node.Seed T) (x : Finset ℕ) :
    colWeight CR T r x = (colSupp CR T r x).card := by
  unfold colWeight colSupp
  rw [Finset.card_filter]
  exact Finset.sum_congr rfl (fun p _ => zmod2_val_eq_ite _)

/-- The empty input toggles no bit. -/
lemma colWeight_empty (CR : CRFamily) (T : Node) (r : Node.Seed T) :
    colWeight CR T r ∅ = 0 := by
  unfold colWeight
  apply Finset.sum_eq_zero
  intro p _
  rw [bitVal_empty]
  exact ZMod.val_zero

/-- Splitting a sum over `Fin (A+B)` through `Fin.append`. -/
lemma sum_append_val {A B : ℕ} (u : Fin A → ZMod 2) (v : Fin B → ZMod 2) :
    (∑ p : Fin (A + B), (Fin.append u v p).val) =
      (∑ a : Fin A, (u a).val) + ∑ b : Fin B, (v b).val := by
  rw [Fin.sum_univ_add]
  simp only [Fin.append_left, Fin.append_right]

/-- Reindexing a sum over `Fin (m·ℓ)` by rows and columns. -/
lemma sum_fin_prod {m ℓ : ℕ} (F : Fin m → Fin ℓ → ℕ) :
    (∑ q : Fin (m * ℓ), F (finProdFinEquiv.symm q).1 (finProdFinEquiv.symm q).2) =
      ∑ j : Fin m, ∑ s : Fin ℓ, F j s := by
  have h1 : (∑ q : Fin (m * ℓ), F (finProdFinEquiv.symm q).1 (finProdFinEquiv.symm q).2)
      = ∑ p : Fin m × Fin ℓ, F p.1 p.2 :=
    Equiv.sum_comp finProdFinEquiv.symm (fun p : Fin m × Fin ℓ => F p.1 p.2)
  rw [h1, Fintype.sum_prod_type]

/-- Reindexing a sum over `Fin (∑ s, f s)` by the children. -/
lemma sum_fin_sigma {ℓ : ℕ} (f : Fin ℓ → ℕ) (H : ((s : Fin ℓ) × Fin (f s)) → ℕ) :
    (∑ q : Fin (∑ s, f s), H (finSigmaFinEquiv.symm q)) =
      ∑ s : Fin ℓ, ∑ q : Fin (f s), H ⟨s, q⟩ := by
  have h1 : (∑ q : Fin (∑ s, f s), H (finSigmaFinEquiv.symm q))
      = ∑ p : ((s : Fin ℓ) × Fin (f s)), H p :=
    Equiv.sum_comp finSigmaFinEquiv.symm H
  rw [h1, Fintype.sum_sigma]

/-- A set of natural numbers is a subset of `{a}` at most. -/
lemma card_fin_mem_le {R : ℕ} {S : Finset ℕ} :
    (univ.filter fun p : Fin R => (p.val : ℕ) ∈ S).card ≤ S.card := by
  have h1 : (univ.filter fun p : Fin R => (p.val : ℕ) ∈ S).card
      = ((univ.filter fun p : Fin R => (p.val : ℕ) ∈ S).image Fin.val).card := by
    rw [Finset.card_image_of_injective _ (fun x y h => Fin.ext h)]
  rw [h1]
  exact Finset.card_le_card (fun v hv => by
    obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hv
    exact (Finset.mem_filter.mp hp).2)

/-- The CR syndrome of a singleton is the set of rows of that coordinate, restricted to the sketch. -/
lemma cr_sketch_singleton (CR : CRFamily) (N t a : ℕ) :
    CR.sketch N t ({a} : Finset ℕ) =
      (range (CR.rows N t)).filter (fun r => r ∈ CR.col N t a) := by
  ext r
  have hf : (({a} : Finset ℕ).filter (fun i => r ∈ CR.col N t i)) =
      if r ∈ CR.col N t a then ({a} : Finset ℕ) else ∅ := by
    ext i
    by_cases hi : i = a <;> by_cases h : r ∈ CR.col N t a <;> simp [hi, h]
  have hc : (({a} : Finset ℕ).filter (fun i => r ∈ CR.col N t i)).card =
      if r ∈ CR.col N t a then 1 else 0 := by
    rw [hf]
    by_cases h : r ∈ CR.col N t a <;> simp [h]
  rw [CRFamily.sketch, mem_filter, mem_filter, hc]
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨h1, ?_⟩
    by_contra h
    rw [if_neg h] at h2
    obtain ⟨k, hk⟩ := h2
    omega
  · rintro ⟨h1, h2⟩
    refine ⟨h1, ?_⟩
    rw [if_pos h2]
    exact ⟨0, by norm_num⟩

/-- The residual contribution of a singleton input at a `cr` node. -/
lemma cr_col_weight_le (CR : CRFamily) (N t a : ℕ) :
    (univ.filter fun q : Fin (CR.rows N t) =>
        (q.val : ℕ) ∈ CR.sketch N t ({a} : Finset ℕ)).card ≤ (CR.col N t a).card := by
  calc (univ.filter fun q : Fin (CR.rows N t) =>
        (q.val : ℕ) ∈ CR.sketch N t ({a} : Finset ℕ)).card
      ≤ (CR.sketch N t ({a} : Finset ℕ)).card := card_fin_mem_le
    _ ≤ (CR.col N t a).card := by
        rw [cr_sketch_singleton]
        exact Finset.card_le_card (fun v hv => (Finset.mem_filter.mp hv).2)

/-- The residual sum of a singleton input (as it appears in the `direct`/`recursive` cases). -/
lemma sum_fin_sketch_le_col (CR : CRFamily) (N t a : ℕ) :
    (∑ q : Fin (CR.rows N t),
        ((if (q.val : ℕ) ∈ CR.sketch N t ({a} : Finset ℕ) then (1 : ZMod 2) else 0)).val)
      ≤ (CR.col N t a).card := by
  have h1 : (∑ q : Fin (CR.rows N t),
        ((if (q.val : ℕ) ∈ CR.sketch N t ({a} : Finset ℕ) then (1 : ZMod 2) else 0)).val)
      = (univ.filter fun q : Fin (CR.rows N t) =>
          (q.val : ℕ) ∈ CR.sketch N t ({a} : Finset ℕ)).card := by
    rw [show (∑ q : Fin (CR.rows N t),
        ((if (q.val : ℕ) ∈ CR.sketch N t ({a} : Finset ℕ) then (1 : ZMod 2) else 0)).val)
        = ∑ q : Fin (CR.rows N t),
          (if (q.val : ℕ) ∈ CR.sketch N t ({a} : Finset ℕ) then (1 : ℕ) else 0) from
        Finset.sum_congr rfl (fun q _ => val_ite_one _)]
    rw [Finset.card_filter]
  rw [h1]
  exact cr_col_weight_le CR N t a

/-! ### 9h.2 The per-node counting lemma -/

/-- `code j β ∅ s = 0`: the empty set has empty row code. -/
lemma code_empty (sch : RowScheme) (j : Fin sch.m) (β : sch.Rand) (s : Fin sch.ℓ) :
    sch.code j β (∅ : Finset ℕ) s = 0 := by
  have h := sch.code_linear j β ∅ ∅ s
  rw [show symmDiff (∅ : Finset ℕ) ∅ = ∅ from by simp [symmDiff_def]] at h
  have h2 : sch.code j β (∅ : Finset ℕ) s + sch.code j β ∅ s = 0 := CharTwo.add_self_eq_zero _
  rw [h2] at h
  exact h

/-- The row-local image of a singleton `{a}`. -/
lemma rowImage_singleton {N m : ℕ} (π : Equiv.Perm (Fin N)) {a : ℕ} (ha : a < N) (j : ℕ) :
    rowImage N m π j ({a} : Finset ℕ) =
      (if (π ⟨a, ha⟩).val % m = j then {(π ⟨a, ha⟩).val / m} else ∅) := by
  classical
  ext v
  simp only [rowImage, mem_image, mem_filter, mem_univ, true_and, mem_singleton]
  by_cases hj : (π ⟨a, ha⟩).val % m = j
  · rw [if_pos hj, mem_singleton]
    constructor
    · rintro ⟨i, ⟨hi, hrow⟩, hv⟩
      have hia : i = ⟨a, ha⟩ := Fin.ext hi
      rw [hia] at hrow hv
      exact hv.symm
    · intro hv
      refine ⟨⟨a, ha⟩, ⟨rfl, hj⟩, ?_⟩
      exact hv.symm
  · rw [if_neg hj]
    constructor
    · rintro ⟨i, ⟨hi, hrow⟩, -⟩
      have hia : i = ⟨a, ha⟩ := Fin.ext hi
      rw [hia] at hrow
      exact absurd hrow hj
    · intro h
      exact absurd h (by simp)

/-- The column of a singleton input is a subset of `[m]`. -/
lemma column_subset_range (sch : RowScheme) (lr : sch.LocalSeed) (x : Finset ℕ) (s : Fin sch.ℓ) :
    sch.column lr x s ⊆ range sch.m := by
  intro v hv
  unfold RowScheme.column RowScheme.rowsWhere at hv
  rw [mem_image] at hv
  obtain ⟨j, -, rfl⟩ := hv
  exact mem_range.mpr j.isLt

/-- The column of a singleton input has at most one row. -/
lemma column_card_le_one (sch : RowScheme) (lr : sch.LocalSeed) {a : ℕ} (ha : a < sch.N)
    (s : Fin sch.ℓ) : (sch.column lr ({a} : Finset ℕ) s).card ≤ 1 := by
  rcases Nat.eq_zero_or_pos sch.m with hm | hm
  · have hz : sch.column lr ({a} : Finset ℕ) s = ∅ := by
      ext v
      constructor
      · intro hv
        have h := column_subset_range sch lr ({a} : Finset ℕ) s hv
        rw [hm] at h
        exact absurd h (by simp)
      · intro hv
        exact absurd hv (by simp)
    rw [hz]
    simp
  · let j0 : Fin sch.m := ⟨(lr.1 ⟨a, ha⟩).val % sch.m, Nat.mod_lt _ hm⟩
    have hsub2 : (sch.column lr ({a} : Finset ℕ) s) ⊆ ({j0.val} : Finset ℕ) := by
      intro v hv
      unfold RowScheme.column RowScheme.rowsWhere at hv
      rw [mem_image] at hv
      obtain ⟨j, hj, rfl⟩ := hv
      rw [mem_singleton]
      have hcode : sch.code j (lr.2 j) (sch.rowOf lr ({a} : Finset ℕ) j) s = 1 := by
        have h := (@Finset.mem_filter (Fin sch.m)
          (fun j => sch.code j (lr.2 j) (sch.rowOf lr ({a} : Finset ℕ) j) s = 1)
          (fun j => Classical.propDecidable
            (sch.code j (lr.2 j) (sch.rowOf lr ({a} : Finset ℕ) j) s = 1))
          Finset.univ j).mp hj
        exact h.2
      by_contra hne
      have hrow : sch.rowOf lr ({a} : Finset ℕ) j = ∅ := by
        unfold RowScheme.rowOf
        rw [rowImage_singleton lr.1 ha j.val]
        have hcond : ¬ ((lr.1 ⟨a, ha⟩).val % sch.m = j.val) := fun h => hne h.symm
        rw [if_neg hcond]
      rw [hrow, code_empty] at hcode
      exact zero_ne_one hcode
    calc (sch.column lr ({a} : Finset ℕ) s).card
        ≤ ({j0.val} : Finset ℕ).card := Finset.card_le_card hsub2
      _ = 1 := Finset.card_singleton _

/-- The column of the empty input is empty. -/
lemma column_empty (sch : RowScheme) (lr : sch.LocalSeed) (s : Fin sch.ℓ) :
    sch.column lr (∅ : Finset ℕ) s = ∅ := by
  ext v
  simp [RowScheme.column, RowScheme.rowsWhere, RowScheme.rowOf, rowImage, code_empty]

/-- The per-node data the column-locality induction needs: a bound `Bℓ` on every node's number of
columns, a bound `Bc` on the number of residual `CR` rows hit by any coordinate, and the well-formedness
`(child s).N = sch.m` at recursive nodes (which is how the child's input, a subset of `[sch.m]`, is a
legitimate input for the child). -/
def ColNodeOK (CR : CRFamily) (Bℓ Bc : ℕ) : Node → Prop
  | .store _ => True
  | .cr N t => ∀ a : ℕ, (CR.col N t a).card ≤ Bc
  | .direct sch t => sch.ℓ ≤ Bℓ ∧ ∀ a : ℕ, (CR.col sch.N t a).card ≤ Bc
  | .recursive sch t _ _ child =>
      sch.ℓ ≤ Bℓ ∧ (∀ a : ℕ, (CR.col sch.N t a).card ≤ Bc) ∧
        (∀ s, (child s).N = sch.m) ∧ ∀ s, ColNodeOK CR Bℓ Bc (child s)

/-- **Per-node column accounting.**  If every node has at most `Bℓ` columns, every coordinate hits at
most `Bc` residual `CR` rows, and the children of a recursive node live on `[m_v]`, then the flat sketch
of a singleton input toggles at most `nodeCount T · (Bℓ + Bc)` bits. -/
lemma colWeight_singleton_le (CR : CRFamily) (Bℓ Bc : ℕ) (hB : 1 ≤ Bℓ) :
    ∀ (T : Node), ColNodeOK CR Bℓ Bc T → ∀ (r : Node.Seed T) (a : ℕ), a < T.N →
      colWeight CR T r ({a} : Finset ℕ) ≤ T.nodeCount * (Bℓ + Bc) := by
  intro T
  induction T with
  | store N =>
      intro _ r a ha
      have h1 : colWeight CR (.store N) r ({a} : Finset ℕ) ≤ 1 := by
        rw [colWeight_eq_card]
        have hsub : colSupp CR (.store N) r ({a} : Finset ℕ) ⊆
            (univ.filter fun p : Fin (synLen CR (.store N)) =>
              (p.val : ℕ) ∈ ({a} : Finset ℕ)) := by
          intro p hp
          rw [mem_filter]
          refine ⟨mem_univ _, ?_⟩
          unfold colSupp at hp
          rw [mem_filter] at hp
          obtain ⟨-, hp⟩ := hp
          by_contra hc
          have h0 : bitVal CR (.store N) r p ({a} : Finset ℕ) = 0 := by
            simp only [bitVal]
            rw [if_neg hc]
          rw [h0] at hp
          exact zero_ne_one hp
        calc (colSupp CR (.store N) r ({a} : Finset ℕ)).card
            ≤ (univ.filter fun p : Fin (synLen CR (.store N)) =>
                (p.val : ℕ) ∈ ({a} : Finset ℕ)).card := Finset.card_le_card hsub
          _ ≤ ({a} : Finset ℕ).card := card_fin_mem_le
          _ = 1 := Finset.card_singleton a
      calc colWeight CR (.store N) r ({a} : Finset ℕ) ≤ 1 := h1
        _ ≤ (Node.store N).nodeCount * (Bℓ + Bc) := by
            simp only [Node.nodeCount, Nat.one_mul]
            omega
  | cr N t =>
      intro hT r a ha
      have h1 : colWeight CR (.cr N t) r ({a} : Finset ℕ)
          = (colSupp CR (.cr N t) r ({a} : Finset ℕ)).card := colWeight_eq_card _ _ _ _
      rw [h1]
      have hsub : colSupp CR (.cr N t) r ({a} : Finset ℕ) ⊆
          (univ.filter fun p : Fin (synLen CR (.cr N t)) => (p.val : ℕ) ∈ CR.col N t a) := by
        intro p hp
        rw [mem_filter]
        refine ⟨mem_univ _, ?_⟩
        unfold colSupp at hp
        rw [mem_filter] at hp
        obtain ⟨-, hp⟩ := hp
        by_contra hc
        have hnot : ¬ ((p.val : ℕ) ∈ CR.sketch N t ({a} : Finset ℕ)) := by
          intro h
          rw [cr_sketch_singleton, mem_filter] at h
          exact hc h.2
        have h0 : bitVal CR (.cr N t) r p ({a} : Finset ℕ) = 0 := by
          simp only [bitVal]
          rw [if_neg hnot]
        rw [h0] at hp
        exact zero_ne_one hp
      have h2 : (colSupp CR (.cr N t) r ({a} : Finset ℕ)).card ≤ Bc :=
        calc (colSupp CR (.cr N t) r ({a} : Finset ℕ)).card
            ≤ (univ.filter fun p : Fin (synLen CR (.cr N t)) => (p.val : ℕ) ∈ CR.col N t a).card :=
              Finset.card_le_card hsub
          _ ≤ (CR.col N t a).card := card_fin_mem_le
          _ ≤ Bc := hT a
      calc (colSupp CR (.cr N t) r ({a} : Finset ℕ)).card ≤ Bc := h2
        _ ≤ (Node.cr N t).nodeCount * (Bℓ + Bc) := by
            simp only [Node.nodeCount, Nat.one_mul]
            omega
  | direct sch t =>
      intro hT r a ha
      obtain ⟨hℓ, hcolB⟩ := hT
      have hsplit : colWeight CR (.direct sch t) r ({a} : Finset ℕ)
          = (∑ q : Fin (sch.m * sch.ℓ),
              ((fun sq : Fin sch.m × Fin sch.ℓ =>
                sch.code sq.1 (r.2 sq.1) (sch.rowOf r ({a} : Finset ℕ) sq.1) sq.2)
                (finProdFinEquiv.symm q)).val)
            + (∑ q : Fin (CR.rows sch.N t),
              ((if (q.val : ℕ) ∈ CR.sketch sch.N t ({a} : Finset ℕ) then (1 : ZMod 2) else 0)).val) := by
        unfold colWeight
        simp only [bitVal, synLen]
        exact sum_append_val _ _
      have hleft : (∑ q : Fin (sch.m * sch.ℓ),
              ((fun sq : Fin sch.m × Fin sch.ℓ =>
                sch.code sq.1 (r.2 sq.1) (sch.rowOf r ({a} : Finset ℕ) sq.1) sq.2)
                (finProdFinEquiv.symm q)).val) ≤ sch.ℓ := by
        have hprod : (∑ q : Fin (sch.m * sch.ℓ),
              ((fun sq : Fin sch.m × Fin sch.ℓ =>
                sch.code sq.1 (r.2 sq.1) (sch.rowOf r ({a} : Finset ℕ) sq.1) sq.2)
                (finProdFinEquiv.symm q)).val)
            = ∑ j : Fin sch.m, ∑ s : Fin sch.ℓ,
                (sch.code j (r.2 j) (sch.rowOf r ({a} : Finset ℕ) j) s).val :=
          sum_fin_prod (F := fun j s =>
            (sch.code j (r.2 j) (sch.rowOf r ({a} : Finset ℕ) j) s).val)
        rw [hprod]
        by_cases hm : sch.m = 0
        · have h0 : (∑ j : Fin sch.m, ∑ s : Fin sch.ℓ,
                (sch.code j (r.2 j) (sch.rowOf r ({a} : Finset ℕ) j) s).val) = 0 := by
            apply Finset.sum_eq_zero
            intro j _
            exact absurd j.isLt (by omega)
          rw [h0]
          exact Nat.zero_le _
        · have hmpos : 0 < sch.m := Nat.pos_of_ne_zero hm
          let j0 : Fin sch.m := ⟨(r.1 ⟨a, ha⟩).val % sch.m, Nat.mod_lt _ hmpos⟩
          have hb : ∀ j : Fin sch.m, (∑ s : Fin sch.ℓ,
              (sch.code j (r.2 j) (sch.rowOf r ({a} : Finset ℕ) j) s).val)
              ≤ if j = j0 then sch.ℓ else 0 := by
            intro j
            by_cases hj : j = j0
            · rw [if_pos hj]
              calc (∑ s : Fin sch.ℓ,
                    (sch.code j (r.2 j) (sch.rowOf r ({a} : Finset ℕ) j) s).val)
                  ≤ ∑ _s : Fin sch.ℓ, 1 :=
                    Finset.sum_le_sum (fun s _ => zmod2_val_le_one _)
                _ = sch.ℓ := by simp
            · rw [if_neg hj]
              have hrow : sch.rowOf r ({a} : Finset ℕ) j = ∅ := by
                unfold RowScheme.rowOf
                rw [rowImage_singleton r.1 ha j.val]
                have hcond : ¬ ((r.1 ⟨a, ha⟩).val % sch.m = j.val) := fun h =>
                  hj (Fin.ext h.symm)
                rw [if_neg hcond]
              have hzero : (∑ s : Fin sch.ℓ,
                  (sch.code j (r.2 j) (sch.rowOf r ({a} : Finset ℕ) j) s).val) = 0 := by
                apply Finset.sum_eq_zero
                intro s _
                rw [hrow]
                rw [code_empty]
                exact ZMod.val_zero
              rw [hzero]
          calc (∑ j : Fin sch.m, ∑ s : Fin sch.ℓ,
                (sch.code j (r.2 j) (sch.rowOf r ({a} : Finset ℕ) j) s).val)
              ≤ ∑ j : Fin sch.m, (if j = j0 then sch.ℓ else 0) :=
                Finset.sum_le_sum (fun j _ => hb j)
            _ = sch.ℓ := by
                rw [Finset.sum_ite_eq']
                simp
      have hright : (∑ q : Fin (CR.rows sch.N t),
              ((if (q.val : ℕ) ∈ CR.sketch sch.N t ({a} : Finset ℕ) then (1 : ZMod 2) else 0)).val)
          ≤ Bc := le_trans (sum_fin_sketch_le_col CR sch.N t a) (hcolB a)
      have hstep : colWeight CR (.direct sch t) r ({a} : Finset ℕ) ≤ sch.ℓ + Bc := by
        rw [hsplit]
        exact Nat.add_le_add hleft hright
      calc colWeight CR (.direct sch t) r ({a} : Finset ℕ) ≤ sch.ℓ + Bc := hstep
        _ ≤ (Node.direct sch t).nodeCount * (Bℓ + Bc) := by
            simp only [Node.nodeCount, Nat.one_mul]
            omega
  | recursive sch t Xs Ys child ih =>
      intro hT r a ha
      obtain ⟨hℓ, hcolB, hNchild, hco⟩ := hT
      have hsplit : colWeight CR (.recursive sch t Xs Ys child) r ({a} : Finset ℕ)
          = (∑ q : Fin (∑ s : Fin sch.ℓ, synLen CR (child s)),
              ((fun sq : (s : Fin sch.ℓ) × Fin (synLen CR (child s)) =>
                bitVal CR (child sq.1) (r.2 sq.1) sq.2
                  (sch.column r.1 ({a} : Finset ℕ) sq.1))
                (finSigmaFinEquiv.symm q)).val)
            + (∑ q : Fin (CR.rows sch.N t),
              ((if (q.val : ℕ) ∈ CR.sketch sch.N t ({a} : Finset ℕ) then (1 : ZMod 2) else 0)).val) := by
        unfold colWeight
        simp only [bitVal, synLen]
        exact sum_append_val _ _
      have hS1 : (∑ q : Fin (∑ s : Fin sch.ℓ, synLen CR (child s)),
              ((fun sq : (s : Fin sch.ℓ) × Fin (synLen CR (child s)) =>
                bitVal CR (child sq.1) (r.2 sq.1) sq.2
                  (sch.column r.1 ({a} : Finset ℕ) sq.1))
                (finSigmaFinEquiv.symm q)).val)
          = ∑ s : Fin sch.ℓ,
              colWeight CR (child s) (r.2 s) (sch.column r.1 ({a} : Finset ℕ) s) := by
        have hsig : (∑ q : Fin (∑ s : Fin sch.ℓ, synLen CR (child s)),
              ((fun sq : (s : Fin sch.ℓ) × Fin (synLen CR (child s)) =>
                bitVal CR (child sq.1) (r.2 sq.1) sq.2
                  (sch.column r.1 ({a} : Finset ℕ) sq.1))
                (finSigmaFinEquiv.symm q)).val)
            = ∑ s : Fin sch.ℓ, ∑ q : Fin (synLen CR (child s)),
                (bitVal CR (child s) (r.2 s) q (sch.column r.1 ({a} : Finset ℕ) s)).val :=
          sum_fin_sigma (f := fun s => synLen CR (child s))
            (H := fun sq => (bitVal CR (child sq.1) (r.2 sq.1) sq.2
              (sch.column r.1 ({a} : Finset ℕ) sq.1)).val)
        rw [hsig]
        simp only [colWeight]
      have hchild : ∀ s : Fin sch.ℓ,
          colWeight CR (child s) (r.2 s) (sch.column r.1 ({a} : Finset ℕ) s)
            ≤ (child s).nodeCount * (Bℓ + Bc) := by
        intro s
        by_cases hzero : sch.column r.1 ({a} : Finset ℕ) s = ∅
        · rw [hzero, colWeight_empty]
          exact Nat.zero_le _
        · have hcard1 : (sch.column r.1 ({a} : Finset ℕ) s).card ≤ 1 :=
            column_card_le_one sch r.1 ha s
          have hpos : 0 < (sch.column r.1 ({a} : Finset ℕ) s).card :=
            Finset.card_pos.mpr (Finset.nonempty_iff_ne_empty.mpr hzero)
          have hcard : (sch.column r.1 ({a} : Finset ℕ) s).card = 1 := le_antisymm hcard1 hpos
          obtain ⟨b, hb⟩ := Finset.card_eq_one.mp hcard
          have hsub := column_subset_range sch r.1 ({a} : Finset ℕ) s
          rw [hb] at hsub
          have hbN : b < (child s).N := by
            rw [hNchild s]
            exact Finset.mem_range.mp (hsub (Finset.mem_singleton.mpr rfl))
          rw [hb]
          exact ih s (hco s) (r.2 s) b hbN
      have hsum : (∑ s : Fin sch.ℓ,
            colWeight CR (child s) (r.2 s) (sch.column r.1 ({a} : Finset ℕ) s))
          ≤ (∑ s : Fin sch.ℓ, (child s).nodeCount) * (Bℓ + Bc) := by
        rw [Finset.sum_mul]
        exact Finset.sum_le_sum (fun s _ => hchild s)
      have hright : (∑ q : Fin (CR.rows sch.N t),
              ((if (q.val : ℕ) ∈ CR.sketch sch.N t ({a} : Finset ℕ) then (1 : ZMod 2) else 0)).val)
          ≤ Bc := le_trans (sum_fin_sketch_le_col CR sch.N t a) (hcolB a)
      have hstep : colWeight CR (.recursive sch t Xs Ys child) r ({a} : Finset ℕ)
          ≤ (∑ s : Fin sch.ℓ, (child s).nodeCount) * (Bℓ + Bc) + Bc := by
        rw [hsplit, hS1]
        exact Nat.add_le_add hsum hright
      calc colWeight CR (.recursive sch t Xs Ys child) r ({a} : Finset ℕ)
          ≤ (∑ s : Fin sch.ℓ, (child s).nodeCount) * (Bℓ + Bc) + Bc := hstep
        _ ≤ (Node.recursive sch t Xs Ys child).nodeCount * (Bℓ + Bc) := by
            simp only [Node.nodeCount]
            rw [Nat.add_mul, Nat.one_mul]
            omega

/-! ### 9h.3 Sharp per-node sizes and the tree -/

/-- `1 ≤ P.rows X Y` at a `direct` node (`m ≠ Y` forces `⌈X/log³n⌉ > Y`). -/
lemma one_le_rows_of_ne {P : HintParams} {X Y : ℕ} (h : P.rows X Y ≠ Y) : 1 ≤ P.rows X Y := by
  unfold HintParams.rows at h ⊢
  by_cases hc : ⌈(X : ℝ) / P.lgn ^ 3⌉₊ = 0
  · rw [hc, Nat.max_zero] at h
    exact absurd rfl h
  · have h1 : 0 < ⌈(X : ℝ) / P.lgn ^ 3⌉₊ := Nat.pos_of_ne_zero hc
    exact le_trans h1 (le_max_right _ _)

/-- The universe of the tree `P.tree` produces is the `N` it is called on. -/
lemma tree_N (P : HintParams) (fuel : ℕ) :
    ∀ (N X Y : ℕ) (T : Node), P.tree fuel N X Y = some T → T.N = N := by
  induction fuel with
  | zero =>
      intro N X Y T h
      simp only [HintParams.tree] at h
      exact absurd h (by simp)
  | succ f ih =>
      intro N X Y T h
      simp only [HintParams.tree] at h
      cases hr : P.rule N X Y
      · simp only [hr] at h
        have hT : T = .cr N (HintParams.D N X Y) := by simpa using h.symm
        subst hT
        rfl
      · simp only [hr] at h
        have hT : T = .cr N (HintParams.D N X Y) := by simpa using h.symm
        subst hT
        rfl
      · simp only [hr] at h
        obtain ⟨child, -, hT⟩ := Option.map_eq_some_iff.mp h
        subst hT
        rfl
      · simp only [hr] at h
        have hT : T = .direct (P.scheme N X Y) (P.resid N X Y) := by simpa using h.symm
        subst hT
        rfl

/-- Sharp per-node size data: every node's universe is at most `n` and its number of columns is at
most `(E+1)log³n` (equation (16)); the children of a recursive node live on its row universe. -/
def NodeShrink (KCR : ℝ) (n : ℕ) : Node → Prop
  | .store N => N ≤ n
  | .cr N t => N ≤ n ∧ t ≤ N
  | .direct sch t => sch.N ≤ n ∧ t ≤ sch.N ∧
      (sch.ℓ : ℝ) ≤ ((hintLenE KCR : ℝ) + 1) * lg (n : ℝ) ^ 3
  | .recursive sch t _ _ child => sch.N ≤ n ∧ t ≤ sch.N ∧
      (sch.ℓ : ℝ) ≤ ((hintLenE KCR : ℝ) + 1) * lg (n : ℝ) ^ 3 ∧
      (∀ s, (child s).N = sch.m) ∧ ∀ s, NodeShrink KCR n (child s)

/-- The tree of `P.tree` satisfies the sharp per-node bounds. -/
lemma tree_shrink {KCR : ℝ} {P : HintParams} (hA : P.A = hintLenA KCR) (hC : P.C = hintLenC KCR)
    (hn : 2 ≤ P.n) :
    ∀ (fuel : ℕ) (N X Y : ℕ) (T : Node), P.tree fuel N X Y = some T →
      1 ≤ N → N ≤ P.n → X ≤ N → Y ≤ N → NodeShrink KCR P.n T := by
  intro fuel
  induction fuel with
  | zero =>
      intro N X Y T h
      simp only [HintParams.tree] at h
      exact absurd h (by simp)
  | succ f ih =>
      intro N X Y T h hN1 hNn hXN hYN
      simp only [HintParams.tree] at h
      have hL1 : (1 : ℝ) ≤ P.lgn := one_le_lg hn
      cases hr : P.rule N X Y
      · simp only [hr] at h
        have hT : T = .cr N (HintParams.D N X Y) := by simpa using h.symm
        subst hT
        exact ⟨hNn, min_le_left _ _⟩
      · simp only [hr] at h
        have hT : T = .cr N (HintParams.D N X Y) := by simpa using h.symm
        subst hT
        exact ⟨hNn, min_le_left _ _⟩
      · simp only [hr] at h
        obtain ⟨child, hsome, hT⟩ := Option.map_eq_some_iff.mp h
        subst hT
        have hrowsY : P.rows X Y = Y := (rule_recursive_spec hr).2.2
        have hY1 : 1 ≤ Y := one_le_Y_of_recursive hL1 (rule_recursive_spec hr).1 hrowsY
        have hell : ((P.scheme N X Y).ℓ : ℝ) ≤
            ((hintLenE KCR : ℝ) + 1) * lg (P.n : ℝ) ^ 3 := by
          have hm1 : 1 ≤ P.rows X Y := by rw [hrowsY]; exact hY1
          exact ell_le_cubic hA hC hn hN1 hNn hXN hYN hm1
        refine ⟨hNn, min_le_left _ _, hell, ?_, ?_⟩
        · intro s
          have h1 : (child s).N = Y :=
            tree_N P f Y (P.capX N X Y s.val) (P.capY N X Y s.val) (child s)
              (allSome_spec _ _ hsome s)
          rw [h1]
          exact hrowsY.symm
        · intro s
          exact ih Y (P.capX N X Y s.val) (P.capY N X Y s.val) (child s)
            (allSome_spec _ _ hsome s) hY1 (le_trans hYN hNn) (min_le_left _ _) (min_le_left _ _)
      · simp only [hr] at h
        have hT : T = .direct (P.scheme N X Y) (P.resid N X Y) := by simpa using h.symm
        subst hT
        have hmne : P.rows X Y ≠ Y := (rule_direct_spec hr).2.2
        have hm1 : 1 ≤ P.rows X Y := one_le_rows_of_ne hmne
        have hell : ((P.scheme N X Y).ℓ : ℝ) ≤
            ((hintLenE KCR : ℝ) + 1) * lg (P.n : ℝ) ^ 3 :=
          ell_le_cubic hA hC hn hN1 hNn hXN hYN hm1
        exact ⟨hNn, min_le_left _ _, hell⟩

/-- `Bℓ`: the sharp bound `(E+1)log³n` on the number of columns, rounded up. -/
noncomputable def colBℓ (KCR : ℝ) (n : ℕ) : ℕ :=
  ⌈((hintLenE KCR : ℝ) + 1) * lg (n : ℝ) ^ 3⌉₊

/-- `Bc`: the column sparsity `KCR log²(n+2)` of Proposition 2.3, rounded up. -/
noncomputable def colBc (KCR : ℝ) (n : ℕ) : ℕ :=
  ⌈max KCR 0 * lg ((n : ℝ) + 2) ^ 2⌉₊

/-- `Bℓ ≥ 1`. -/
lemma colBℓ_pos {KCR : ℝ} {n : ℕ} (hn : 2 ≤ n) : 1 ≤ colBℓ KCR n := by
  have hL1 : (1 : ℝ) ≤ lg (n : ℝ) := one_le_lg hn
  have hE0 : (0 : ℝ) ≤ (hintLenE KCR : ℝ) := by positivity
  have h3 : (1 : ℝ) ≤ lg (n : ℝ) ^ 3 := by
    calc (1 : ℝ) ≤ lg (n : ℝ) := hL1
      _ = lg (n : ℝ) ^ 1 := by simp
      _ ≤ lg (n : ℝ) ^ 3 := pow_le_pow_right₀ hL1 (by norm_num)
  have hx1 : (1 : ℝ) ≤ ((hintLenE KCR : ℝ) + 1) * lg (n : ℝ) ^ 3 := by
    nlinarith only [hE0, h3]
  have h2 : ((hintLenE KCR : ℝ) + 1) * lg (n : ℝ) ^ 3 ≤ ((colBℓ KCR n : ℕ) : ℝ) := by
    unfold colBℓ
    exact Nat.le_ceil _
  have h4 : (1 : ℝ) ≤ ((colBℓ KCR n : ℕ) : ℝ) := le_trans hx1 h2
  exact_mod_cast h4

/-- The column bound of a node, moved to the global universe `n` (using `N_v ≤ n`). -/
lemma col_card_le_ceil {KCR : ℝ} {N n : ℕ} {S : Finset ℕ}
    (h : (S.card : ℝ) ≤ KCR * lg ((N : ℝ) + 2) ^ 2) (hNn : N ≤ n) :
    S.card ≤ colBc KCR n := by
  have h2 : (S.card : ℝ) ≤ max KCR 0 * lg ((n : ℝ) + 2) ^ 2 := by
    have hL0 : (0 : ℝ) ≤ lg ((N : ℝ) + 2) := by
      apply lg_nonneg_of_one_le
      have h1 : (0 : ℝ) ≤ (N : ℝ) := by positivity
      linarith only [h1]
    have hmono : lg ((N : ℝ) + 2) ≤ lg ((n : ℝ) + 2) := by
      refine Real.logb_le_logb_of_le (by norm_num) (by positivity) ?_
      have h1 : (N : ℝ) ≤ (n : ℝ) := by exact_mod_cast hNn
      linarith only [h1]
    have hmono2 : lg ((N : ℝ) + 2) ^ 2 ≤ lg ((n : ℝ) + 2) ^ 2 := by
      nlinarith only [hmono, hL0]
    rcases lt_or_ge KCR 0 with hk | hk
    · have h0 : (0 : ℝ) ≤ lg ((N : ℝ) + 2) ^ 2 := by positivity
      have hneg : KCR * lg ((N : ℝ) + 2) ^ 2 ≤ 0 := by nlinarith only [hk, h0]
      have hle0 : (S.card : ℝ) ≤ 0 := le_trans h hneg
      have hge0 : (0 : ℝ) ≤ (S.card : ℝ) := by positivity
      have hz : (S.card : ℝ) = 0 := le_antisymm hle0 hge0
      rw [hz, max_eq_right (le_of_lt hk)]
      simp
    · rw [max_eq_left hk]
      exact le_trans h (mul_le_mul_of_nonneg_left hmono2 hk)
  have h3 : (S.card : ℝ) ≤ ((colBc KCR n : ℕ) : ℝ) := by
    refine le_trans h2 ?_
    unfold colBc
    exact Nat.le_ceil _
  exact_mod_cast h3

/-- The sharp per-node sizes give the hypotheses of the counting induction. -/
lemma colNodeOK_of_shrink {KCR : ℝ} {CR : CRFamily} {n : ℕ}
    (hcol : ∀ N' t : ℕ, t ≤ N' → ∀ a : ℕ,
      ((CR.col N' t a).card : ℝ) ≤ KCR * lg ((N' : ℝ) + 2) ^ 2) :
    ∀ T : Node, NodeShrink KCR n T → ColNodeOK CR (colBℓ KCR n) (colBc KCR n) T := by
  intro T
  induction T with
  | store N =>
      intro _
      trivial
  | cr N t =>
      intro h
      obtain ⟨hNn, ht⟩ := h
      intro a
      exact col_card_le_ceil (hcol N t ht a) hNn
  | direct sch t =>
      intro h
      obtain ⟨hNn, ht, hℓ⟩ := h
      refine ⟨?_, ?_⟩
      · have h1 : (sch.ℓ : ℝ) ≤ ((colBℓ KCR n : ℕ) : ℝ) := by
          refine le_trans hℓ ?_
          unfold colBℓ
          exact Nat.le_ceil _
        exact_mod_cast h1
      · intro a
        exact col_card_le_ceil (hcol sch.N t ht a) hNn
  | recursive sch t Xs Ys child ih =>
      intro h
      obtain ⟨hNn, ht, hℓ, hNchild, hco⟩ := h
      refine ⟨?_, ?_, hNchild, ?_⟩
      · have h1 : (sch.ℓ : ℝ) ≤ ((colBℓ KCR n : ℕ) : ℝ) := by
          refine le_trans hℓ ?_
          unfold colBℓ
          exact Nat.le_ceil _
        exact_mod_cast h1
      · intro a
        exact col_card_le_ceil (hcol sch.N t ht a) hNn
      · intro s
        exact ih s (hco s)

/-! ### 9h.4 The constants and the numeric endgame -/

/-- The `K` of conjunct 5: it dominates Lemma 5.10's node-count constant, the first scheme constant
`A` and the sharp column constant `E` of equation (16); all are absolute (functions of `KCR`). -/
noncomputable def hintColK (KCR : ℝ) : ℝ :=
  hintLenK KCR + (hintLenA KCR : ℝ) + (hintLenE KCR : ℝ) + 1

theorem hintColK_pos (KCR : ℝ) : 0 < hintColK KCR := by
  have h1 : 0 < hintLenK KCR := hintLenK_pos KCR
  have h2 : (0 : ℝ) ≤ (hintLenA KCR : ℝ) := by positivity
  have h3 : (0 : ℝ) ≤ (hintLenE KCR : ℝ) := by positivity
  unfold hintColK
  linarith only [h1, h2, h3]

theorem KCR_le_hintColK (KCR : ℝ) : KCR ≤ hintColK KCR := by
  have h1 := KCR_le_hintLenK KCR
  have h2 : (0 : ℝ) ≤ (hintLenA KCR : ℝ) := by positivity
  have h3 : (0 : ℝ) ≤ (hintLenE KCR : ℝ) := by positivity
  unfold hintColK
  linarith only [h1, h2, h3]

theorem hintLenK₁₀_le_hintColK (KCR : ℝ) : hintLenK₁₀ ≤ hintColK KCR := by
  have h1 : (0 : ℝ) < hintLenK₅₉ KCR := (Classical.choose_spec (LinearSetReconciliation327.Main.HintUpstream59.lemma_5_9 KCR)).1
  have h2 : (0 : ℝ) < hintLenK₁₀ := (Classical.choose_spec LinearSetReconciliation327.Main.HintUpstream510.lemma_5_10).1
  have h3 : (0 : ℝ) ≤ max KCR 0 := le_max_right _ _
  have h4 : (0 : ℝ) ≤ (hintLenA KCR : ℝ) := by positivity
  have h5 : (0 : ℝ) ≤ (hintLenE KCR : ℝ) := by positivity
  unfold hintColK hintLenK
  linarith only [h1, h2, h3, h4, h5]

theorem hintLenA_le_hintColK (KCR : ℝ) : (hintLenA KCR : ℝ) ≤ hintColK KCR := by
  have h1 : (0 : ℝ) < hintLenK₅₉ KCR := (Classical.choose_spec (LinearSetReconciliation327.Main.HintUpstream59.lemma_5_9 KCR)).1
  have h2 : (0 : ℝ) < hintLenK₁₀ := (Classical.choose_spec LinearSetReconciliation327.Main.HintUpstream510.lemma_5_10).1
  have h3 : (0 : ℝ) ≤ max KCR 0 := le_max_right _ _
  have h4 : (0 : ℝ) ≤ (hintLenE KCR : ℝ) := by positivity
  unfold hintColK hintLenK
  linarith only [h1, h2, h3, h4]

theorem hintLenE_le_hintColK (KCR : ℝ) : (hintLenE KCR : ℝ) ≤ hintColK KCR := by
  have h1 : (0 : ℝ) < hintLenK₅₉ KCR := (Classical.choose_spec (LinearSetReconciliation327.Main.HintUpstream59.lemma_5_9 KCR)).1
  have h2 : (0 : ℝ) < hintLenK₁₀ := (Classical.choose_spec LinearSetReconciliation327.Main.HintUpstream510.lemma_5_10).1
  have h3 : (0 : ℝ) ≤ max KCR 0 := le_max_right _ _
  have h4 : (0 : ℝ) ≤ (hintLenA KCR : ℝ) := by positivity
  unfold hintColK hintLenK
  linarith only [h1, h2, h3, h4]

theorem maxKCR_le_hintColK (KCR : ℝ) : max KCR 0 ≤ hintColK KCR := by
  have h1 : (0 : ℝ) < hintLenK₅₉ KCR := (Classical.choose_spec (LinearSetReconciliation327.Main.HintUpstream59.lemma_5_9 KCR)).1
  have h2 : (0 : ℝ) < hintLenK₁₀ := (Classical.choose_spec LinearSetReconciliation327.Main.HintUpstream510.lemma_5_10).1
  have h4 : (0 : ℝ) ≤ (hintLenA KCR : ℝ) := by positivity
  have h5 : (0 : ℝ) ≤ (hintLenE KCR : ℝ) := by positivity
  unfold hintColK hintLenK
  linarith only [h1, h2, h4, h5]

/-- `Bℓ + Bc ≤ (E + 4KCR + 3) log³n`. -/
lemma colB_sum_le {KCR : ℝ} {n : ℕ} (hn : 2 ≤ n) :
    (colBℓ KCR n : ℝ) + (colBc KCR n : ℝ)
      ≤ ((hintLenE KCR : ℝ) + 4 * max KCR 0 + 3) * lg (n : ℝ) ^ 3 := by
  have hL1 : (1 : ℝ) ≤ lg (n : ℝ) := one_le_lg hn
  have hE0 : (0 : ℝ) ≤ (hintLenE KCR : ℝ) := by positivity
  have hKr0 : (0 : ℝ) ≤ max KCR 0 := le_max_right _ _
  have hB1 : (colBℓ KCR n : ℝ) ≤ ((hintLenE KCR : ℝ) + 1) * lg (n : ℝ) ^ 3 + 1 := by
    have hx0 : (0 : ℝ) ≤ ((hintLenE KCR : ℝ) + 1) * lg (n : ℝ) ^ 3 := by positivity
    have h := Nat.ceil_lt_add_one hx0
    unfold colBℓ
    linarith only [h]
  have hB2 : (colBc KCR n : ℝ) ≤ max KCR 0 * lg ((n : ℝ) + 2) ^ 2 + 1 := by
    have hx0 : (0 : ℝ) ≤ max KCR 0 * lg ((n : ℝ) + 2) ^ 2 := by
      have h0 : (0 : ℝ) ≤ lg ((n : ℝ) + 2) ^ 2 := by positivity
      positivity
    have h := Nat.ceil_lt_add_one hx0
    unfold colBc
    linarith only [h]
  have hlg2 : lg ((n : ℝ) + 2) ^ 2 ≤ 4 * lg (n : ℝ) ^ 2 := by
    have h1 : lg ((n : ℝ) + 2) ≤ lg (n : ℝ) + 1 := lg_add_two_le hn
    have h0 : (0 : ℝ) ≤ lg ((n : ℝ) + 2) := by
      apply lg_nonneg_of_one_le
      have h3 : (0 : ℝ) ≤ (n : ℝ) := by positivity
      linarith only [h3]
    have h2 : lg ((n : ℝ) + 2) ^ 2 ≤ (lg (n : ℝ) + 1) ^ 2 := by nlinarith only [h1, h0, hL1]
    have h3 : (lg (n : ℝ) + 1) ^ 2 ≤ 4 * lg (n : ℝ) ^ 2 := sq_add_one_le_four_sq hL1
    linarith only [h2, h3]
  have hB2' : (colBc KCR n : ℝ) ≤ max KCR 0 * (4 * lg (n : ℝ) ^ 2) + 1 := by
    have h3 : max KCR 0 * lg ((n : ℝ) + 2) ^ 2 ≤ max KCR 0 * (4 * lg (n : ℝ) ^ 2) :=
      mul_le_mul_of_nonneg_left hlg2 hKr0
    linarith only [hB2, h3]
  have h4 : (1 : ℝ) ≤ lg (n : ℝ) ^ 3 := by
    calc (1 : ℝ) ≤ lg (n : ℝ) := hL1
      _ = lg (n : ℝ) ^ 1 := by simp
      _ ≤ lg (n : ℝ) ^ 3 := pow_le_pow_right₀ hL1 (by norm_num)
  have h5 : (1 : ℝ) ≤ lg (n : ℝ) ^ 2 := by
    calc (1 : ℝ) ≤ lg (n : ℝ) := hL1
      _ = lg (n : ℝ) ^ 1 := by simp
      _ ≤ lg (n : ℝ) ^ 2 := pow_le_pow_right₀ hL1 (by norm_num)
  have h6 : max KCR 0 * (4 * lg (n : ℝ) ^ 2) ≤ max KCR 0 * (4 * lg (n : ℝ) ^ 3) := by
    have h8 : lg (n : ℝ) ^ 2 ≤ lg (n : ℝ) ^ 3 := pow_le_pow_right₀ hL1 (by norm_num : 2 ≤ 3)
    have h7 : (4 : ℝ) * lg (n : ℝ) ^ 2 ≤ 4 * lg (n : ℝ) ^ 3 := by linarith only [h8]
    exact mul_le_mul_of_nonneg_left h7 hKr0
  nlinarith only [hB1, hB2', h6, h4, hE0, hKr0, hL1]

/-- The numeric endgame: `nodeCount·(Bℓ+Bc) ≤ Cu log^{pu} n`. -/
lemma nodeCol_bound {KCR : ℝ} {n : ℕ} {T : Node} (hn : 2 ≤ n)
    (hnc : (T.nodeCount : ℝ) ≤ hintLenK₁₀ * (hintLenA KCR : ℝ) * lg (n : ℝ) ^ 27) :
    (T.nodeCount : ℝ) * ((colBℓ KCR n : ℝ) + (colBc KCR n : ℝ))
      ≤ hintCu (hintColK KCR) * lg (n : ℝ) ^ hintpu := by
  have hL1 : (1 : ℝ) ≤ lg (n : ℝ) := one_le_lg hn
  have hKc1 : (1 : ℝ) ≤ hintColK KCR := by
    have h1 : (0 : ℝ) ≤ hintLenK KCR := le_of_lt (hintLenK_pos KCR)
    have h2 : (0 : ℝ) ≤ (hintLenA KCR : ℝ) := by positivity
    have h3 : (0 : ℝ) ≤ (hintLenE KCR : ℝ) := by positivity
    unfold hintColK
    linarith only [h1, h2, h3]
  have hA0 : (0 : ℝ) ≤ (hintLenA KCR : ℝ) := by positivity
  have hE0 : (0 : ℝ) ≤ (hintLenE KCR : ℝ) := by positivity
  have hKr0 : (0 : ℝ) ≤ max KCR 0 := le_max_right _ _
  have hsum := colB_sum_le (KCR := KCR) hn
  have hsum0 : (0 : ℝ) ≤ (colBℓ KCR n : ℝ) + (colBc KCR n : ℝ) := by
    have h1 : (0 : ℝ) ≤ (colBℓ KCR n : ℝ) := by positivity
    have h2 : (0 : ℝ) ≤ (colBc KCR n : ℝ) := by positivity
    linarith only [h1, h2]
  have hright0 : (0 : ℝ) ≤ (hintLenE KCR : ℝ) + 4 * max KCR 0 + 3 := by
    linarith only [hE0, hKr0]
  have hb0 : (0 : ℝ) ≤ hintLenK₁₀ * (hintLenA KCR : ℝ) * lg (n : ℝ) ^ 27 := by
    have h1 : (0 : ℝ) ≤ hintLenK₁₀ := le_of_lt (Classical.choose_spec LinearSetReconciliation327.Main.HintUpstream510.lemma_5_10).1
    have h2 : (0 : ℝ) ≤ (hintLenA KCR : ℝ) := by positivity
    have h3 : (0 : ℝ) ≤ lg (n : ℝ) ^ 27 := by positivity
    exact mul_nonneg (mul_nonneg h1 h2) h3
  have hstep1 : (T.nodeCount : ℝ) * ((colBℓ KCR n : ℝ) + (colBc KCR n : ℝ))
      ≤ (hintLenK₁₀ * (hintLenA KCR : ℝ) * lg (n : ℝ) ^ 27) *
          (((hintLenE KCR : ℝ) + 4 * max KCR 0 + 3) * lg (n : ℝ) ^ 3) :=
    mul_le_mul hnc hsum hsum0 hb0
  have hstep2 : (hintLenK₁₀ * (hintLenA KCR : ℝ) * lg (n : ℝ) ^ 27) *
          (((hintLenE KCR : ℝ) + 4 * max KCR 0 + 3) * lg (n : ℝ) ^ 3)
      = (hintLenK₁₀ * (hintLenA KCR : ℝ) * ((hintLenE KCR : ℝ) + 4 * max KCR 0 + 3)) *
          lg (n : ℝ) ^ 30 := by
    ring
  have hstep3 : hintLenK₁₀ * (hintLenA KCR : ℝ) * ((hintLenE KCR : ℝ) + 4 * max KCR 0 + 3)
      ≤ 8 * (hintColK KCR + 1) ^ 3 := by
    have h1 : hintLenK₁₀ ≤ hintColK KCR + 1 := by
      have h := hintLenK₁₀_le_hintColK KCR
      linarith only [h, hKc1]
    have h2 : (hintLenA KCR : ℝ) ≤ hintColK KCR + 1 := by
      have h := hintLenA_le_hintColK KCR
      linarith only [h, hKc1]
    have h3 : (hintLenE KCR : ℝ) + 4 * max KCR 0 + 3 ≤ 8 * (hintColK KCR + 1) := by
      have h4 := hintLenE_le_hintColK KCR
      have h5 := maxKCR_le_hintColK KCR
      nlinarith only [h4, h5, hKc1]
    have hp1 : hintLenK₁₀ * (hintLenA KCR : ℝ)
        ≤ (hintColK KCR + 1) * (hintColK KCR + 1) :=
      mul_le_mul h1 h2 hA0 (by linarith only [hKc1])
    have hp2 : hintLenK₁₀ * (hintLenA KCR : ℝ) * ((hintLenE KCR : ℝ) + 4 * max KCR 0 + 3)
        ≤ ((hintColK KCR + 1) * (hintColK KCR + 1)) * (8 * (hintColK KCR + 1)) := by
      apply mul_le_mul hp1 h3
      · linarith only [hE0, hKr0]
      · positivity
    calc hintLenK₁₀ * (hintLenA KCR : ℝ) * ((hintLenE KCR : ℝ) + 4 * max KCR 0 + 3)
        ≤ ((hintColK KCR + 1) * (hintColK KCR + 1)) * (8 * (hintColK KCR + 1)) := hp2
      _ = 8 * (hintColK KCR + 1) ^ 3 := by ring
  have hX1 : (1 : ℝ) ≤ hintColK KCR + 1 := by linarith only [hKc1]
  have hstep4 : 8 * (hintColK KCR + 1) ^ 3 * lg (n : ℝ) ^ 30
      ≤ ((2 : ℝ) ^ 30 * (hintColK KCR + 1) ^ 4) * lg (n : ℝ) ^ 1024 := by
    have hp : (8 : ℝ) * (hintColK KCR + 1) ^ 3 ≤ (2 : ℝ) ^ 30 * (hintColK KCR + 1) ^ 4 := by
      have h9 : (hintColK KCR + 1) ^ 3 ≤ (hintColK KCR + 1) ^ 4 := by
        have h := pow_le_pow_right₀ hX1 (by norm_num : 3 ≤ 4)
        simpa using h
      have h8 : (8 : ℝ) ≤ (2 : ℝ) ^ 30 := by norm_num
      calc (8 : ℝ) * (hintColK KCR + 1) ^ 3
          ≤ (2 : ℝ) ^ 30 * (hintColK KCR + 1) ^ 3 :=
            mul_le_mul_of_nonneg_right h8 (by positivity)
        _ ≤ (2 : ℝ) ^ 30 * (hintColK KCR + 1) ^ 4 :=
            mul_le_mul_of_nonneg_left h9 (by positivity)
    have hl : lg (n : ℝ) ^ 30 ≤ lg (n : ℝ) ^ 1024 := by
      have h := pow_le_pow_right₀ hL1 (by norm_num : 30 ≤ 1024)
      simpa using h
    exact mul_le_mul hp hl (by positivity) (by positivity)
  calc (T.nodeCount : ℝ) * ((colBℓ KCR n : ℝ) + (colBc KCR n : ℝ))
      ≤ (hintLenK₁₀ * (hintLenA KCR : ℝ) * lg (n : ℝ) ^ 27) *
          (((hintLenE KCR : ℝ) + 4 * max KCR 0 + 3) * lg (n : ℝ) ^ 3) := hstep1
    _ = (hintLenK₁₀ * (hintLenA KCR : ℝ) * ((hintLenE KCR : ℝ) + 4 * max KCR 0 + 3)) *
          lg (n : ℝ) ^ 30 := hstep2
    _ ≤ (8 * (hintColK KCR + 1) ^ 3) * lg (n : ℝ) ^ 30 :=
        mul_le_mul_of_nonneg_right hstep3 (by positivity)
    _ ≤ ((2 : ℝ) ^ 30 * (hintColK KCR + 1) ^ 4) * lg (n : ℝ) ^ 1024 := hstep4
    _ = hintCu (hintColK KCR) * lg (n : ℝ) ^ hintpu := by
        unfold hintCu hintpu
        ring

/-! ### 9h.5 Conjunct 5 -/

/-- **Theorem 5.1, conjunct 5**, at the tree of `P.tree`, with the *column* sparsity of Proposition
2.3 (`hcol`) as the only extra input (the row bound of conjunct 4 is not needed): every column of
`H = hintH_trees CR P T hT` has weight at most `Cu log^{pu} n`. -/
theorem hintColumnOK {KCR : ℝ} :
    ∃ K : ℝ, 0 < K ∧ KCR ≤ K ∧
      ∀ (n lam N X Y : ℕ) (CR : CRFamily),
        (∀ N' t : ℕ, t ≤ N' → ∀ a : ℕ,
          ((CR.col N' t a).card : ℝ) ≤ KCR * lg ((N' : ℝ) + 2) ^ 2) →
        (hintP KCR n lam).NodeArgs N X Y →
        ∀ (fuel : ℕ) (T : Node), (hintP KCR n lam).tree fuel N X Y = some T →
        ∀ (hT : IsSchemeTree (hintP KCR n lam) T) (r : (hintSpec T).Seed),
          HintColumnOK (hintColK KCR) (hintH_trees CR (hintP KCR n lam) T hT r) n := by
  refine ⟨hintColK KCR, hintColK_pos KCR, KCR_le_hintColK KCR, ?_⟩
  intro n lam N X Y CR hcol hargs fuel T htree hT r
  have hargs' := hargs
  obtain ⟨hn, hlam, hN1, hNn, hXN, hYN⟩ := hargs
  have hshrink : NodeShrink KCR n T :=
    tree_shrink (KCR := KCR) (P := hintP KCR n lam) rfl rfl hn fuel N X Y T htree hN1 hNn hXN hYN
  have hcok : ColNodeOK CR (colBℓ KCR n) (colBc KCR n) T :=
    colNodeOK_of_shrink (n := n) hcol T hshrink
  have hB : 1 ≤ colBℓ KCR n := colBℓ_pos hn
  obtain ⟨f₀, T₀, hT₀, -, -, -, hnc₀⟩ := lemma_5_10_at (KCR := KCR) n lam N X Y hargs'
  have hmax : (hintP KCR n lam).tree (max fuel f₀) N X Y = some T :=
    tree_mono (hintP KCR n lam) fuel N X Y htree (max fuel f₀) (le_max_left _ _)
  have hmax0 : (hintP KCR n lam).tree (max fuel f₀) N X Y = some T₀ :=
    tree_mono (hintP KCR n lam) f₀ N X Y hT₀ (max fuel f₀) (le_max_right _ _)
  have hTT : T = T₀ := Option.some.inj (by rw [← hmax, ← hmax0])
  have hnc : (T.nodeCount : ℝ) ≤ hintLenK₁₀ * (hintLenA KCR : ℝ) * lg (n : ℝ) ^ 27 := by
    rw [hTT]
    exact hnc₀
  intro i
  have hcard : (univ.filter fun p : Fin (synLen CR T) =>
        hintH_trees CR (hintP KCR n lam) T hT r (Pi.single i 1) p = 1).card
      ≤ T.nodeCount * (colBℓ KCR n + colBc KCR n) := by
    have h1 : (univ.filter fun p : Fin (synLen CR T) =>
          hintH_trees CR (hintP KCR n lam) T hT r (Pi.single i 1) p = 1).card
        = colWeight CR T (hintKappa (hintP KCR n lam) T hT r) ({i.val} : Finset ℕ) := by
      rw [colWeight_eq_card]
      simp only [colSupp, hintH_trees_apply, support_single]
    rw [h1]
    exact colWeight_singleton_le CR (colBℓ KCR n) (colBc KCR n) hB T hcok
      (hintKappa (hintP KCR n lam) T hT r) i.val i.isLt
  calc ((univ.filter fun p : Fin (synLen CR T) =>
        hintH_trees CR (hintP KCR n lam) T hT r (Pi.single i 1) p = 1).card : ℝ)
      ≤ ((T.nodeCount * (colBℓ KCR n + colBc KCR n) : ℕ) : ℝ) := by exact_mod_cast hcard
    _ = (T.nodeCount : ℝ) * ((colBℓ KCR n : ℝ) + (colBc KCR n : ℝ)) := by push_cast; ring
    _ ≤ hintCu (hintColK KCR) * lg (n : ℝ) ^ hintpu := nodeCol_bound hn hnc


end LinearSetReconciliation327.Main.HintProgramFree
end

#print axioms LinearSetReconciliation327.Main.HintProgramFree.hintLengthOK
#print axioms LinearSetReconciliation327.Main.HintProgramFree.hintColumnOK


