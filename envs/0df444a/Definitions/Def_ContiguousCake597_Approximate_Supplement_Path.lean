-- Prove2me | Definitions.Def_ContiguousCake597_Approximate_Supplement_Path
-- name    : ContiguousCake597_Approximate_Supplement_Path
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-15T19:57:56.220459+00:00
-- url     : https://prove2.me/theorems/26fedc07-b89b-4f0d-be73-2c1fcdc890d2
-- title:
--   Goods and chores on a path, contiguous EFc and EFc-outer, and their search problems
-- statement:
--   An instance of the discrete problem has $n\ge1$ agents and items $g_1,\dots,g_m$ on a path, in this order ($m\ge0$). Each agent $i$ has an additive valuation $\nu_i$ (goods) or an additive cost $\kappa_i$ (chores) that assigns every item a nonnegative rational number; the value or cost of a set $S$ of items is the sum over its items. No normalization is imposed. The **binary exclusive equal-count** class consists of the instances in which every value is $0$ or $1$, every item has value $1$ for exactly one agent, and all agents have value $1$ on the same number of items.
--
--   A **contiguous allocation** consists of integer indices and a bijection $\sigma:[n]\to[n]$,
--   $$0=\beta_0\le\beta_1\le\dots\le\beta_n=m,\qquad X_i=\{g_k:\beta_{\sigma(i)-1}<k\le\beta_{\sigma(i)}\}.$$
--   Bundles may be empty. For an integer $c\ge0$, an allocation of goods is **EF$c$** if for all agents $i,j$ there is $G\subseteq X_j$ with $|G|\le c$ and $\nu_i(X_i)\ge\nu_i(X_j\setminus G)$; an allocation of chores is EF$c$ if for all $i,j$ there is $G\subseteq X_i$ with $|G|\le c$ and $\kappa_i(X_i\setminus G)\le\kappa_i(X_j)$. It is **EF$c_{\mathrm{outer}}$** if moreover $G$ can be chosen so that the remaining set ($X_j\setminus G$ for goods, $X_i\setminus G$ for chores) is a run of consecutive items or empty.
--
--   The removal budget is either a fixed integer $c$ or $\lfloor m^\alpha\rfloor$ for a fixed rational $\alpha$; for $\alpha=p/q$ in lowest terms with $0<\alpha<1$ this is computed exactly as the largest integer $h\le m$ with $h^q\le m^p$.
--
--   The search problem for a choice of item kind, fairness notion, budget and instance class takes as input the binary encoding of an instance (self-delimiting binary $n$ and $m$, then each agent's row as a length-prefixed list of binary rationals), and accepts as an answer the binary encoding of any complete contiguous allocation (all $n+1$ cuts and the full bijection) satisfying the fairness notion. **PPAD membership** in the sense of §2.1 of the paper means: membership in the published class PPAD (totality plus a polynomial-time search reduction to End-of-Line), a polynomial-time verifier for the answer relation, and a polynomial bound on the length of some answer for every valid input. **PPAD-completeness** adds that every problem in PPAD reduces to it.
--
--   These are the objects of §2.2 used by Theorem 2 and Lemmas 11 and 12.
--
--   **Formalization Note** Item $g_{k+1}$ is index $k$ of `Fin m`. Allocations reuse the published `Allocation ℕ n` (cuts and assignment) of the mission's model. The goods EF$c$ test reuses the published `BalancedKneser.AcceptsEF`. "At least one agent" is the standing convention: with $n=0$ and $m>0$ no complete allocation exists.
-- source:
--   Yasushi Kawase, Bodhayan Roy, Mohammad Azharuddin Sanpui, STOC 2027 submission #597 (October 2026), p. 4 (PDF 5), §2.2; pp. 2, 4 (PDF 3, 5), Theorem 2 and §2.1

import Definitions.Def_ContiguousCake597_Approximate_Search
import Definitions.Def_BalancedKneser_AcceptsEF

namespace ContiguousCake597.Approximate.Supplement
open QAlgorithms.LocalHamiltonian

/-- §2.2, printed p.4 (PDF 5). Items `g₁,…,g_m` on a path are the indices `0,…,m-1` of
`Fin m` (item `k` is `g_{k+1}`). `val i k` is agent `i`'s value (goods) or cost (chores)
for item `k`. Validity is separate from parsing. -/
structure PathData where
  n : ℕ
  m : ℕ
  val : Fin n → Fin m → ℚ

/-- At least one agent, every value or cost nonnegative. No normalization. -/
def PathData.Valid (D : PathData) : Prop :=
  1 ≤ D.n ∧ ∀ i k, 0 ≤ D.val i k

/-- Binary values, each item valued (with value 1) by exactly one agent, and every agent
values the same number of items. -/
def PathData.BinaryExclusiveEqual (D : PathData) : Prop :=
  (∀ i k, D.val i k = 0 ∨ D.val i k = 1) ∧
  (∀ k, ∃! i, D.val i k = 1) ∧
  ∃ r : ℕ, ∀ i, (Finset.univ.filter fun k => D.val i k = 1).card = r

/-- Index cuts `0 = β₀ ≤ β₁ ≤ ⋯ ≤ βₙ = m`; the assignment is `Allocation.assign`. -/
def PathComplete {n : ℕ} (m : ℕ) (T : Allocation ℕ n) : Prop :=
  T.cuts 0 = 0 ∧ T.cuts (Fin.last n) = m ∧ Monotone T.cuts

/-- The `j`th spatial piece `{g_k : β_{j-1} < k ≤ β_j}`, in `0`-based item indices. -/
def piece {n : ℕ} (m : ℕ) (T : Allocation ℕ n) (j : Fin n) : Finset (Fin m) :=
  Finset.univ.filter fun k => T.cuts j.castSucc ≤ k.val ∧ k.val < T.cuts j.succ

/-- Agent `i`'s bundle `X_i`, the `σ(i)`th piece. -/
def bundle {n : ℕ} (m : ℕ) (T : Allocation ℕ n) (i : Fin n) : Finset (Fin m) :=
  piece m T (T.assign i)

/-- Additive value (or cost) of a set of items for agent `i`. -/
noncomputable def setValue (D : PathData) (i : Fin D.n) (S : Finset (Fin D.m)) : ℝ :=
  ∑ k ∈ S, (D.val i k : ℝ)

/-- A set of items is connected on the path (a run of consecutive items) or empty. -/
def ConnectedOrEmpty {m : ℕ} (S : Finset (Fin m)) : Prop :=
  ∀ a ∈ S, ∀ b ∈ S, ∀ k : Fin m, a ≤ k → k ≤ b → k ∈ S

/-- Goods EFc (`outer = false`) and EFc_outer (`outer = true`): for all agents `i, j`
some `G ⊆ X_j`, `|G| ≤ c`, has `ν_i(X_i) ≥ ν_i(X_j ∖ G)`, and for the outer version
`X_j ∖ G` is connected or empty. -/
def GoodsFair (outer : Bool) (c : ℕ) (D : PathData) (T : Allocation ℕ D.n) : Prop :=
  ∀ i j : Fin D.n,
    if outer then
      ∃ G ⊆ bundle D.m T j, G.card ≤ c ∧ ConnectedOrEmpty (bundle D.m T j \ G) ∧
        setValue D i (bundle D.m T j \ G) ≤ setValue D i (bundle D.m T i)
    else BalancedKneser.AcceptsEF c (setValue D i) (bundle D.m T i) (bundle D.m T j)

/-- Chores EFc and EFc_outer: for all agents `i, j` some `G ⊆ X_i`, `|G| ≤ c`, has
`κ_i(X_i ∖ G) ≤ κ_i(X_j)`, and for the outer version `X_i ∖ G` is connected or empty. -/
def ChoresFair (outer : Bool) (c : ℕ) (D : PathData) (T : Allocation ℕ D.n) : Prop :=
  ∀ i j : Fin D.n, ∃ G ⊆ bundle D.m T i, G.card ≤ c ∧
    (outer = true → ConnectedOrEmpty (bundle D.m T i \ G)) ∧
    setValue D i (bundle D.m T i \ G) ≤ setValue D i (bundle D.m T j)

/-- `⌊m^α⌋` for rational `0 < α < 1`, computed exactly: with `α = p/q` in lowest terms
it is the largest `h ≤ m` with `h^q ≤ m^p` (for such `α`, `⌊m^α⌋ ≤ m`). -/
def powFloor (α : ℚ) (m : ℕ) : ℕ :=
  Nat.findGreatest (fun h => h ^ α.den ≤ m ^ α.num.toNat) m

/-- The removal budget: a fixed integer `c`, or `⌊m^α⌋` for a fixed rational `α`. -/
inductive Budget where
  | const (c : ℕ)
  | power (α : ℚ)

def Budget.eval : Budget → ℕ → ℕ
  | .const c, _ => c
  | .power α, m => powFloor α m

/-- Dimensions, then each agent's row as a length-prefixed list of binary rationals. -/
def encPath (D : PathData) : List Bool :=
  encBin D.n ++ encBin D.m ++
    (List.finRange D.n).flatMap fun i => encRats ((List.finRange D.m).map (D.val i))

/-- All `n+1` index cuts and the full assignment, in binary. -/
def encPathAllocation {n : ℕ} (T : Allocation ℕ n) : List Bool :=
  (List.finRange (n+1)).flatMap (fun j => encBin (T.cuts j)) ++
    (List.finRange n).flatMap fun i => encBin (T.assign i).val

/-- The fairness predicate of the chosen item kind. -/
def Fair (chores outer : Bool) (c : ℕ) (D : PathData) (T : Allocation ℕ D.n) : Prop :=
  if chores then ChoresFair outer c D T else GoodsFair outer c D T

/-- Contiguous EFc / EFc_outer search on a path: items are goods (`chores = false`) or
chores, the budget is `b.eval m`, and `restricted = true` limits instances to the binary
exclusive-ownership equal-count class. Every complete allocation is an answer; no length
bound is imposed on answers. -/
def PathProblem (chores outer : Bool) (b : Budget) (restricted : Bool) :
    TetrisHard.Rows.SearchProblem where
  valid s := ∃ D : PathData, D.Valid ∧ (restricted = true → D.BinaryExclusiveEqual) ∧
    s = encPath D
  answer s t := ∃ (D : PathData) (T : Allocation ℕ D.n), D.Valid ∧
    (restricted = true → D.BinaryExclusiveEqual) ∧ s = encPath D ∧
    t = encPathAllocation T ∧ PathComplete D.m T ∧ Fair chores outer (b.eval D.m) D T

/-- Membership in PPAD in the sense of §2.1: the published `PPAD` predicate, a uniform
polynomial-time verifier of the answer relation, and short answers for every valid input. -/
def PaperPPAD (Q : TetrisHard.Rows.SearchProblem) : Prop :=
  Q ∈ QuasiStrictNE.PPAD ∧
  CookPvsNP.checkLang Q.answer ∈ CookPvsNP.P (Option (Bool ⊕ Bool)) ∧
  ∃ k : ℕ, ∀ s, Q.valid s → ∃ t, t.length ≤ s.length ^ k + k ∧ Q.answer s t

/-- PPAD-completeness with §2.1 membership. -/
def PaperPPADComplete (Q : TetrisHard.Rows.SearchProblem) : Prop :=
  PaperPPAD Q ∧ QuasiStrictNE.PPADComplete Q

end ContiguousCake597.Approximate.Supplement


