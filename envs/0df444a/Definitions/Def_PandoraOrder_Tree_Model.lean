-- Prove2me | Definitions.Def_PandoraOrder_Tree_Model
-- name    : PandoraOrder_Tree_Model
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-29T21:58:32.82202+00:00
-- url     : https://prove2.me/theorems/8e7d57ae-48ad-4146-a46a-d3f8175d3ecc
-- title:
--   Tree-constrained search: independent boxes, histories, payoff and suffix values
-- statement:
--   There are $n$ boxes. Each has a finite atom table, a real probability distribution, a nonnegative real reward at each atom, and a nonnegative opening cost. Rewards of different boxes are sampled independently. Tables may contain zero-mass or repeated atoms. The general distribution object is the published finite real probability distribution; the general tree object is the published rooted parent-map tree.
--
--   A history is the ordered list of opened box labels and revealed rewards. A behavioral policy assigns a distribution over stopping and the next box to every history. Admissibility requires each positive-probability opening to be legal and unrepeated. A deterministic policy chooses a single action at each history. Stopping is allowed initially and is irreversible. Legal tree openings require the parent to have been opened, except at the root. A line allows its next vertex; a union of disjoint lines permits the next vertex of any unfinished line.
--
--   Starting with incumbent $x$, the terminal payoff is the maximum of $x$ and all revealed rewards, minus all incurred costs. The finite execution recursion sums the stopping branch and each opening-and-reward branch. It evaluates a fixed policy, rather than optimizing. The semantic suffix value $\Phi(x,L)$ is the supremum of these values over admissible policies. Its generalized threshold is the infimum of $\{x\ge0:\Phi(x,L)=x\}$. Claim 2 separately requires this infimum to be the least root and requires attainment of the value supremum.
--
--   The classical reservation value is the least real root of the expected positive-part equation; negative roots are not clamped. The same equation gives its zero-cost extension for finite support. A separate recursive Bellman function and continuation value are defined numerically. Their equality with the semantic value is a conclusion of Theorem 5. The auxiliary stopping time uses optimal-continuation ties, whereas the actual search rule uses the strict Algorithm 1 test. Prefix length stops before the first strictly smaller following suffix threshold, or at the end of the line.
--
--   Formalization Note: suffix values are restarted experiments, including off-support incumbents, following Appendix C (9). Real suprema and infima have Lean's total defaults on invalid inputs; the theorem contracts establish attainment and least-root existence for legal inputs. Empty lines allow only stopping. Arbitrarily many boxes, support atoms and branches are permitted.
-- source:
--   Boodaghians et al., arXiv:2002.06968v2, §§2–3.1, pp. 5–8 (PDF pp. 5–8), Definitions 2–3 and Appendix C (9), p. 22; https://arxiv.org/abs/2002.06968v2

import Mathlib
import Definitions.Def_WildeQIT_FinDist
import Definitions.Def_HarelTarjan_Compressed_RootedTree

namespace PandoraOrder.Tree

/-- Finite-support box data. Atom labels need not have distinct values or positive mass. -/
structure Instance (n : ℕ) where
  size : Fin n → ℕ
  law : (b : Fin n) → WildeQIT.FinDist (Fin (size b))
  reward : (b : Fin n) → Fin (size b) → ℝ
  reward_nonneg : ∀ b a, 0 ≤ reward b a
  cost : Fin n → ℝ
  cost_nonneg : ∀ b, 0 ≤ cost b

abbrev History (n : ℕ) := List (Fin n × ℝ)
abbrev Constraint (n : ℕ) := List (Fin n) → Fin n → Prop
abbrev Policy (n : ℕ) := History n → WildeQIT.FinDist (Option (Fin n))

/-- Every past action was available, with no repeated openings. Rewards in a history are
actual observed values, not latent atom labels. -/
def Legal {n : ℕ} (F : Constraint n) : History n → Prop
  | [] => True
  | h => h.Pairwise (fun a b => a.1 ≠ b.1) ∧
      ∀ k (b : Fin n) r, h[k]? = some (b, r) → F ((h.take k).map Prod.fst) b

def Admissible {n : ℕ} (F : Constraint n) (π : Policy n) : Prop :=
  ∀ h, Legal F h → ∀ b, (π h).prob (some b) ≠ 0 →
    b ∉ h.map Prod.fst ∧ F (h.map Prod.fst) b

noncomputable def pureAction {n : ℕ} (a : Option (Fin n)) : WildeQIT.FinDist (Option (Fin n)) := by
  classical
  exact ⟨fun b => if b = a then 1 else 0, by intro b; split_ifs <;> norm_num,
    by simp⟩

def Deterministic {n : ℕ} (π : Policy n) : Prop :=
  ∀ h, ∃ a, π h = pureAction a

noncomputable def stopPolicy {n : ℕ} : Policy n := fun _ => pureAction none

/-- Terminal payoff, including every incurred cost and the incumbent outside option. -/
def payoff {n : ℕ} (I : Instance n) (x : ℝ) (h : History n) : ℝ :=
  h.foldl (fun y br => max y br.2) x - (h.map (fun br => I.cost br.1)).sum

/-- Actual finite experiment: a stop action terminates, and an opening samples the next
independent box law. This evaluates a fixed history policy, without optimizing it. -/
noncomputable def expectedRun {n : ℕ} (I : Instance n) (π : Policy n) (x : ℝ) :
    ℕ → History n → ℝ
  | 0, h => payoff I x h
  | t + 1, h => (π h).prob none * payoff I x h +
      ∑ b : Fin n, (π h).prob (some b) *
        ∑ a : Fin (I.size b), (I.law b).prob a *
          expectedRun I π x t (h ++ [(b, I.reward b a)])

noncomputable def value {n : ℕ} (I : Instance n) (π : Policy n) (x : ℝ := 0) : ℝ :=
  expectedRun I π x n []

def treeConstraint {n : ℕ} (T : HarelTarjan.Compressed.RootedTree (Fin n)) : Constraint n :=
  fun opened b => b ∉ opened ∧ (b = T.root ∨ T.parent b ∈ opened)

/-- A line can open exactly its next vertex. Empty lines permit only stopping. -/
def lineConstraint {n : ℕ} (L : List (Fin n)) : Constraint n :=
  fun opened b => opened ++ [b] <+: L

/-- The input lines partition the boxes; a head or a vertex whose predecessor is open
is available. This definition does not impose an order between different lines. -/
def unionConstraint {n : ℕ} (Ls : List (List (Fin n))) : Constraint n :=
  fun opened b => b ∉ opened ∧ ∃ L ∈ Ls, ∃ k, L[k]? = some b ∧
    (L.take k).all (fun a => decide (a ∈ opened)) = true

def LinesCover {n : ℕ} (Ls : List (List (Fin n))) : Prop :=
  Ls.flatten.Nodup ∧ ∀ b : Fin n, b ∈ Ls.flatten

/-- Semantic line value: supremum of actual admissible randomized-policy payoffs. -/
noncomputable def lineValue {n : ℕ} (I : Instance n) (L : List (Fin n)) (x : ℝ) : ℝ :=
  sSup {v | ∃ π : Policy n, Admissible (lineConstraint L) π ∧ value I π x = v}

noncomputable def threshold {n : ℕ} (I : Instance n) (L : List (Fin n)) : ℝ :=
  sInf {x : ℝ | 0 ≤ x ∧ lineValue I L x = x}

/-- Classical reservation values range over all reals, including negative values.
Claim 3 also uses the same least-root equation at zero cost, where its least root
is the largest positive-mass reward. -/
noncomputable def classicalReservation {n : ℕ} (I : Instance n) (b : Fin n) : ℝ :=
  sInf {z : ℝ | (∑ a : Fin (I.size b), (I.law b).prob a *
    max (I.reward b a - z) 0) = I.cost b}

/-- Numerical Bellman recursion, kept separate from the semantic supremum. -/
noncomputable def lineDP {n : ℕ} (I : Instance n) : List (Fin n) → ℝ → ℝ
  | [], x => x
  | b :: L, x => max x (-I.cost b + ∑ a : Fin (I.size b),
      (I.law b).prob a * lineDP I L (max x (I.reward b a)))

noncomputable def continueValue {n : ℕ} (I : Instance n) (b : Fin n)
    (L : List (Fin n)) (x : ℝ) : ℝ :=
  -I.cost b + ∑ a : Fin (I.size b), (I.law b).prob a * lineDP I L (max x (I.reward b a))

/-- Auxiliary optimal continuation tie convention of p. 8. At a zero threshold,
continue only when continuation is optimal; this leaves the printed indifference claim
as a theorem obligation rather than building it into the definition. -/
noncomputable def auxiliaryStop {n : ℕ} (I : Instance n) :
    List (Fin n) → ℝ → (Fin n → ℝ) → ℕ
  | [], _, _ => 0
  | b :: L, x, rewards => if x ≤ continueValue I b L x then
      1 + auxiliaryStop I L (max x (rewards b)) rewards else 0

/-- Length through the vertex immediately before the first strictly smaller threshold. -/
noncomputable def prefixLength {n : ℕ} (I : Instance n) (L : List (Fin n)) : ℕ := by
  classical
  exact ((List.range L.length).filter (fun k =>
    0 < k ∧ threshold I (L.drop k) < threshold I L)).headD L.length

def inputSize {n : ℕ} (I : Instance n) : ℕ := n + ∑ b : Fin n, I.size b

end PandoraOrder.Tree


