-- Prove2me | Definitions.Def_OAI_Probability_SATVariance_PairEvolution
-- name    : OAI_Probability_SATVariance_PairEvolution
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-15T17:31:32.255684+00:00
-- url     : https://prove2.me/theorems/1772e33d-7268-4ab2-a8da-bbf0bb8f1771
-- title:
--   Pair-state evolution of root and residual assignments under split clauses, with forced roots and hidden tests
-- statement:
--   Fix $u,k\in\mathbb N$. Assignments on $m$ Boolean variables are maps $[m]\to\{\mathrm T,\mathrm F\}$, $[m]=\{0,\dots,m-1\}$. An $s$-clause on $u$ variables is a set of $s$ distinct variables in $[u]$ with a sign for each, satisfied by an assignment that agrees with at least one sign. A *root type* is a map $t:[k]\to\{\bot,\mathrm T,\mathrm F\}$ with size $|t|=\#\{j:t(j)\ne\bot\}$; an assignment $a$ on $[k]$ *root-satisfies* $t$ if $t(j)=a(j)$ for some $j$.
--
--   1. **Root data and pair states.** A root datum is a pair $p=(t,c)$ of a root type $t$ and a $(k-|t|)$-clause $c$ on $u$ variables, i.e. a $k$-clause on $k+u$ variables split into root and residual parts. A pair state is a finite set $S$ of pairs $x=(a,b)$, where $a$ is an assignment on $[k]$ and $b$ an assignment on $[u]$.
--   2. **Satisfaction and filtering.** $x=(a,b)$ satisfies $p=(t,c)$ if $a$ root-satisfies $t$ or $b$ satisfies $c$. The step $\operatorname{step}_p(S)=\{x\in S:\ x\text{ satisfies }p\}$ removes the pairs violating $p$.
--   3. **Fibres and masks.** For a root assignment $a$, $\operatorname{fib}_a(S)=\{b:(a,b)\in S\}$ and $\operatorname{mask}_a(p)=\{b:(a,b)\text{ satisfies }p\}$.
--   4. **Refreshed evolution.** For refresh noise $z=(z_1,z_2)$, consisting of a fresh $k$-clause $z_1$ and fresh $(k-1)$-clauses $z_2(j)$ for $j\in[k]$, the refreshed datum $\operatorname{refresh}_a(p,z)=(t,c^{z})$ keeps $t$ and replaces $c$ by $z_1$ if $|t|=0$, by $z_2(j)$ if $|t|=1$ and $a$ satisfies the single root literal (at position $j$), and keeps $c^{z}=c$ otherwise. Given an environment $(p_i)_{i\ge0}$ of root data, the evolution at time $i$ with noise $z$ is $S\mapsto\operatorname{step}_{\operatorname{refresh}_a(p_i,z)}(S)$.
--   5. **Forced reward.** $\phi_a(S)=1$ if $S\ne\emptyset$ and every $x\in S$ has root part $a$; otherwise $\phi_a(S)=0$.
--   6. **Prefixes and rewards along a finite word.** For root data $p_0,\dots,p_{M-1}$, let $\operatorname{pre}_m(S)=\{x\in S:\ x\text{ satisfies }p_i\text{ for all }i<m\}$, and for a real function $f$ on pair states
--   $$
--   \operatorname{Rew}_f(S;p_0,\dots,p_{M-1})=\sum_{i=0}^{M-1}f\big(\operatorname{pre}_i(S)\big).
--   $$
--   7. **Noise reorganization.** A word of $M$ refresh noises is identified with a pair consisting of $M$ fresh $k$-clauses $o_0,\dots,o_{M-1}$ and a $k\times M$ array $(y_{j,i})$ of fresh $(k-1)$-clauses, where $o_i$ and $y_{j,i}$ are the components $z_1$ and $z_2(j)$ of the $i$-th noise.
--   8. **Fibre prefix.** For root data $p_i=(t_i,c_i)$, $i<M$, and fresh $k$-clauses $o_i$,
--   $$
--   \operatorname{FP}_m=\big\{b:\ \text{for every } i<m,\ \ b\text{ satisfies } o_i \text{ if } |t_i|=0,\ \text{ and } (a,b)\text{ satisfies } p_i \text{ if } |t_i|\ne0\big\}.
--   $$
--   9. **Flips, unique true roots, tests and availability.** $a^{(j)}$ is $a$ with coordinate $j$ negated. Position $j$ is the *unique true* root of $t$ under $a$ if $t(j)=a(j)$ and $t(l)\ne a(l)$ for every $l\ne j$. A root datum $p=(t,c)$ is a *test at* $j$ if $|t|=1$ and $t(j)=a(j)$. Position $j$ is *available* for $(p_i)_{i<M}$ if no $p_i$ with $|t_i|\ge2$ has $j$ as its unique true root under $a$.
--
--   Here $a$ stands for the root assignment falsifying a deleted clause, and the forced reward records the steps at which every surviving pair has root part $a$, so that the deleted clause is the binding constraint. The fibre of the refreshed evolution is described by the masks and the fresh clauses $o_i$ (the fibre prefix). For the root to stay forced, every flipped root $a^{(j)}$ must have been eliminated, and for an available position $j$ this can only be done by the hidden $(k-1)$-clauses $y_{j,i}$ attached to the tests at $j$. This bounds the probability that the root stays forced, and hence the second moment of the effect of deleting one clause on the first unsatisfiability time.
--
--   **Formalization Note** `RootData u k` is the sigma type of a root type `t` and a `Clause u (k - rootSize t)`, and `PairState u k` is a `Finset` of pairs of assignments. In `pairPrefix` and `fibrePrefix` the condition $i<m$ ranges over $i\in\{0,\dots,M-1\}$, so for $m>M$ all data are used. The noise reorganization is the explicit equivalence `noiseWordEquiv`. `dataStep`, `fibre`, `dataMask`, `refreshData`, `forcedReward`, `pairEvolution`, `pairPrefix`, `dataRewards`, `flipRoot`, `UniqueTrue`, `TestAt` and `Available` are items 2 to 9 in order.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Probability/SATVariance/PairEvolution.lean

-- Generated from openai/math@1581d4c lean/OAI/Probability/SATVariance/PairEvolution.lean by skeleton subtraction
-- (upload_full_project.md Phase 3): Definitions bundle for the SATVariance mission closure.
-- Kept: reachable definitions/instances and the theorems their bodies or the node statements cite.
-- Project imports rewritten to platform modules; otherwise byte-identical to the source.
import Mathlib
import Definitions.Def_SATVariance
import Definitions.Def_OAI_Probability_SATVariance_ClauseCombinatorics__SATVariance
import Definitions.Def_OAI_Probability_SATVariance_FrozenReplacement__SATVariance
import Definitions.Def_OAI_Probability_SATVariance_BlockKilling
import Definitions.Def_OAI_Probability_SATVariance_MarkovReplacement__SATVariance
import Definitions.Def_OAI_Probability_SATVariance_FiniteVariance
import Definitions.Def_OAI_Probability_SATVariance_LifetimePotential
import Definitions.Def_OAI_Probability_SATVariance_RootDisintegration__SATVariance
import Definitions.Def_OAI_Probability_SATVariance_FiberRefresh

-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory

namespace RandomKSAT

open scoped Classical ENNReal

abbrev RootData (u k : ℕ) := (t : RootType k) × Clause u (k-rootSize t)

abbrev PairState (u k : ℕ) := Finset (Assignment k × Assignment u)

def DataSatisfies {u k : ℕ} (p : RootData u k) (x : Assignment k × Assignment u) : Prop :=
  RootSatisfies p.1 x.1 ∨ Satisfies p.2 x.2

def dataStep {u k : ℕ} (p : RootData u k) (S : PairState u k) : PairState u k :=
  S.filter (DataSatisfies p)

def fibre {u k : ℕ} (a : Assignment k) (S : PairState u k) : Finset (Assignment u) :=
  Finset.univ.filter fun b => (a,b) ∈ S

def dataMask {u k : ℕ} (p : RootData u k) (a : Assignment k) : Finset (Assignment u) :=
  Finset.univ.filter fun b => DataSatisfies p (a,b)

def refreshData {u k : ℕ} (a : Assignment k) (p : RootData u k)
    (z : RefreshNoise u k) : RootData u k := ⟨p.1,refreshPart p.1 a p.2 z⟩

def forcedReward {u k : ℕ} (a : Assignment k) (S : PairState u k) : ℝ :=
  if S.Nonempty ∧ ∀ x ∈ S, x.1 = a then 1 else 0

def pairEvolution {u k : ℕ} (a : Assignment k) (env : ℕ → RootData u k)
    (i : ℕ) (z : RefreshNoise u k) (S : PairState u k) : PairState u k :=
  dataStep (refreshData a (env i) z) S

def pairPrefix {u k M : ℕ} (S : PairState u k) (ps : Fin M → RootData u k)
    (m : ℕ) : PairState u k :=
  S.filter fun x => ∀ i : Fin M, i.val < m → DataSatisfies (ps i) x

def dataRewards {u k M : ℕ} (f : PairState u k → ℝ) (S : PairState u k)
    (ps : Fin M → RootData u k) : ℝ := ∑ i : Fin M, f (pairPrefix S ps i.val)

def noiseWordEquiv (u k M : ℕ) :
    (Fin M → RefreshNoise u k) ≃
      ((Fin M → Clause u k) × (Fin k → Fin M → Clause u (k-1))) where
  toFun w := (fun i => (w i).1, fun j i => (w i).2 j)
  invFun z := fun i => (z.1 i, fun j => z.2 j i)
  left_inv w := by funext i; rfl
  right_inv z := by rfl

def fibrePrefix {u k M : ℕ} (a : Assignment k) (env : Fin M → RootData u k)
    (o : Fin M → Clause u k) (m : ℕ) : Finset (Assignment u) :=
  Finset.univ.filter fun b => ∀ i : Fin M, i.val < m →
    if rootSize (env i).1 = 0 then Satisfies (o i) b else DataSatisfies (env i) (a,b)

def flipRoot {k : ℕ} (a : Assignment k) (j : Fin k) : Assignment k := Function.update a j (!(a j))

def UniqueTrue {k : ℕ} (t : RootType k) (a : Assignment k) (j : Fin k) : Prop :=
  t j = some (a j) ∧ ∀ l, l ≠ j → t l ≠ some (a l)

def TestAt {u k : ℕ} (a : Assignment k) (p : RootData u k) (j : Fin k) : Prop :=
  rootSize p.1 = 1 ∧ p.1 j = some (a j)

def Available {u k M : ℕ} (a : Assignment k) (env : Fin M → RootData u k) (j : Fin k) : Prop :=
  ∀ i, 2 ≤ rootSize (env i).1 → ¬ UniqueTrue (env i).1 a j

end RandomKSAT

end

end OAI


