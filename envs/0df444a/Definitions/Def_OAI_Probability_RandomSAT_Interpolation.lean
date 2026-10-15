-- Prove2me | Definitions.Def_OAI_Probability_RandomSAT_Interpolation
-- name    : OAI_Probability_RandomSAT_Interpolation
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-15T04:40:03.754682+00:00
-- url     : https://prove2.me/theorems/bf1ca8ca-6876-4543-9853-e1df1ddd8c70
-- title:
--   Auxiliary clauses with repeated variables, finite averaging operators and block product sets
-- statement:
--   The auxiliary model replaces proper clauses, whose variables are distinct, by ordered clauses whose literals are chosen independently, so variables may repeat. For a set $S$ of assignments, $\operatorname{alive}(S)$ is $1$ if $S\neq\emptyset$ and $0$ otherwise, and $\Omega_n$ is the set of all assignments on $n$ variables.
--
--   1. **Auxiliary clause.** An auxiliary $k$-clause on $n$ variables is a $k$-tuple $C=\big((i_1,t_1),\dots,(i_k,t_k)\big)$ of literals, with variables $i_j\in\{0,\dots,n-1\}$ that need not be distinct and signs $t_j$. An assignment $\sigma$ satisfies $C$ if $\sigma(i_j)=t_j$ for some $j$.
--   2. **Finite clause average.** For any finite set $\mathcal{C}$ of clauses with a satisfaction relation $\mathrm{sat}(c,\sigma)$, the averaging operator acts on real functions $f$ of sets of assignments by
--   $$
--   (A_{\mathcal{C}}f)(S)=\mathbb{E}_{c\in\mathcal{C}}\Big[f\big(\{\sigma\in S:\mathrm{sat}(c,\sigma)\}\big)\Big].
--   $$
--   3. **Mixed average.** For two operators $A,B$ and $p\in\mathbb{R}$, $\big(\mathrm{mix}_p(A,B)f\big)(S)=(1-p)\,(Bf)(S)+p\,(Af)(S)$.
--   4. **Embedded averages.** For a map $e:\{0,\dots,v-1\}\to\{0,\dots,n-1\}$, an auxiliary clause on $v$ variables is pushed forward to $n$ variables by relabelling each variable $i_j$ as $e(i_j)$. The operator $A_{e,k}$ is the finite clause average over uniformly random auxiliary $k$-clauses on $v$ variables pushed forward along $e$. The auxiliary average $A^{\mathrm{aux}}_k$ is the case $v=n$, $e=\mathrm{id}$.
--   5. **Auxiliary survival and probability.** $\operatorname{surv}^{\mathrm{aux}}_k(m,S)=\big((A^{\mathrm{aux}}_k)^m\operatorname{alive}\big)(S)$ and
--   $$
--   p_{\mathrm{aux}}(n,k,m)=\operatorname{surv}^{\mathrm{aux}}_k(m,\Omega_n),
--   $$
--   the probability that $m$ independent uniform auxiliary $k$-clauses on $n$ variables are simultaneously satisfiable.
--   6. **Embedded forced variables.** For a set $S$ of assignments on $n$ variables and $e$ as above, the set $\{i<v: e(i)\in\operatorname{Forced}(S)\}$.
--   7. **Block sets.** For a set $S$ of assignments on $r$ variables and a set $T$ on $s$ variables, the block set consists of the assignments on $r+s$ variables whose restriction to the first $r$ variables lies in $S$ and whose restriction to the last $s$ variables lies in $T$. It is the product $S\times T$ under this identification, and the block set of $\Omega_r$ and $\Omega_s$ is $\Omega_{r+s}$.
--
--   Averaging operators of this kind commute with one another. Mixing the averages over the two blocks of a partition of the variables gives an interpolation that compares the auxiliary satisfiability probability on $r+s$ variables with products of the probabilities on $r$ and on $s$ variables, weighted binomially. The auxiliary model is afterwards transferred back to proper clauses.
--
--   **Formalization Note** An auxiliary clause is a function `Fin k → Fin n × Bool`. The two blocks of `Fin (r + s)` are addressed with `Fin.castAdd` and `Fin.natAdd`. The quantity $p_{\mathrm{aux}}$ is defined as an iterate of the averaging operator applied to the alive indicator; reading it as a probability is the Fubini identification of iterated uniform means.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Probability/RandomSAT/Interpolation.lean

-- Generated from openai/math@1581d4c lean/OAI/Probability/RandomSAT/Interpolation.lean by skeleton subtraction
-- (upload_full_project.md Phase 3): Definitions bundle for the FixedClauseThreshold mission closure.
-- Kept: reachable definitions/instances and the theorems their bodies or the node statements cite.
-- Project imports rewritten to platform modules; otherwise byte-identical to the source.
import Mathlib
import Definitions.Def_FixedClauseThreshold
import Definitions.Def_OAI_Probability_RandomSAT_Clauses
import Definitions.Def_OAI_Probability_RandomSAT_Replacement
import Definitions.Def_OAI_Probability_RandomSAT_FiniteMean
import Definitions.Def_OAI_Probability_RandomSAT_ClauseProcess
import Definitions.Def_OAI_Probability_RandomSAT_Binomial
import Definitions.Def_OAI_Probability_RandomSAT_Forcing
import Definitions.Def_OAI_Probability_RandomSAT_Variance
import Definitions.Def_OAI_Probability_RandomSAT_Concentration
import Definitions.Def_OAI_Probability_RandomSAT_CenterBounds

-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

/-!
Auxiliary ordered clauses allow repeated variables. Commuting finite averaging
operators give the fixed-count partition interpolation corresponding to the
marked-Poisson comparison.
-/

namespace FixedClauseThreshold

open Finset

noncomputable section

attribute [local instance] Classical.propDecidable

abbrev AuxiliaryClause (n k : ℕ) := Fin k → (Fin n × Bool)

def auxiliarySatisfies {n k : ℕ} (σ : Assignment n) (C : AuxiliaryClause n k) : Prop :=
  ∃ j, σ (C j).1 = (C j).2

def finiteClauseAverage {n : ℕ} {C : Type*} [Fintype C]
    (sat : C → Assignment n → Prop) (f : Finset (Assignment n) → ℝ)
    (S : Finset (Assignment n)) : ℝ := uniformMean (fun c => f (S.filter (sat c)))

def mixedAverage {X : Type*} (p : ℝ) (A B : (X → ℝ) → (X → ℝ))
    (f : X → ℝ) : X → ℝ := fun S => (1 - p) * B f S + p * A f S

def embedAuxiliaryClause {n v k : ℕ} (e : Fin v → Fin n) (C : AuxiliaryClause v k) :
    AuxiliaryClause n k := fun j => (e (C j).1, (C j).2)

def embeddedAverage {n v : ℕ} (e : Fin v → Fin n) (k : ℕ) :
    (Finset (Assignment n) → ℝ) → (Finset (Assignment n) → ℝ) :=
  finiteClauseAverage (fun C : AuxiliaryClause v k => fun σ => auxiliarySatisfies σ (embedAuxiliaryClause e C))

def auxiliaryAverage {n : ℕ} (k : ℕ) :
    (Finset (Assignment n) → ℝ) → (Finset (Assignment n) → ℝ) :=
  embeddedAverage (id : Fin n → Fin n) k

def auxiliarySurvival {n : ℕ} (k m : ℕ) (S : Finset (Assignment n)) : ℝ :=
  ((auxiliaryAverage k)^[m] alive) S

def auxiliaryProbability (n k m : ℕ) : ℝ :=
  auxiliarySurvival k m (Finset.univ : Finset (Assignment n))

def embeddedForced {n v : ℕ} (S : Finset (Assignment n)) (e : Fin v → Fin n) : Finset (Fin v) :=
  Finset.univ.filter (fun i => e i ∈ forcedVariables S)

@[simp] theorem mem_embeddedForced {n v : ℕ} (S : Finset (Assignment n)) (e : Fin v → Fin n) (i : Fin v) :
    i ∈ embeddedForced S e ↔ e i ∈ forcedVariables S := by simp [embeddedForced]

@[simp] theorem embeddedForced_id {n : ℕ} (S : Finset (Assignment n)) :
    embeddedForced S (id : Fin n → Fin n) = forcedVariables S := by ext i; simp

def blockSet {r s : ℕ} (S : Finset (Assignment r)) (T : Finset (Assignment s)) :
    Finset (Assignment (r + s)) :=
  Finset.univ.filter (fun σ => (fun i => σ (Fin.castAdd s i)) ∈ S ∧
    (fun i => σ (Fin.natAdd r i)) ∈ T)

@[simp] theorem mem_blockSet {r s : ℕ} (S : Finset (Assignment r)) (T : Finset (Assignment s))
    (σ : Assignment (r + s)) : σ ∈ blockSet S T ↔
      (fun i => σ (Fin.castAdd s i)) ∈ S ∧ (fun i => σ (Fin.natAdd r i)) ∈ T := by
  simp [blockSet]

@[simp] theorem blockSet_univ (r s : ℕ) :
    blockSet (Finset.univ : Finset (Assignment r)) (Finset.univ : Finset (Assignment s)) =
      Finset.univ := by ext σ; simp

end

end FixedClauseThreshold

end OAI


