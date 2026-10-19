-- Prove2me | Definitions.Def_OAI_Analysis_RecursivePotentials_VariableEstimates
-- name    : OAI_Analysis_RecursivePotentials_VariableEstimates
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-18T07:39:41.010295+00:00
-- url     : https://prove2.me/theorems/f94093b1-b5b9-4da3-befe-8d2c54b2d062
-- title:
--   Exit cuts, tight labels, increments and tail flux for $\ell^p$-aggregated tree potentials
-- statement:
--   This file introduces the bookkeeping objects (exit cuts, tight labels, increments, coefficients, cut energies and tail fluxes) used to estimate the $\ell^p$-aggregated tree norms, together with a few elementary symmetry facts about the $\ell^p$ potentials.
--
--   **Setting.** Throughout, $T$ is a rooted tree on a finite index set $I$: a root $r$, a parent map $\pi:I\to I$ with $\pi(r)=r$, and a depth $d:I\to\mathbb N$ with $d(r)=0$ and $d(\pi(s))<d(s)$ for $s\neq r$; the children $\mathrm{ch}(s)$ of $s$ are the nodes $c\neq r$ with $\pi(c)=s$. Let $p\ge1$ be real. For a finite set $S$ and $f:S\to\mathbb R$ put $\|f\|_{p,S}=\big(\sum_{i\in S}|f(i)|^p\big)^{1/p}$. For any $v:I\to\mathbb R$ the $\ell^p$-potentials $(P_v,Q_v)$ are defined from the leaves upward by
--
--   $$
--   P_v(s)=\max\big(A_s,\ v(s)+B_s\big),\qquad Q_v(s)=\max\big(B_s,\ -v(s)+A_s\big),
--   $$
--
--   where $A_s=\big(\sum_{c\in\mathrm{ch}(s)}P_v(c)^p\big)^{1/p}$ and $B_s=\big(\sum_{c\in\mathrm{ch}(s)}Q_v(c)^p\big)^{1/p}$; the root sum is $\|v\|_p=P_v(r)+Q_v(r)$. The potentials are nonnegative with $P_v-Q_v=v$. The file first records: for $a\ge0$, $\|f\|_{p,S}\le a$ if and only if $\sum_{i\in S}|f(i)|^p\le a^p$; $\|{-f}\|_{p,S}=\|f\|_{p,S}$; at every node one of the two maxima is attained by its first argument, i.e. $P_v(s)=A_s$ or $Q_v(s)=B_s$ (tightness); the potentials of $v=0$ vanish; and $P_{-v}=Q_v$, $Q_{-v}=P_v$, so that $\|0\|_p=0$ and $\|{-v}\|_p=\|v\|_p$.
--
--   The definitions are as follows. Below $H\subseteq I$ is any subset, $j\in\mathbb N$, $x,y:I\to\mathbb R$, labels $b\in\{\mathsf P,\mathsf Q\}$ select one of the two potentials, and signs $\sigma\in\{+1,-1\}$ select one of $x\pm y$.
--
--   1. **Recurrence ceiling.** The constant $C=3e$.
--
--   2. **First exits.** $\mathrm{Exit}(H)=\{s\in I: s\notin H,\ \pi(s)\in H\}$, the nodes just outside $H$.
--
--   3. **Stopped exits.** $\mathrm{Exit}_{\le j}(H)=\{s\in\mathrm{Exit}(H): d(s)\le j\}$.
--
--   4. **Exit cuts.** $\mathrm{Cut}_j(H)=\{s\in H: d(s)=j\}\cup\mathrm{Exit}_{\le j}(H)$: the level $j$ of $H$ together with the exits already passed.
--
--   5. **Cut energy.** For a real exponent $q$ and $D:\{+1,-1\}\times I\to\mathbb R$,
--   $$
--   \mathcal K_j(q,H,D)=\Big(\sum_{\sigma\in\{+1,-1\}}\ \sum_{s\in\mathrm{Cut}_j(H)}D(\sigma,s)^q\Big)^{1/q}.
--   $$
--
--   6. **Labelled fields.** $F_v(\mathsf P,s)=P_v(s)$ and $F_v(\mathsf Q,s)=Q_v(s)$.
--
--   7. **Tight label.** $\beta_v(s)\in\{\mathsf P,\mathsf Q\}$ is a label, fixed by choice, for which the $p$-th power of the field is carried by the children:
--   $$
--   F_v(\beta_v(s),s)^p=\sum_{c\in\mathrm{ch}(s)}F_v(\beta_v(s),c)^p ;
--   $$
--   such a label exists by tightness.
--
--   8. **Signed perturbation.** $\sigma y$ is $y$ for $\sigma=+1$ and $-y$ for $\sigma=-1$.
--
--   9. **Increments.**
--   $$
--   \delta_\sigma(s)=\begin{cases}P_{x+\sigma y}(s)-P_x(s), & s\in H,\\ F_{x+\sigma y}\big(\beta_x(\pi(s)),s\big), & s\notin H.\end{cases}
--   $$
--
--   10. **Coefficients.**
--   $$
--   \gamma_\sigma(s)=\begin{cases}F_{x+\sigma y}\big(\beta_x(s),s\big), & s\in H,\\ \delta_\sigma(s), & s\notin H.\end{cases}
--   $$
--
--   11. **Tail flux.**
--   $$
--   \Phi_y(s)=\begin{cases}P_y(s)^p, & s\in H,\\ P_y(s)^p+Q_y(s)^p, & s\notin H.\end{cases}
--   $$
--
--   These quantities serve the cubic-type stability estimate for the norms $\|\cdot\|_p$ with $p=1+1/h$ on trees of height at most $h$ in which each child is exactly one level below its parent. There $x$ vanishes outside an initial set $H$ (one containing $r$ and closed under $\pi$) and $y$ vanishes on $H$. The exit cuts sweep through $H$ level by level, the increments record by how much the potentials of $x\pm y$ exceed those of $x$ along the tight labels, the cut energies $\mathcal K_j(p,H,\delta)$ of the increments obey a level-by-level recursion controlled by the ceiling $C$, and the tail flux compares $\|y\|_p$ with the increments on the exits. The constant $(2C)^{-3}=(6e)^{-3}$ is the constant of the resulting cubic estimate.
--
--   **Formalization Note** The tree is a `FiniteRootedTree` on a `Fintype` index, the exponent is a `ChildExponent` (a real number at least $1$), $\|f\|_{p,S}$ is `ChildExponent.agg`, the potentials are `FiniteRootedTree.pfields` and $\|v\|_p$ is `pRootSum`. Labels and signs are both Booleans: `pField v true` is $P_v$ and `pField v false` is $Q_v$, while `signed y true = y` and `signed y false = -y`. `tightLabel` is obtained by `Classical.choose` from `exists_tight_label`. `cutEnergy` takes an arbitrary real exponent and uses `Real.rpow`; it is intended for nonnegative data, since for negative bases `Real.rpow` follows Lean's own convention. None of the definitions imposes hypotheses on $H$, $x$ or $y$. Lean names: `recurrenceCeiling`, `firstExit`, `stoppedExit`, `exitCut` (built from `headLevel H j`), `cutEnergy`, `pField`, `tightLabel`, `signed`, `increment`, `coefficient`, `tailFlux`; the facts above are `agg_le_iff`, `agg_neg`, `pfields_tight`, `pfields_zero`, `pfields_neg`, `pRootSum_zero`, `pRootSum_neg`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/RecursivePotentials/VariableEstimates.lean

-- Generated from openai/math@1581d4c lean/OAI/Analysis/RecursivePotentials/VariableEstimates.lean by skeleton subtraction
-- (upload_full_project.md Phase 3): Definitions bundle for the RecursivePotentials mission closure.
-- Kept: reachable definitions/instances and the theorems their bodies or the node statements cite.
-- Project imports rewritten to platform modules; otherwise byte-identical to the source.
import Mathlib
import Definitions.Def_RecursivePotentials
import Definitions.Def_OAI_Analysis_RecursivePotentials_Model
import Definitions.Def_OAI_Analysis_RecursivePotentials_TreeGeometry
import Definitions.Def_OAI_Analysis_RecursivePotentials_ZeroRootGeometry
import Definitions.Def_OAI_Analysis_RecursivePotentials_EquivalentNorms
import Definitions.Def_OAI_Analysis_RecursivePotentials_JoinedGeometry

-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

universe uIndex uSpace uOther uDomain uTarget uFiber

open scoped BigOperators

namespace RecursivePotentials

open Filter Topology

open Filter Topology

open scoped ENNReal

open UniformSpace

open Filter

open scoped Topology

namespace FiniteRootedTree

end FiniteRootedTree

namespace ChildExponent

noncomputable section

variable (p : ChildExponent)

lemma agg_le_iff {ι : Type uIndex} (s : Finset ι) (f : ι → ℝ) {a : ℝ} (ha : 0 ≤ a) :
    p.agg s f ≤ a ↔ (∑ i ∈ s, |f i| ^ p.val) ≤ a ^ p.val := by
  rw [← p.agg_rpow]
  exact (Real.rpow_le_rpow_iff (p.agg_nonneg s f) ha p.pos).symm

@[simp] lemma agg_neg {ι : Type uIndex} (s : Finset ι) (f : ι → ℝ) : p.agg s (-f) = p.agg s f := by
  simp [agg]

end

end ChildExponent

namespace FiniteRootedTree

noncomputable section

variable {ι : Type uIndex} [indexFinite : Fintype ι] [indexDecidable : DecidableEq ι]
    (T : FiniteRootedTree ι) (p : ChildExponent)

lemma pfields_tight (v : ι → ℝ) (s : ι) :
    (T.pfields p v s).1 = p.agg (T.children s) (fun c => (T.pfields p v c).1) ∨
    (T.pfields p v s).2 = p.agg (T.children s) (fun c => (T.pfields p v c).2) := by
  simpa only [← T.pfields_eq] using leastPair_tight (v s)
    (p.agg (T.children s) (fun c => (T.pfields p v c).1))
    (p.agg (T.children s) (fun c => (T.pfields p v c).2))

lemma PUpper.zero : T.PUpper p (fun _ => 0) := by intro s; simp

lemma pfields_zero (s : ι) : T.pfields p (fun _ => 0) s = (0,0) := by
  have hm := T.pfields_minimal p (fun _ => 0) (fun _ => 0) (fun _ => 0)
    (fun _ => le_rfl) (fun _ => le_rfl) (fun _ => by ring) (PUpper.zero T p) (PUpper.zero T p) s
  have hn := T.pfields_nonneg p (fun _ => 0) s
  exact Prod.ext (le_antisymm hm.1 hn.1) (le_antisymm hm.2 hn.2)

lemma pfields_neg (v : ι → ℝ) (s : ι) :
    T.pfields p (-v) s = ((T.pfields p v s).2, (T.pfields p v s).1) := by
  have h₁ := T.pfields_minimal p (-v) (fun s => (T.pfields p v s).2)
    (fun s => (T.pfields p v s).1)
    (fun s => (T.pfields_nonneg p v s).2) (fun s => (T.pfields_nonneg p v s).1)
    (fun s => by dsimp; linarith [T.pfields_difference p v s])
    (T.pfields_upper p v).2 (T.pfields_upper p v).1 s
  have h₂ := T.pfields_minimal p v (fun s => (T.pfields p (-v) s).2)
    (fun s => (T.pfields p (-v) s).1)
    (fun s => (T.pfields_nonneg p (-v) s).2) (fun s => (T.pfields_nonneg p (-v) s).1)
    (fun s => by have := T.pfields_difference p (-v) s; dsimp at this; linarith)
    (T.pfields_upper p (-v)).2 (T.pfields_upper p (-v)).1 s
  exact Prod.ext (le_antisymm h₁.1 h₂.2) (le_antisymm h₁.2 h₂.1)

@[simp] lemma pRootSum_zero : T.pRootSum p (fun _ => 0) = 0 := by simp [pRootSum, T.pfields_zero]
@[simp] lemma pRootSum_neg (v : ι → ℝ) : T.pRootSum p (-v) = T.pRootSum p v := by
  simp [pRootSum, T.pfields_neg, add_comm]

end

end FiniteRootedTree

namespace VariableExponent

noncomputable section

def recurrenceCeiling : ℝ := 3 * Real.exp 1

end

end VariableExponent

namespace FiniteRootedTree

noncomputable section

variable {ι : Type uIndex} [indexFinite : Fintype ι] [indexDecidable : DecidableEq ι]
    (T : FiniteRootedTree ι)

def firstExit (H : Finset ι) : Finset ι := Finset.univ.filter fun s => s ∉ H ∧ T.parent s ∈ H

def stoppedExit (H : Finset ι) (j : ℕ) : Finset ι := (T.firstExit H).filter fun s => T.depth s ≤ j

def exitCut (H : Finset ι) (j : ℕ) : Finset ι := T.headLevel H j ∪ T.stoppedExit H j

end

end FiniteRootedTree

namespace VariableExponent

end VariableExponent

namespace FiniteRootedTree

noncomputable section

variable {ι : Type uIndex} [indexFinite : Fintype ι] [indexDecidable : DecidableEq ι]
    (T : FiniteRootedTree ι)

end

end FiniteRootedTree

namespace VariableExponent

noncomputable section

variable {ι : Type uIndex} [indexFinite : Fintype ι] [indexDecidable : DecidableEq ι]
    (T : FiniteRootedTree ι)

def cutEnergy (p : ℝ) (H : Finset ι) (d : Bool → ι → ℝ) (j : ℕ) : ℝ :=
  (∑ σ, ∑ s ∈ T.exitCut H j, d σ s ^ p) ^ (1/p)

end

end VariableExponent

namespace FiniteRootedTree

noncomputable section

variable {ι : Type uIndex} [indexFinite : Fintype ι] [indexDecidable : DecidableEq ι]
    (T : FiniteRootedTree ι) (p : ChildExponent)

def pField (v : ι → ℝ) (b : Bool) (s : ι) :
    ℝ := if b then (T.pfields p v s).1 else (T.pfields p v s).2

lemma exists_tight_label (v : ι → ℝ) (s : ι) :
    ∃ b : Bool, T.pField p v b s ^ p.val = ∑ c ∈ T.children s, T.pField p v b c ^ p.val := by
  rcases T.pfields_tight p v s with h | h
  · refine ⟨true, ?_⟩
    simp only [pField, ite_true]
    rw [h, p.agg_rpow]
    apply Finset.sum_congr rfl
    intro c hc; rw [abs_of_nonneg (T.pfields_nonneg p v c).1]
  · refine ⟨false, ?_⟩
    simp only [pField, Bool.false_eq_true, ite_false]
    rw [h, p.agg_rpow]
    apply Finset.sum_congr rfl
    intro c hc; rw [abs_of_nonneg (T.pfields_nonneg p v c).2]

def tightLabel (v : ι → ℝ) (s : ι) : Bool := (T.exists_tight_label p v s).choose

end

end FiniteRootedTree

namespace VariableExponent

noncomputable section

variable {ι : Type uIndex}

def signed (y : ι → ℝ) (σ : Bool) : ι → ℝ := if σ then y else -y

@[simp] lemma signed_true (y : ι → ℝ) : signed y true = y := rfl

@[simp] lemma signed_false (y : ι → ℝ) : signed y false = -y := rfl

variable [indexFinite : Fintype ι] [indexDecidable : DecidableEq ι] (T : FiniteRootedTree ι)
    (p : ChildExponent)

variable (H : Finset ι) (x y : ι → ℝ)

def increment (σ : Bool) (s : ι) : ℝ :=
  if s ∈ H then T.pField p (x + signed y σ) true s - T.pField p x true s
  else T.pField p (x + signed y σ) (T.tightLabel p x (T.parent s)) s

def coefficient (σ : Bool) (s : ι) : ℝ :=
  if s ∈ H then T.pField p (x + signed y σ) (T.tightLabel p x s) s
  else increment T p H x y σ s

variable {H x y} (hH : T.Initial H) (hx : ∀ s ∉ H, x s = 0) (hy : ∀ s ∈ H, y s = 0)

end

end VariableExponent

namespace FiniteRootedTree

noncomputable section

variable {ι : Type uIndex} [indexFinite : Fintype ι] [indexDecidable : DecidableEq ι]
    (T : FiniteRootedTree ι) (p : ChildExponent)

end

end FiniteRootedTree

namespace VariableExponent

noncomputable section

variable {ι : Type uIndex} [indexFinite : Fintype ι] [indexDecidable : DecidableEq ι]
    (T : FiniteRootedTree ι) (p : ChildExponent)

variable {H : Finset ι} {x y : ι → ℝ} (hH : T.Initial H)
    (hx : ∀ s ∉ H, x s = 0) (hy : ∀ s ∈ H, y s = 0)
    (hstep : ∀ c, c ≠ T.root → T.depth c = T.depth (T.parent c) + 1)

def tailFlux (H : Finset ι) (y : ι → ℝ) (s : ι) : ℝ :=
  if s ∈ H then T.pField p y true s ^ p.val
  else T.pField p y true s ^ p.val + T.pField p y false s ^ p.val

end

end VariableExponent

end RecursivePotentials

end OAI


