-- Prove2me | Definitions.Def_DynEdgeColorLLL_Main_LLLTranscript
-- name    : DynEdgeColorLLL_Main_LLLTranscript
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-11T07:08:31.775703+00:00
-- url     : https://prove2.me/theorems/24dcdfc5-348a-4dbf-b7e0-a575b76c0c37
-- title:
--   Variable LLL instances, the [CPS14] parallel resampling transcript, 2-witness trees and dirty pairs
-- statement:
--   **Instances (§3.1).** There is a finite set $X$ of mutually independent random variables; variable $x$ has a domain $\Omega_x$ and a law $D_x$. Clauses carry distinct IDs in $[m]$. A family of truth tables $f_{C,U}$ says when clause $C$ is falsified if its variable set is $\mathrm{vbl}(C)=U$. The table $f_{C,U}$ depends only on the variables in $U$, a clause with no variables is satisfied, and every clause event is measurable. An instance at one moment is the map $C\mapsto\mathrm{vbl}(C)$.
--
--   The dependency graph $H$ joins two distinct clauses that share a variable, and $\Gamma_H^r(C)$ is the closed $r$-ball around $C$. The **parameters** are uniform bounds: every variable lies in at most $k$ clauses, every clause has at most $s$ variables, and $|\Gamma_H(C)|\le d$, with $k,s\ge1$ and $d\ge2$. **Assumption (1)**: for $q\in(0,1/2)$ there is $x:[m]\to[0,1)$ with $x(C)/(1-x(C))\le K$ such that, for every clause $A$,
--   $$\Pr[A]\le\frac{q}{4d^2}\,x(A)\prod_{B\in\Gamma_H^2(A)}\bigl(1-x(B)\bigr).$$
--
--   **The static algorithm (§3.2, Table 1).** The randomness tables $R(x,i)$, $i\ge0$, are independent, with $R(x,i)\sim D_x$, and $\sigma_0(x)=R(x,0)$. At stage $r\ge1$, $b_{C,r}$ records whether $C$ is falsified by $\sigma_{r-1}$. The counter is
--   $$\mathrm{cnt}_{C,r}=b_{C,r}\sum_{C'\in\Gamma_H(C)}[\mathrm{ID}(C')<\mathrm{ID}(C),\ b_{C',r}=1],$$
--   and $I_r=\{C:b_{C,r}=1,\ \mathrm{cnt}_{C,r}=0\}$. Every variable of a clause of $I_r$ is resampled: $b_{x,r}=[I_r\cap C(x)\ne\emptyset]$ and $\sigma_r(x)=R(x,\sum_{j\le r}b_{x,j})$. Further, $s_x=\sum_r b_{x,r}$, $r_x=\max(\{0\}\cup\{r:b_{x,r}=1\})$, and the output is $\sigma_\infty(x)=R(x,s_x)$. Stages after termination are empty.
--
--   **2-witness trees (Definition 1).** The resampling log lists the pairs $(r,C)$ with $C\in I_r$, ordered by stage and then by ID. The 2-witness tree of a log entry $L_i$ has as its nodes exactly the entries $L_j$, $j\le i$, joined to $L_i$ by a chain $j=j_0<j_1<\dots<j_t=i$ of log entries in which each label lies in $\Gamma^2_H$ of the next label. Its number of nodes does not depend on how ties are broken.
--
--   **Batches and dirty pairs (§3.3).** A batch $B$ of distinct clause updates $(C_i,x_i)$ toggles $x_i$ in $\mathrm{vbl}(C_i)$. Write $M=\{C_i\}$ and $H^\cup=H^{old}\cup H^{new}$. A pair $(C,r)$ is **dirty** when $(b^{old}_{C,r},\mathrm{cnt}^{old}_{C,r})\ne(b^{new}_{C,r},\mathrm{cnt}^{new}_{C,r})$, both transcripts using the same randomness tables.
--
--   **Formalization Note.** Variables form a finite type and clause IDs are `Fin m`. When $s_x=\infty$, an event of probability zero, $\sigma_\infty(x)$ takes the junk value $R(x,0)$.
-- source:
--   Sijin Peng, Mohsen Ghaffari, STOC 2027 submission #615 (October 2026), §3.1 Model and Main Result and assumption (1), printed pp. 9–10 (PDF pp. 11–12); §3.2, Equation (2), Table 1 and Definition 1, printed pp. 10–11 (PDF pp. 12–13); §3.3 dirty pairs, printed p. 11 (PDF p. 13)

import Mathlib

namespace DynEdgeColorLLL.Main

open MeasureTheory

/-! # Variable LLL instances, the [CPS14] parallel resampling transcript, and dirty pairs

Sijin Peng, Mohsen Ghaffari, STOC 2027 submission #615 (October 2026), §3.1 "Model and Main
Result", printed pp. 9–10 (PDF pp. 11–12); §3.2 "The Static Algorithm", Table 1 and Definition 1,
printed pp. 10–11 (PDF pp. 12–13); §3.3, printed p. 11 (PDF p. 13).

* Variables form a finite type `X`; variable `x` has domain `Ω x` with law `D x`. Clauses are the
  identifiers `C : Fin m` (the paper's IDs in `[m]`, compared through `C.val`).
* The truth-table family is `f C U σ`: "`C` is falsified by `σ` when `vbl(C) = U`". It depends
  only on the coordinates in `U`, and a clause with no variables is satisfied. An instance at one
  moment is the variable-set map `vbl`, and `C` is falsified by `σ` when `f C (vbl C) σ`.
* `H` is the dependency graph (two distinct clauses sharing a variable); `ball vbl r C` is the
  closed `r`-ball `Γ^r_H(C)` (it contains `C`).
* Randomness tables `τ x i`, `i ≥ 0`, independent with law `D x`; `σ_0(x) = τ x 0`. At stage
  `r ≥ 1`, `b_{C,r}` says that `C` is falsified by `σ_{r-1}`, `cnt_{C,r}` is Equation (2), `I_r`
  is the set of falsified clauses with `cnt = 0`, every variable of a clause of `I_r` is resampled,
  and `σ_r(x) = τ x (∑_{j ≤ r} b_{x,j})`. Stages after termination are empty automatically.
* The resampling log lists the pairs `(r, C)` with `C ∈ I_r`, ordered by stage and then by ID.
  The 2-witness tree of Definition 1 for a log entry `i` has as its node set exactly the entries
  `j` joined to `i` by a chain `j = j₀ < j₁ < ⋯ < j_t = i` of log entries in which each label lies
  in the closed 2-ball of the next one; its number of nodes does not depend on how ties among
  "deepest" nodes are broken, and `witnessSize` is that number. -/

variable {X : Type*} [Fintype X] [DecidableEq X] {Ω : X → Type*} {m : ℕ}

/-- A truth-table family for clauses `Fin m` over variables `X`: `f C U σ` holds when clause `C`
with variable set `U` is falsified by the assignment `σ`. -/
abbrev TruthTables (X : Type*) (Ω : X → Type*) (m : ℕ) :=
  Fin m → Finset X → ((x : X) → Ω x) → Prop

/-- The standing conventions of §3.1 on a truth-table family: `f C U` depends only on the
variables in `U`, a clause with no variables is satisfied, and every clause event is measurable. -/
def IsTruthTableFamily [∀ x, MeasurableSpace (Ω x)] (f : TruthTables X Ω m) : Prop :=
  (∀ C U (σ σ' : (x : X) → Ω x), (∀ x ∈ U, σ x = σ' x) → (f C U σ ↔ f C U σ')) ∧
    (∀ C σ, ¬ f C ∅ σ) ∧ ∀ C U, MeasurableSet {σ | f C U σ}

/-- The dependency graph `H` of the instance `vbl`: distinct clauses sharing a variable. -/
def depGraph (vbl : Fin m → Finset X) : SimpleGraph (Fin m) :=
  SimpleGraph.fromRel fun C C' => (vbl C ∩ vbl C').Nonempty

open Classical in
/-- `Γ^r_H(C)`: the clauses within distance at most `r` of `C` in `H`, including `C`. -/
noncomputable def ball (vbl : Fin m → Finset X) (r : ℕ) (C : Fin m) : Finset (Fin m) :=
  Finset.univ.filter fun C' => ∃ p : (depGraph vbl).Walk C C', p.length ≤ r

open Classical in
/-- The uniform parameter bounds of §3.1: every variable lies in at most `k` clauses, every
clause depends on at most `s` variables, `|Γ_H(C)| ≤ d`, with `k, s ≥ 1` and `d ≥ 2`. -/
def HasParams (vbl : Fin m → Finset X) (k s d : ℕ) : Prop :=
  1 ≤ k ∧ 1 ≤ s ∧ 2 ≤ d ∧
    (∀ x, (Finset.univ.filter fun C => x ∈ vbl C).card ≤ k) ∧
    (∀ C, (vbl C).card ≤ s) ∧ ∀ C, (ball vbl 1 C).card ≤ d

/-- Assumption (1) of §3.1 for the function `xw : Fin m → ℝ` with `max xw/(1 - xw) ≤ K`:
`0 ≤ xw C < 1`, `xw C/(1 - xw C) ≤ K`, and for every clause `A`,
`Pr[A] ≤ (q/4d²) xw(A) ∏_{B ∈ Γ²_H(A)} (1 - xw(B))`, where `Pr[A]` is the probability that `A`
is falsified under the product law of the variables. -/
def Assumption1 [∀ x, MeasurableSpace (Ω x)] (D : (x : X) → Measure (Ω x))
    (f : TruthTables X Ω m) (vbl : Fin m → Finset X) (d : ℕ) (q K : ℝ) (xw : Fin m → ℝ) :
    Prop :=
  (∀ C, 0 ≤ xw C ∧ xw C < 1) ∧ (∀ C, xw C / (1 - xw C) ≤ K) ∧
    ∀ A, (Measure.pi D).real {σ | f A (vbl A) σ} ≤
      q / (4 * (d : ℝ) ^ 2) * xw A * ∏ B ∈ ball vbl 2 A, (1 - xw B)

/-- The law of the randomness tables: `τ x i` independent over `x` and `i`, `τ x i ∼ D x`. -/
noncomputable def tableMeasure [∀ x, MeasurableSpace (Ω x)] (D : (x : X) → Measure (Ω x))
    [∀ x, IsProbabilityMeasure (D x)] : Measure ((x : X) → ℕ → Ω x) :=
  Measure.pi fun x => Measure.infinitePi fun _ : ℕ => D x

section Transcript

variable (f : TruthTables X Ω m) (vbl : Fin m → Finset X) (τ : (x : X) → ℕ → Ω x)

/-- The assignment reading entry `c x` of the table of every variable `x`. -/
def assignOf (c : X → ℕ) : (x : X) → Ω x := fun x => τ x (c x)

open Classical in
/-- Equation (2) under the assignment `σ`: zero unless `C` is falsified, otherwise the number of
falsified clauses `C' ∈ Γ_H(C)` with a smaller ID. -/
noncomputable def cntUnder (σ : (x : X) → Ω x) (C : Fin m) : ℕ :=
  if f C (vbl C) σ then
    ((ball vbl 1 C).filter fun C' => C'.val < C.val ∧ f C' (vbl C') σ).card
  else 0

/-- `C` is selected under `σ`: falsified and an ID local minimum among falsified clauses of
`Γ_H(C)` (`cnt = 0`). -/
def selectedUnder (σ : (x : X) → Ω x) (C : Fin m) : Prop :=
  f C (vbl C) σ ∧ cntUnder f vbl σ C = 0

open Classical in
/-- `resampCount r x = ∑_{j ≤ r} b_{x,j}`: the number of times `x` is resampled in stages
`1, …, r`. -/
noncomputable def resampCount : ℕ → X → ℕ
  | 0 => fun _ => 0
  | r + 1 => fun x => resampCount r x +
      if ∃ C, x ∈ vbl C ∧ selectedUnder f vbl (assignOf τ (resampCount r)) C then 1 else 0

/-- `σ_i`: the assignment after stage `i` (`σ_0(x) = τ x 0`). -/
noncomputable def stageAssign (i : ℕ) : (x : X) → Ω x :=
  assignOf τ (resampCount f vbl τ i)

/-- `b_{C,r}` (`r ≥ 1`): `C` is falsified by `σ_{r-1}`. -/
def bC (C : Fin m) (r : ℕ) : Prop :=
  f C (vbl C) (stageAssign f vbl τ (r - 1))

/-- `cnt_{C,r}` (`r ≥ 1`), Equation (2). -/
noncomputable def cntC (C : Fin m) (r : ℕ) : ℕ :=
  cntUnder f vbl (stageAssign f vbl τ (r - 1)) C

/-- `C ∈ I_r` (`r ≥ 1`): `b_{C,r} = 1` and `cnt_{C,r} = 0`. -/
def inI (r : ℕ) (C : Fin m) : Prop :=
  selectedUnder f vbl (stageAssign f vbl τ (r - 1)) C

/-- `b_{x,r} = [I_r ∩ C(x) ≠ ∅]` (`r ≥ 1`): `x` is resampled at stage `r`. -/
def bx (x : X) (r : ℕ) : Prop :=
  ∃ C, x ∈ vbl C ∧ inI f vbl τ r C

/-- `s_x = ∑_{r ≥ 1} b_{x,r}`, the total number of resamplings of `x` (possibly `⊤`). -/
noncomputable def sx (x : X) : ℕ∞ :=
  ⨆ r : ℕ, (resampCount f vbl τ r x : ℕ∞)

/-- `r_x = max({0} ∪ {r : b_{x,r} = 1})`, the last stage at which `x` is resampled (`⊤` if it is
resampled infinitely often). -/
noncomputable def rx (x : X) : ℕ∞ :=
  ⨆ (r : ℕ) (_ : 1 ≤ r ∧ bx f vbl τ x r), (r : ℕ∞)

/-- The final output `σ_∞(x) = τ x s_x`. (When `s_x = ⊤`, an event of probability zero by
Lemmas 1–2, the value is the junk entry `τ x 0`.) -/
noncomputable def finalAssign (x : X) : Ω x :=
  τ x (sx f vbl τ x).toNat

/-- The strict order of the resampling log: by stage, then by clause ID. -/
def LogLT (j i : ℕ × Fin m) : Prop :=
  j.1 < i.1 ∨ (j.1 = i.1 ∧ j.2.val < i.2.val)

/-- One link of a witness chain: `j` is a log entry before the log entry `i` and the label of `j`
lies in the closed 2-ball of the label of `i`. -/
def WitnessLink (j i : ℕ × Fin m) : Prop :=
  1 ≤ j.1 ∧ inI f vbl τ j.1 j.2 ∧ LogLT j i ∧ j.2 ∈ ball vbl 2 i.2

/-- The node labels of the 2-witness tree (Definition 1) of the log entry `i = (r, C)`: the log
entries joined to `i` by a witness chain, `i` included. -/
def witnessNodes (i : ℕ × Fin m) : Set (ℕ × Fin m) :=
  {j | Relation.ReflTransGen (WitnessLink f vbl τ) j i}

/-- The number of nodes of the 2-witness tree of the log entry `i` (Definition 1). -/
noncomputable def witnessSize (i : ℕ × Fin m) : ℕ :=
  Set.ncard (witnessNodes f vbl τ i)

/-- "The execution contains a 2-witness tree with root label `C` and at least `r` nodes": some
resampling event `(r', C)` of the log has a 2-witness tree with at least `r` nodes. -/
def HasWitnessTree (C : Fin m) (r : ℕ) : Prop :=
  ∃ r', 1 ≤ r' ∧ inI f vbl τ r' C ∧ r ≤ witnessSize f vbl τ (r', C)

end Transcript

section Batch

/-- The new variable sets after the batch `B` of distinct clause updates: `(C, x) ∈ B` adds `x`
to `vbl(C)` when `x ∉ vbl(C)` and removes it otherwise. -/
def applyBatch (vbl : Fin m → Finset X) (B : Finset (Fin m × X)) : Fin m → Finset X :=
  fun C => symmDiff (vbl C) ((B.filter fun p => p.1 = C).image Prod.snd)

/-- `M = {C_i}`: the clauses touched by the batch. -/
def touched (B : Finset (Fin m × X)) : Finset (Fin m) :=
  B.image Prod.fst

/-- `H^∪ = H^old ∪ H^new`. -/
def unionDepGraph (vbl vbl' : Fin m → Finset X) : SimpleGraph (Fin m) :=
  depGraph vbl ⊔ depGraph vbl'

/-- `(C, r)` is dirty: `(b^old_{C,r}, cnt^old_{C,r}) ≠ (b^new_{C,r}, cnt^new_{C,r})`, the two
transcripts using the same randomness table `τ`. -/
def IsDirty (f : TruthTables X Ω m) (vbl vbl' : Fin m → Finset X) (τ : (x : X) → ℕ → Ω x)
    (C : Fin m) (r : ℕ) : Prop :=
  ¬ ((bC f vbl τ C r ↔ bC f vbl' τ C r) ∧ cntC f vbl τ C r = cntC f vbl' τ C r)

end Batch

end DynEdgeColorLLL.Main


