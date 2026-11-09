-- Prove2me | Definitions.Def_ForestPersuasion_Symmetric_LPs
-- name    : ForestPersuasion_Symmetric_LPs
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-08T10:23:38.718934+00:00
-- url     : https://prove2.me/theorems/592d2644-1fb0-4b67-9a83-2afbba3e9dd4
-- title:
--   The grid LP, its relaxation, and the explicit dual
-- statement:
--   For each state $w$ and grid vector $\bar l$, a nonnegative variable $x^w_{\bar l}$ sums to $1$ over $\bar l$. LP (1) imposes Bayes consistency for each receiver's full descendant-grid observation. LP (2) retains consistency conditional on its own posterior and descendant adoption count, and the parent-posterior conditional-mean equations. Both maximize
--   $$\sum_{\bar l}u(S(\bar l))\bigl(\mu x^1_{\bar l}+(1-\mu)x^0_{\bar l}\bigr).$$
--
--   The displayed coefficient matrices implement every equality as two opposite inequalities, with identity rows for nonnegativity, using the published generic LP feasibility definition. The objective-value image retains feasible witnesses; it is not used to define $V^*$.
--
--   LP (6) has free variables $\alpha,\beta,\gamma^i_{\kappa,l},\delta^{j,i}_{\kappa,l}$, objective $\alpha+\beta$, and the two explicit constraint families from PDF p. 14. The dual arrays are extended to all natural count indices and all pairs of vertices; only $\kappa<d_i$ and actual edges occur in the program, so unused entries change no feasible effective dual point.
--
--   This bundle supplies the paper-specific LP data on the shared linear-program substrate.
-- source:
--   Konstantin Zabarnyi, Designing Information in a Forest: Algorithmic Aspects, STOC 2027 submission #271 (October 2026; PDF dated November 2, 2026), Lemma 5, LP (1); §5, LP (2) and LP (6), PDF pp. 9, 12, 14 (printed pp. 8, 11, 13). https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/271.pdf

import Mathlib
import Definitions.Def_ForestPersuasion_Symmetric_Grid
import Definitions.Def_ModernConvex_LPDuality_LinearProgram

open scoped NNReal ENNReal
open Classical
noncomputable section

namespace ForestPersuasion.Symmetric

/-- An equality-and-nonnegativity adapter to the published generic LP interface.
Each equality is two opposite inequality rows; identity rows impose nonnegativity. -/
def equalityMatrix {R C : Type} [Fintype R] [Fintype C]
    (A : Matrix R C ℝ) : Matrix ((Bool × R) ⊕ C) C ℝ :=
  fun r c => match r with
    | .inl (s, r) => if s then A r c else -A r c
    | .inr c' => if c' = c then 1 else 0

def equalityRhs {R C : Type} (b : R → ℝ) : ((Bool × R) ⊕ C) → ℝ :=
  fun r => match r with
    | .inl (s, r) => if s then b r else -b r
    | .inr _ => 0

abbrev Columns {n : ℕ} (I : Model n) := Bool × GridVector I
abbrev Weights {n : ℕ} (I : Model n) := Columns I → ℝ

/-- i as an element of its own observed descendant subtree. -/
def selfNode {n : ℕ} (I : Model n) (i : Fin n) :
    {j // j ∈ I.hierarchy.descendants i} :=
  ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ _, Relation.ReflTransGen.refl⟩⟩

abbrev EqRows1 {n : ℕ} (I : Model n) :=
  Bool ⊕ (Σ i : Fin n, SubtreeVector I i)

instance eqRows1Fintype {n : ℕ} (I : Model n) : Fintype (EqRows1 I) :=
  inferInstanceAs (Fintype (Bool ⊕ (Σ i : Fin n, SubtreeVector I i)))

/-- Coefficients of the equality rows of LP (1), PDF p. 9. -/
def matrix1 {n : ℕ} (I : Model n) : Matrix (EqRows1 I) (Columns I) ℝ :=
  fun r c => match r with
    | .inl w => if c.1 = w then 1 else 0
    | .inr ⟨i, q⟩ =>
      if (∀ j : {j // j ∈ I.hierarchy.descendants i}, c.2 j.val = q j) then
        if c.1 then (1 - (q (selfNode I i)).val) * I.prior
        else -(q (selfNode I i)).val * (1 - I.prior)
      else 0

def rhs1 {n : ℕ} (I : Model n) : EqRows1 I → ℝ :=
  Sum.elim (fun _ => 1) (fun _ => 0)

def LP1Feasible {n : ℕ} (I : Model n) (X : Weights I) : Prop :=
  ModernConvex.LPDuality.PrimalFeasible (equalityMatrix (matrix1 I)) (equalityRhs (rhs1 I)) X

/-- κ ranges over 0,...,d_i-1; q over the distinct grid. -/
abbrev MarginalRows {n : ℕ} (I : Model n) :=
  Σ i : Fin n, Fin (I.hierarchy.descendants i).card × Grid I

abbrev EdgeRows {n : ℕ} (I : Model n) :=
  Σ e : {e // e ∈ I.hierarchy.edges},
    Fin (I.hierarchy.descendants e.val.2).card × Grid I

abbrev EqRows2 {n : ℕ} (I : Model n) := Bool ⊕ (MarginalRows I ⊕ EdgeRows I)

/-- Coefficients of the two relaxed constraint families, with (j,i) parent to child. -/
def matrix2 {n : ℕ} (I : Model n) : Matrix (EqRows2 I) (Columns I) ℝ :=
  fun r c => match r with
    | .inl w => if c.1 = w then 1 else 0
    | .inr (.inl ⟨i, κ, q⟩) =>
      if c.2 i = q ∧ k I c.2 i = κ.val then
        if c.1 then (1 - q.val) * I.prior else -q.val * (1 - I.prior)
      else 0
    | .inr (.inr ⟨e, κ, q⟩) =>
      if c.2 e.val.2 = q ∧ k I c.2 e.val.2 = κ.val then
        ((c.2 e.val.1).val - q.val) * (if c.1 then I.prior else 1 - I.prior)
      else 0

def rhs2 {n : ℕ} (I : Model n) : EqRows2 I → ℝ :=
  Sum.elim (fun _ => 1) (fun _ => 0)

def LP2Feasible {n : ℕ} (I : Model n) (X : Weights I) : Prop :=
  ModernConvex.LPDuality.PrimalFeasible (equalityMatrix (matrix2 I)) (equalityRhs (rhs2 I)) X

/-- Shared maximization objective of LP (1) and LP (2). -/
def objective {n : ℕ} (I : Model n) (u : SenderUtility n) (X : Weights I) : ℝ :=
  ∑ l : GridVector I, (u (gridAdopters I l) : ℝ) *
    (I.prior * X (true, l) + (1 - I.prior) * X (false, l))

def lpValues {n : ℕ} (I : Model n) (u : SenderUtility n)
    (feasible : Weights I → Prop) : Set ℝ :=
  {v | ∃ X, feasible X ∧ objective I u X = v}

/-- Free dual arrays, extended to natural κ and nonedges. Only κ<d_i and edges
are ever read by LP (6) or the dynamic program. Extra entries are ignored. -/
structure DualCoefficients {n : ℕ} (I : Model n) where
  gamma : Fin n → ℕ → Grid I → ℝ
  delta : (Fin n × Fin n) → ℕ → Grid I → ℝ

structure DualPoint {n : ℕ} (I : Model n) where
  alpha : ℝ
  beta : ℝ
  coefficients : DualCoefficients I

/-- Both inequality families of the dual LP (6), PDF p. 14. -/
def LP6Feasible {n : ℕ} (I : Model n) (f : Fin (n + 1) → ℝ≥0)
    (y : DualPoint I) : Prop :=
  ∀ l : GridVector I,
    I.prior * (symmetricUtility f (gridAdopters I l) : ℝ) ≤
      y.alpha + I.prior * (∑ i, (1 - (l i).val) * y.coefficients.gamma i (k I l i) (l i)) +
        I.prior * (∑ e ∈ I.hierarchy.edges,
          ((l e.1).val - (l e.2).val) * y.coefficients.delta e (k I l e.2) (l e.2)) ∧
    (1 - I.prior) * (symmetricUtility f (gridAdopters I l) : ℝ) ≤
      y.beta - (1 - I.prior) * (∑ i, (l i).val * y.coefficients.gamma i (k I l i) (l i)) +
        (1 - I.prior) * (∑ e ∈ I.hierarchy.edges,
          ((l e.1).val - (l e.2).val) * y.coefficients.delta e (k I l e.2) (l e.2))

def dualObjective {n : ℕ} (I : Model n) (y : DualPoint I) : ℝ := y.alpha + y.beta

end ForestPersuasion.Symmetric


