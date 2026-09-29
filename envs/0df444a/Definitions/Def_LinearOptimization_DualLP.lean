-- Prove2me | Definitions.Def_LinearOptimization_DualLP
-- name    : LinearOptimization_DualLP
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-08-05T17:50:46.853292+00:00
-- url     : https://prove2.me/theorems/10f5f1f2-c0d8-4ce1-a596-ca6e8d962837
-- title:
--   The dual linear programming problem
-- statement:
--   **(The dual problem, §4.2 pp. 142-143 and Table 4.1)** Let $A$ be a matrix with rows $a_i'$ and columns $A_j$. Given a primal problem $\min c'x$ subject to
--
--   - $a_i'x \ge b_i$ ($i \in M_1$),
--   - $a_i'x \le b_i$ ($i \in M_2$),
--   - $a_i'x = b_i$ ($i \in M_3$),
--   - $x_j \ge 0$ ($j \in N_1$),
--   - $x_j \le 0$ ($j \in N_2$),
--   - $x_j$ free ($j \in N_3$),
--
--   its dual is defined to be the maximization problem $\max p'b$ subject to
--
--   - $p_i \ge 0$ ($i \in M_1$),
--   - $p_i \le 0$ ($i \in M_2$),
--   - $p_i$ free ($i \in M_3$),
--   - $p'A_j \le c_j$ ($j \in N_1$),
--   - $p'A_j \ge c_j$ ($j \in N_2$),
--   - $p'A_j = c_j$ ($j \in N_3$).
--
--   For each constraint in the primal (other than the sign constraints) we introduce a variable in the dual; for each variable in the primal, we introduce a constraint in the dual.
--
--   In particular (p. 143): the dual of the standard-form problem $\min c'x$, $Ax = b$, $x \ge 0$ is $\max p'b$, $p'A \le c'$; the dual of $\min c'x$, $Ax \ge b$ is $\max p'b$, $p'A = c'$, $p \ge 0$.
-- source:
--   Bertsimas & Tsitsiklis, Introduction to Linear Optimization, Athena Scientific, 1997, §4.2, pp. 142-143, incl. Table 4.1

import Definitions.Def_ActiveConstraints
import Definitions.Def_Polyhedron

/-!
General-form linear programs and their duals.

Source: Bertsimas & Tsitsiklis, *Introduction to Linear Optimization*,
Athena Scientific 1997, §4.2 pp. 142–144:

- **The dual problem (pp. 142–143, Table 4.1).** Let `A` be a matrix with
  rows `aᵢ'` and columns `Aⱼ`. Given the primal `min c'x` subject to
  `aᵢ'x ≥ bᵢ (i ∈ M₁)`, `aᵢ'x ≤ bᵢ (i ∈ M₂)`, `aᵢ'x = bᵢ (i ∈ M₃)`,
  `xⱼ ≥ 0 (j ∈ N₁)`, `xⱼ ≤ 0 (j ∈ N₂)`, `xⱼ` free `(j ∈ N₃)`, its dual is
  the maximization problem `max p'b` subject to `pᵢ ≥ 0 (i ∈ M₁)`,
  `pᵢ ≤ 0 (i ∈ M₂)`, `pᵢ` free `(i ∈ M₃)`, `p'Aⱼ ≤ cⱼ (j ∈ N₁)`,
  `p'Aⱼ ≥ cⱼ (j ∈ N₂)`, `p'Aⱼ = cⱼ (j ∈ N₃)`.
- **The equivalent-minimization conversion (p. 144, Example 4.1).** "We
  transform the dual into an equivalent minimization problem … and
  multiply the … constraints by −1": `max p'b` becomes `min (−b)'p`, and
  each dual constraint `p'Aⱼ ⋈ cⱼ` becomes `(−Aⱼ)'p ⋈' (−cⱼ)` with the
  inequality reversed; the sign constraints are unchanged. This conversion
  does not change the feasible set.

Design: one structure `GeneralFormLP` (minimization orientation, the
book's standing convention p. 143) carries the data `(A, b, c)` plus the
row tags `M₁/M₂/M₃` (reusing `ConstraintRel`) and the variable tags
`N₁/N₂/N₃` (`VarSign`). The dual operator `dualLP` produces the dual **in
the book's equivalent-minimization form**, so that it maps minimization
problems to minimization problems and Theorem 4.1 ("the dual of the dual
is the primal") becomes an exact identity of general-form data. Since the
conversion leaves the feasible set unchanged, `generalFeasibleSet (dualLP P)`
is literally the Table 4.1 dual feasible set; the dual VALUE is the
supremum of `p'b` over it (maximization orientation, `EReal`-valued:
`⊥` = infeasible, `⊤` = unbounded — mirroring `lpValue`'s trichotomy
encoding, Table 4.2 p. 151). The standard-form and inequality-form pairs
displayed on p. 143 are definitional specializations, proved below.
-/

open Matrix

namespace LinearOptimization

/-- The sign tag of one variable of a general-form LP: the book's index
sets `N₁` (`xⱼ ≥ 0`), `N₂` (`xⱼ ≤ 0`), `N₃` (`xⱼ` free) — Bertsimas & Tsitsiklis, §4.2
p. 142. -/
inductive VarSign : Type
  | nonneg : VarSign
  | nonpos : VarSign
  | free : VarSign
deriving DecidableEq

/-- The scalar `t` satisfies the sign tag. -/
def VarSign.IsSatisfiedBy : VarSign → ℝ → Prop
  | .nonneg, t => 0 ≤ t
  | .nonpos, t => t ≤ 0
  | .free, _ => True

/-- A linear program in the book's general form (Bertsimas & Tsitsiklis, §4.2 p. 142,
minimization orientation): `min c'x` subject to `aᵢ'x ⋈ᵢ bᵢ` for each row
`i` (tag `rowRel i` ∈ {≥, ≤, =}, the index sets `M₁/M₂/M₃`) and the sign
constraint `colSign j` on each variable `xⱼ` (the index sets
`N₁/N₂/N₃`). -/
structure GeneralFormLP (m n : ℕ) : Type where
  /-- The constraint matrix (rows `aᵢ'`, columns `Aⱼ`). -/
  A : Matrix (Fin m) (Fin n) ℝ
  /-- The right-hand side. -/
  b : Fin m → ℝ
  /-- The cost vector. -/
  c : Fin n → ℝ
  /-- The relation tag of each row constraint (`M₁`/`M₂`/`M₃`). -/
  rowRel : Fin m → ConstraintRel
  /-- The sign tag of each variable (`N₁`/`N₂`/`N₃`). -/
  colSign : Fin n → VarSign

/-- The feasible set of a general-form LP: all row constraints and all
variable sign constraints hold. -/
def generalFeasibleSet {m n : ℕ} (P : GeneralFormLP m n) : Set (Fin n → ℝ) :=
  {x | (∀ i, (LinearConstraint.mk (P.A i) (P.b i) (P.rowRel i)).IsSatisfiedAt x) ∧
    ∀ j, (P.colSign j).IsSatisfiedBy (x j)}

/-- Table 4.1, constraints column (Bertsimas & Tsitsiklis, p. 143): a primal row constraint
tagged `≥ / ≤ / =` yields a dual variable tagged `≥ 0 / ≤ 0 /` free. -/
def ConstraintRel.dualSign : ConstraintRel → VarSign
  | .ge => .nonneg
  | .le => .nonpos
  | .eq => .free

/-- Table 4.1, variables column, after the p. 144 multiplication by `−1`:
a primal variable tagged `≥ 0 / ≤ 0 /` free yields the dual constraint
`p'Aⱼ ≤ cⱼ / ≥ cⱼ / = cⱼ`, i.e. `(−Aⱼ)'p ≥ −cⱼ / ≤ −cⱼ / = −cⱼ` in the
equivalent-minimization form. -/
def VarSign.dualRel : VarSign → ConstraintRel
  | .nonneg => .ge
  | .nonpos => .le
  | .free => .eq

/-- **Bertsimas & Tsitsiklis, §4.2 (pp. 142–144).** The dual of the general-form LP `P`, in
the book's equivalent-minimization form (p. 144): `min (−b)'p` subject to
`(−Aⱼ)'p ⋈ −cⱼ` (one row per primal variable, relation per Table 4.1 with
the inequality reversed by the multiplication by `−1`) and the Table 4.1
sign constraint on each dual variable `pᵢ`. The feasible set is literally
the Table 4.1 dual feasible set (the conversion only rescales constraints
by `−1`), and the dual's own value as a maximization problem is
`lpDualValue P.b (generalFeasibleSet (dualLP P))`. -/
def dualLP {m n : ℕ} (P : GeneralFormLP m n) : GeneralFormLP n m where
  A := -P.Aᵀ
  b := -P.c
  c := -P.b
  rowRel := fun j => (P.colSign j).dualRel
  colSign := fun i => (P.rowRel i).dualSign

/-- The optimal value of the maximization problem `max p'b` over `S`,
valued in `EReal`: `⊥` iff `S = ∅` (infeasible), `⊤` iff the objective is
unbounded above — the maximization mirror of `lpValue`, encoding the
book's trichotomy for the dual (Bertsimas & Tsitsiklis, p. 67 and Table 4.2, p. 151). -/
noncomputable def lpDualValue {m : ℕ} (b : Fin m → ℝ) (S : Set (Fin m → ℝ)) :
    EReal :=
  ⨆ p ∈ S, ((p ⬝ᵥ b : ℝ) : EReal)

/-- `p` is an optimal solution of the maximization problem
`max p'b over S` (the dual orientation). -/
def IsLpDualOptimal {m : ℕ} (b : Fin m → ℝ) (S : Set (Fin m → ℝ))
    (p : Fin m → ℝ) : Prop :=
  p ∈ S ∧ ∀ q ∈ S, q ⬝ᵥ b ≤ p ⬝ᵥ b

/-- The standard-form problem `min c'x, Ax = b, x ≥ 0` as general-form
data (all rows `=`, all variables `≥ 0`) — the first p. 143 display. -/
def stdFormLP {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ)
    (c : Fin n → ℝ) : GeneralFormLP m n :=
  ⟨A, b, c, fun _ => .eq, fun _ => .nonneg⟩

/-- The inequality-form problem `min c'x, Ax ≥ b` as general-form data
(all rows `≥`, all variables free) — the second p. 143 display. -/
def geFormLP {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ)
    (c : Fin n → ℝ) : GeneralFormLP m n :=
  ⟨A, b, c, fun _ => .ge, fun _ => .free⟩

/-- The feasible set of the dual of the standard-form problem (Bertsimas & Tsitsiklis, p. 143):
`{p | p'A ≤ c'}`. -/
def dualFeasibleStd {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ)
    (c : Fin n → ℝ) : Set (Fin m → ℝ) :=
  {p | Aᵀ.mulVec p ≤ c}

/-- The feasible set of the dual of the inequality-form problem
(Bertsimas & Tsitsiklis, p. 143): `{p | p ≥ 0, p'A = c'}`. -/
def dualFeasibleGE {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ)
    (c : Fin n → ℝ) : Set (Fin m → ℝ) :=
  {p | 0 ≤ p ∧ Aᵀ.mulVec p = c}

/-- Sanity/bridge lemma: the general-form feasible set of `stdFormLP`
is the standard-form polyhedron. -/
theorem generalFeasibleSet_stdFormLP {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ)
    (b : Fin m → ℝ) (c : Fin n → ℝ) :
    generalFeasibleSet (stdFormLP A b c) = stdPolyhedron A b := by
  ext x
  simp [generalFeasibleSet, stdFormLP, LinearConstraint.IsSatisfiedAt,
    VarSign.IsSatisfiedBy, stdPolyhedron, funext_iff, Pi.le_def,
    Matrix.mulVec, dotProduct]

/-- Sanity/bridge lemma: the general-form feasible set of `geFormLP` is
the general-form polyhedron `{x | Ax ≥ b}`. -/
theorem generalFeasibleSet_geFormLP {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ)
    (b : Fin m → ℝ) (c : Fin n → ℝ) :
    generalFeasibleSet (geFormLP A b c) = polyhedron A b := by
  ext x
  simp [generalFeasibleSet, geFormLP, LinearConstraint.IsSatisfiedAt,
    VarSign.IsSatisfiedBy, polyhedron, Pi.le_def, Matrix.mulVec, dotProduct]

/-- **Bertsimas & Tsitsiklis, p. 143 (first display).** The dual of the standard-form problem
`min c'x, Ax = b, x ≥ 0` is `max p'b` subject to `p'A ≤ c'`: the feasible
set of `dualLP (stdFormLP A b c)` is `dualFeasibleStd A c`. -/
theorem dualFeasibleSet_stdFormLP {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ)
    (b : Fin m → ℝ) (c : Fin n → ℝ) :
    generalFeasibleSet (dualLP (stdFormLP A b c)) = dualFeasibleStd A c := by
  ext p
  have hkey : ∀ j : Fin n, (-Aᵀ) j ⬝ᵥ p = -(Aᵀ.mulVec p j) :=
    fun j => congrFun (Matrix.neg_mulVec p Aᵀ) j
  constructor
  · rintro ⟨hrow, -⟩
    show Aᵀ.mulVec p ≤ c
    rw [Pi.le_def]
    intro j
    have h : (-c) j ≤ (-Aᵀ) j ⬝ᵥ p := hrow j
    rw [hkey j] at h
    simpa using h
  · intro h
    refine ⟨fun j => ?_, fun i => trivial⟩
    show (-c) j ≤ (-Aᵀ) j ⬝ᵥ p
    rw [hkey j]
    simpa using Pi.le_def.mp h j

/-- **Bertsimas & Tsitsiklis, p. 143 (second display).** The dual of the inequality-form
problem `min c'x, Ax ≥ b` is `max p'b` subject to `p'A = c', p ≥ 0`: the
feasible set of `dualLP (geFormLP A b c)` is `dualFeasibleGE A c`. -/
theorem dualFeasibleSet_geFormLP {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ)
    (b : Fin m → ℝ) (c : Fin n → ℝ) :
    generalFeasibleSet (dualLP (geFormLP A b c)) = dualFeasibleGE A c := by
  ext p
  have hkey : ∀ j : Fin n, (-Aᵀ) j ⬝ᵥ p = -(Aᵀ.mulVec p j) :=
    fun j => congrFun (Matrix.neg_mulVec p Aᵀ) j
  constructor
  · rintro ⟨hrow, hsign⟩
    refine ⟨fun i => hsign i, funext fun j => ?_⟩
    have h : (-Aᵀ) j ⬝ᵥ p = (-c) j := hrow j
    rw [hkey j] at h
    simpa using h
  · rintro ⟨hsign, hrow⟩
    refine ⟨fun j => ?_, fun i => hsign i⟩
    show (-Aᵀ) j ⬝ᵥ p = (-c) j
    rw [hkey j]
    simpa using congrFun hrow j

end LinearOptimization


