-- Prove2me | Definitions.Def_ConservativeVCSP_Treewidth_LocalNecessity
-- name    : ConservativeVCSP_Treewidth_LocalNecessity
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-10T21:46:04.233971+00:00
-- url     : https://prove2.me/theorems/84289a96-96af-4cc0-be48-a499d4059975
-- title:
--   Linear program 6.16 and locally fractionally necessary elements
-- statement:
--   Fix an instance $I$ with available sets $L_u$, a variable $v$ with primal-graph neighbours $N_v$, the family $\mathcal C_v$ of finite-valued constraints whose scope contains $v$, and $a\in L_v$. For $C\in\mathcal C_v$ let $g_C(d,\bar y)$ be its cost with $v$ set to $d$ and its other distinct variables $u_{C,1},\dots,u_{C,k_C}$ set to $\bar y\in Y_C=L_{u_{C,1}}\times\cdots\times L_{u_{C,k_C}}$. Linear program 6.16 has variables $q_{u,d}\in[0,1]$, $p_{C,\bar y}\in[0,1]$ and $\varepsilon$, maximizes $\varepsilon$, and requires (4) $\sum_{d\in L_u}q_{u,d}=1$ for $u\in N_v$; (5) $\sum_{\bar y}p_{C,\bar y}=1$; (6) $\sum_{\bar y:\,y_j=d}p_{C,\bar y}=q_{u_{C,j},d}$; (7) for every $b\in L_v\setminus\{a\}$,
--   $$\varepsilon\le d_a(b,p)=\sum_{C\in\mathcal C_v}\mathrm{weight}(C)\sum_{\bar y\in Y_C}p_{C,\bar y}\big(g_C(b,\bar y)-g_C(a,\bar y)\big);$$
--   (8) $\varepsilon\le1$. The element $a$ is **locally fractionally necessary** at $v$ if the optimum is positive.
--
--   **Formalization Note** Constraints are indexed by their position; $Y_C$ is the set of available maps from the other variables of the scope to $D$. Values of `q`, `p` outside the LP's index sets are unconstrained and appear nowhere. "Optimum positive" is stated as the existence of a feasible point with $\varepsilon>0$, equivalent because the feasible region is a nonempty polytope when all $L_u$ are nonempty. `gVal` reads a finite cost as a rational; it is used only on finite-valued constraints.
-- source:
--   Greilhuber, Marx, Osipov, Piecyk, Rzążewski, Živný, Tight Algorithms for Conservative Finite-Valued CSPs Parameterized by Treewidth, STOC 2027 submission (manuscript sha256 e3f9968e…), pp. 37–39, Definition 6.14, Mixed integer linear program 6.15, Linear program 6.16, Definition 6.17

import Definitions.Def_ConservativeVCSP_Treewidth_Instance

set_option autoImplicit false

namespace ConservativeVCSP.Treewidth

variable {D : Type} [Fintype D]

/-- The `c`-th constraint of `I` (constraints are indexed by their position in the family). -/
def Instance.con (I : Instance D) (c : Fin I.constraints.length) : Constraint D (Fin I.n) :=
  I.constraints.get c

open scoped Classical in
/-- `C_v` (Definition 6.14, p. 37; Linear program 6.16, p. 39): the finite-valued constraints whose
scope contains `v`. -/
noncomputable def Instance.Cv (I : Instance D) (v : Fin I.n) : Finset (Fin I.constraints.length) :=
  Finset.univ.filter fun c => (I.con c).fn.FiniteValued ∧ ∃ i, (I.con c).scope i = v

/-- The distinct variables other than `v` in the scope of the `c`-th constraint (the variables
`u_{C,1}, …, u_{C,k_C}` of Mixed integer linear program 6.15, p. 38, as a set). -/
def Instance.others (I : Instance D) (c : Fin I.constraints.length) (v : Fin I.n) :
    Finset (Fin I.n) :=
  Finset.univ.filter fun u => u ≠ v ∧ ∃ i, (I.con c).scope i = u

open scoped Classical in
/-- `N_v`, the neighbours of `v` in the primal graph. -/
noncomputable def Instance.nbrs (I : Instance D) (v : Fin I.n) : Finset (Fin I.n) :=
  Finset.univ.filter fun u => I.primalGraph.Adj v u

open scoped Classical in
/-- `L_u` as a finite set. -/
noncomputable def Instance.availF (I : Instance D) (u : Fin I.n) : Finset D :=
  Finset.univ.filter fun d => d ∈ I.avail u

open scoped Classical in
/-- `Y_C`: the available tuples `ȳ` for the other variables of the `c`-th constraint
(`ȳ(u) ∈ L_u`); with no other variables it consists of the empty tuple. -/
noncomputable def Instance.Y (I : Instance D) (c : Fin I.constraints.length) (v : Fin I.n) :
    Finset (I.others c v → D) :=
  Finset.univ.filter fun y => ∀ u, y u ∈ I.avail u.1

/-- The argument tuple of the `c`-th constraint when `v` takes the value `b` and the other
variables take the values `ȳ` (repeated variables identified, `v` placed first: `g_C(b, ȳ)`). -/
def Instance.gArg (I : Instance D) (c : Fin I.constraints.length) (v : Fin I.n) (b : D)
    (y : I.others c v → D) : Fin (I.con c).fn.arity → D :=
  fun i => if h : (I.con c).scope i = v then b else
    y ⟨(I.con c).scope i, Finset.mem_filter.mpr ⟨Finset.mem_univ _, h, i, rfl⟩⟩

/-- `g_C(b, ȳ)` as a rational number. It is only used for `C ∈ C_v`, whose cost function is
finite-valued, so the default value `0` for `∞` is never taken there. -/
noncomputable def Instance.gVal (I : Instance D) (c : Fin I.constraints.length) (v : Fin I.n)
    (b : D) (y : I.others c v → D) : ℚ :=
  ((WithTop.untopD (0 : ℚ≥0) ((I.con c).fn.f (I.gArg c v b y)) : ℚ≥0) : ℚ)

/-- The cost difference `d_a(b, p) = Σ_{C ∈ C_v} weight(C) Σ_{ȳ ∈ Y_C} p_{C,ȳ} (g_C(b,ȳ) − g_C(a,ȳ))`
(Mixed integer linear program 6.15, p. 38). -/
noncomputable def Instance.costDiff (I : Instance D) (v : Fin I.n) (a b : D)
    (p : (c : Fin I.constraints.length) → (I.others c v → D) → ℚ) : ℚ :=
  ∑ c ∈ I.Cv v, ((I.con c).weight : ℚ) *
    ∑ y ∈ I.Y c v, p c y * (I.gVal c v b y - I.gVal c v a y)

open scoped Classical in
/-- `(q, p, ε)` is a feasible solution of Linear program 6.16 (p. 39) for `I`, `v`, `a`:
constraints (4)–(8) of Mixed integer linear program 6.15 (p. 38) with (9)–(10) relaxed to
`0 ≤ q_{u,d} ≤ 1` and `0 ≤ p_{C,ȳ} ≤ 1`. The variables `q_{u,d}` (`u ∈ N_v`, `d ∈ L_u`) and
`p_{C,ȳ}` (`C ∈ C_v`, `ȳ ∈ Y_C`) are the values of `q` and `p` at those indices; values at other
indices are not LP variables and are unconstrained. -/
def Instance.LPFeasible (I : Instance D) (v : Fin I.n) (a : D) (q : Fin I.n → D → ℚ)
    (p : (c : Fin I.constraints.length) → (I.others c v → D) → ℚ) (ε : ℚ) : Prop :=
  -- (4)
  (∀ u ∈ I.nbrs v, ∑ d ∈ I.availF u, q u d = 1) ∧
  -- (5)
  (∀ c ∈ I.Cv v, ∑ y ∈ I.Y c v, p c y = 1) ∧
  -- (6)
  (∀ c ∈ I.Cv v, ∀ u : I.others c v, ∀ d ∈ I.availF u.1,
      ∑ y ∈ (I.Y c v).filter (fun y => y u = d), p c y = q u.1 d) ∧
  -- (7)
  (∀ b ∈ I.availF v, b ≠ a → ε ≤ I.costDiff v a b p) ∧
  -- (8)
  ε ≤ 1 ∧
  -- relaxed (9), (10)
  (∀ u ∈ I.nbrs v, ∀ d ∈ I.availF u, 0 ≤ q u d ∧ q u d ≤ 1) ∧
  (∀ c ∈ I.Cv v, ∀ y ∈ I.Y c v, 0 ≤ p c y ∧ p c y ≤ 1)

/-- `a` is locally fractionally necessary at `v` (Definition 6.17, p. 39): `a ∈ L_v` and the
optimum of Linear program 6.16 for `I`, `v`, `a` is positive, i.e. (the program maximizes `ε`
over a polytope) some feasible solution has `ε > 0`. -/
def Instance.LocFracNecessary (I : Instance D) (v : Fin I.n) (a : D) : Prop :=
  a ∈ I.avail v ∧ ∃ q p ε, I.LPFeasible v a q p ε ∧ 0 < ε

end ConservativeVCSP.Treewidth


