-- Prove2me | Definitions.Def_RobustBoolPCSP_Signed
-- name    : RobustBoolPCSP_Signed
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T12:22:38.373164+00:00
-- url     : https://prove2.me/theorems/ff55f54e-8282-4a53-9016-e5d82b911c18
-- title:
--   Literals, signed instances of Boolean templates, symmetric templates and polymorphisms
-- statement:
--   A **literal** over variables $x_0,\dots,x_{n-1}$ is a variable $x_v$, its negation $1-x_v$, or one of the constants $0$ and $1$. A **signed instance** of a Boolean template $\Gamma=\{(P_j,Q_j)\}$ has variables $V=\{0,\dots,n-1\}$ and a multiset of constraints, each applying a relation pair $(P_j,Q_j)$ to a tuple of $r_j$ literals; a variable may occur several times in a scope, with either sign. Strong error, weak error and $\alpha(I)$ are defined as for ordinary instances, evaluating each literal under the assignment $b:V\to\{0,1\}$; $b$ **weakly satisfies** $I$ when every constraint's literal tuple lies in its $Q_j$. A signed instance has **no constants** when every literal is a variable or a negated variable.
--
--   A Boolean template is **symmetric** when each $P_j$ and $Q_j$ is closed under permutations of coordinates, equivalently when membership depends only on the Hamming weight. An operation $f:\{0,1\}^L\to\{0,1\}$ is a **polymorphism** of $\Gamma$ (it **preserves** every relation pair) when, for every $j$, applying $f$ coordinatewise to any $L$ tuples of $P_j$ gives a tuple of $Q_j$.
--
--   The robust satisfiability problem $\mathrm{fiPCSP}(\Gamma)$ is posed on these signed instances.
--
--   **Formalization Note** $\{0,1\}$ is `Bool` with `true` $=1$. Symmetry and preservation reuse the published `SymBoolPCSP.CFixing.IsSymmetricRel` and `PolOf`; literal substitution and negation are provided for the replacement lemma.
-- source:
--   Cai, Jiang, Zou, On Robust Promise CSPs: A Boolean Dichotomy, Sharp Quantitative Bounds, and Soft-Equality Transfer, STOC 2027 submission (manuscript of 2026-11-03, sha256 fd1be0d0624155f00f7a115874a4dadfb7ebb2d4187530c7d0bdd4e1406e8732), §3.2, p.15 (literals, signed instances, symmetric templates); §3.1, p.15 (polymorphisms)

import Mathlib
import Definitions.Def_RobustBoolPCSP_Template
import Definitions.Def_SymBoolPCSP_CFixing_Basic

set_option autoImplicit false

namespace RobustBoolPCSP

/-- A **literal** over the variables `Fin n` (§3.2, p.15): "A literal is a variable xv, its negation
1 − xv, or one of the constants 0 and 1." -/
inductive Literal (n : ℕ) where
  /-- The variable `x_v`. -/
  | pos (v : Fin n)
  /-- The negated variable `1 − x_v`. -/
  | neg (v : Fin n)
  /-- The constant `0`. -/
  | zero
  /-- The constant `1`. -/
  | one
  deriving DecidableEq

/-- The value of a literal under a Boolean assignment `b : Fin n → Bool` (`true` = 1). -/
def Literal.eval {n : ℕ} (b : Fin n → Bool) : Literal n → Bool
  | pos v => b v
  | neg v => !b v
  | zero => false
  | one => true

/-- The negation of a literal: `x ↔ ¬x`, `0 ↔ 1`. -/
def Literal.negate {n : ℕ} : Literal n → Literal n
  | pos v => neg v
  | neg v => pos v
  | zero => one
  | one => zero

/-- Substitution of literals: a literal over `y_1, …, y_ℓ` (`Fin ℓ`) with each `y_i` replaced by the
literal `σ i` over `Fin n`. -/
def Literal.subst {ℓ n : ℕ} (σ : Fin ℓ → Literal n) : Literal ℓ → Literal n
  | pos i => σ i
  | neg i => (σ i).negate
  | zero => zero
  | one => one

/-- A literal is a variable or a negated variable (not a constant). -/
def Literal.IsVarLit {n : ℕ} : Literal n → Prop
  | pos _ => True
  | neg _ => True
  | zero => False
  | one => False

/-- A **signed instance** of a Boolean template `Γ` (§3.2, p.15): variables `Fin n` and a multiset
(`List`) of constraints, each applying a relation pair `(P_j, Q_j)` of `Γ` to a tuple of literals.
"A signed instance of a Boolean template Γ consists of constraints that apply a relation pair
(Pj, Qj) of Γ to a tuple of literals; a variable may occur several times in a scope, with either
sign." Each constraint occurrence has weight one (unweighted). -/
structure SignedInstance {ι : Type} (Γ : Template ι Bool Bool) where
  /-- The number of variables. -/
  n : ℕ
  /-- The constraints, with multiplicity. -/
  cons : List (Σ j : ι, Fin (Γ.r j) → Literal n)

/-- The value of a literal tuple under an assignment. -/
def evalLits {n k : ℕ} (b : Fin n → Bool) (t : Fin k → Literal n) : Fin k → Bool :=
  fun i => (t i).eval b

/-- Strong error of a signed instance (§3.2, p.15, "evaluating each literal under the
assignment"), `0` when there are no constraints. -/
noncomputable def SignedInstance.errStr {ι : Type} {Γ : Template ι Bool Bool}
    (I : SignedInstance Γ) (s : Fin I.n → Bool) : ℝ :=
  fracOf I.cons (fun c => evalLits s c.2 ∉ Γ.P c.1)

/-- Weak error of a signed instance (§3.2, p.15), `0` when there are no constraints. -/
noncomputable def SignedInstance.errWk {ι : Type} {Γ : Template ι Bool Bool}
    (I : SignedInstance Γ) (b : Fin I.n → Bool) : ℝ :=
  fracOf I.cons (fun c => evalLits b c.2 ∉ Γ.Q c.1)

/-- `α(I) = min_s err_str(s; I)` for a signed instance, a minimum over the finite nonempty set
`Fin n → Bool`. -/
noncomputable def SignedInstance.alpha {ι : Type} {Γ : Template ι Bool Bool}
    (I : SignedInstance Γ) : ℝ :=
  Finset.univ.inf' Finset.univ_nonempty (fun s : Fin I.n → Bool => I.errStr s)

/-- `b` satisfies every weak constraint of the signed instance. -/
def SignedInstance.WeakSat {ι : Type} {Γ : Template ι Bool Bool} (I : SignedInstance Γ)
    (b : Fin I.n → Bool) : Prop :=
  ∀ c ∈ I.cons, evalLits b c.2 ∈ Γ.Q c.1

/-- Every literal of every constraint is a variable or a negated variable: the signed model of
[BGS25] with negations but without constants. -/
def SignedInstance.NoConstants {ι : Type} {Γ : Template ι Bool Bool} (I : SignedInstance Γ) :
    Prop :=
  ∀ c ∈ I.cons, ∀ i, (c.2 i).IsVarLit

/-- `Γ` is a **symmetric** Boolean template (§2.1 p.7, §3.2 p.15): every relation `P_j`, `Q_j` is
symmetric, i.e. closed under permutations of coordinates (published `SymBoolPCSP.CFixing.
IsSymmetricRel`); for Boolean relations this is "membership depends only on the Hamming weight". -/
def IsSymmetricTemplate {ι : Type} (Γ : Template ι Bool Bool) : Prop :=
  ∀ j, SymBoolPCSP.CFixing.IsSymmetricRel (Γ.P j) ∧ SymBoolPCSP.CFixing.IsSymmetricRel (Γ.Q j)

/-- `P_j ⊆ Q_j` for every pair. -/
def IsPromiseTemplate {ι A : Type} (Γ : Template ι A A) : Prop :=
  ∀ j, Γ.P j ⊆ Γ.Q j

/-- `f : {0,1}^L → {0,1}` is a **polymorphism** of the Boolean template `Γ` (§3.1, p.15): for every
`j`, applying `f` coordinatewise to any `L` tuples of `P_j` gives a tuple of `Q_j` (published
`SymBoolPCSP.CFixing.PolOf` for each pair). "`f` preserves every relation pair of `Γ`". -/
def IsPolB {ι : Type} (Γ : Template ι Bool Bool) {L : ℕ} (f : (Fin L → Bool) → Bool) : Prop :=
  ∀ j, SymBoolPCSP.CFixing.PolOf (Γ.P j) (Γ.Q j) f

end RobustBoolPCSP


