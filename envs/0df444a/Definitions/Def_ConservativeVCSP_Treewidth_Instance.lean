-- Prove2me | Definitions.Def_ConservativeVCSP_Treewidth_Instance
-- name    : ConservativeVCSP_Treewidth_Instance
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-10T21:45:23.759061+00:00
-- url     : https://prove2.me/theorems/16fe4276-e670-4537-a020-7ec0702b539b
-- title:
--   Cost functions, hard lists, finite-valued hard-list languages, VCSP instances, Opt, primal graph and available sets
-- statement:
--   A **cost function** of arity $a\ge 0$ over a finite nonempty domain $D$ is a map $f: D^a\to\mathbb Q_{\ge0}\cup\{\infty\}$; it is **finite-valued** if it never takes the value $\infty$. A **constraint language** is a finite set $\Gamma$ of cost functions. The **hard list** on $D'\subseteq D$ is the unary function equal to $0$ on $D'$ and $\infty$ outside ($D'=\emptyset$ allowed); $H_D$ is the set of all hard lists. $\Gamma$ is a **finite-valued hard-list language** if $\Gamma=\Phi\cup H_D$ for a finite set $\Phi$ of finite-valued cost functions of arbitrary arities.
--
--   An instance $I=(V,\mathcal C,t)$ of $\mathrm{VCSP}(\Gamma)$ has variables $V$, a family of constraints $C=(f,S,w)$ with $f\in\Gamma$, scope $S\in V^{\mathrm{arity}(f)}$ (repetitions allowed) and weight $w\in\mathbb Q_{>0}$, and a target $t\in\mathbb Q$. For $\pi:V\to D$,
--   $$\mathrm{cost}_I(\pi)=\sum_{C\in\mathcal C}\mathrm{weight}(C)\,f_C(\pi(\mathrm{scope}(C))),\qquad \mathrm{Opt}(I)=\min_{\pi}\mathrm{cost}_I(\pi),$$
--   with $w\cdot\infty=\infty$ and $x+\infty=\infty$; the decision problem asks whether $\mathrm{Opt}(I)\le t$. The **primal graph** joins two distinct variables occurring together in a scope. The **available set** $L_v$ is the intersection of the sets allowed by the hard-list constraints on $v$ ($L_v=D$ if there are none).
--
--   **Formalization Note** Variables are `Fin n`, the constraint family is a list, values are `WithTop ℚ≥0`, and $\mathrm{Opt}$ is the infimum over the finite set of assignments. `Instance.Yes` holds iff $\mathrm{Opt}(I)$ is a finite rational $\le t$. `addConstraints` appends constraints (used for "add hard-list constraints").
-- source:
--   Greilhuber, Marx, Osipov, Piecyk, Rzążewski, Živný, Tight Algorithms for Conservative Finite-Valued CSPs Parameterized by Treewidth, STOC 2027 submission (manuscript sha256 e3f9968e…), p. 17, §3 Preliminaries and Definition 3.2; p. 30, Definitions 6.1–6.2

import Mathlib

set_option autoImplicit false

namespace ConservativeVCSP.Treewidth

/-- A cost function over the domain `D` (Greilhuber et al., §3, p. 17): a function
`f : D^a → ℚ≥0 ∪ {∞}` of arity `a ≥ 0` (nullary functions are allowed). The value `∞` is `⊤`. -/
structure CostFn (D : Type) where
  arity : ℕ
  f : (Fin arity → D) → WithTop ℚ≥0

/-- A cost function is finite-valued if it never takes the value `∞` (§3, p. 17). -/
def CostFn.FiniteValued {D : Type} (g : CostFn D) : Prop :=
  ∀ x, g.f x ≠ ⊤

/-- The unary cost function given by `u : D → ℚ≥0 ∪ {∞}`. -/
def unary {D : Type} (u : D → WithTop ℚ≥0) : CostFn D :=
  ⟨1, fun x => u (x 0)⟩

/-- The binary cost function given by `g : D → D → ℚ≥0 ∪ {∞}`. -/
def binary {D : Type} (g : D → D → WithTop ℚ≥0) : CostFn D :=
  ⟨2, fun x => g (x 0) (x 1)⟩

open scoped Classical in
/-- The hard list on `D' ⊆ D` (Definition 6.1, p. 30): the unary cost function with value `0` on
`D'` and `∞` outside `D'`. `D' = ∅` is allowed (value `∞` everywhere). -/
noncomputable def hardList {D : Type} (D' : Set D) : CostFn D :=
  unary fun d => if d ∈ D' then 0 else ⊤

/-- `H_D`, the set of all hard lists on `D` (Definition 6.2, p. 30). -/
def hardLists (D : Type) : Set (CostFn D) :=
  Set.range (hardList (D := D))

/-- A constraint language is a finite set of cost functions over `D` (§1, p. 2; §3, p. 17). -/
def IsLanguage {D : Type} (Γ : Set (CostFn D)) : Prop :=
  Γ.Finite

/-- A finite-valued hard-list language (Definition 6.2, p. 30): `Γ = Φ ∪ H_D` for a finite set
`Φ` of finite-valued cost functions (of arbitrary arities), `H_D` being all hard lists. -/
def IsFVHardListLanguage {D : Type} (Γ : Set (CostFn D)) : Prop :=
  ∃ Φ : Set (CostFn D), Φ.Finite ∧ (∀ g ∈ Φ, g.FiniteValued) ∧ Γ = Φ ∪ hardLists D

/-- A finite constraint language whose cost functions are finite-valued or hard lists
(the hypothesis of Lemma 2.8, p. 11). -/
def IsFVOrHardListLanguage {D : Type} (Γ : Set (CostFn D)) : Prop :=
  Γ.Finite ∧ ∀ g ∈ Γ, g.FiniteValued ∨ g ∈ hardLists D

/-- A constraint `(f, S, w)` on the variable set `V` (§3, p. 17): a cost function `f`, a scope
`S ∈ V^{arity f}` (repeated variables allowed) and a positive rational weight `w`. -/
structure Constraint (D V : Type) where
  fn : CostFn D
  scope : Fin fn.arity → V
  weight : ℚ≥0
  weight_pos : 0 < weight

/-- Cost of a weighted constraint system at the assignment `σ`:
`Σ_C weight(C) · f_C(σ(scope C))`, with `w · ∞ = ∞` (`w > 0`) and `x + ∞ = ∞`. -/
def sysCost {D V : Type} (cs : List (Constraint D V)) (σ : V → D) : WithTop ℚ≥0 :=
  (cs.map fun C => (C.weight : WithTop ℚ≥0) * C.fn.f (σ ∘ C.scope)).sum

/-- A VCSP instance `I = (V, C, t)` (§3, p. 17): the variables are `Fin n`, the constraint family
is a list (repetitions allowed) and `t ∈ ℚ` is the cost target. -/
structure Instance (D : Type) where
  n : ℕ
  constraints : List (Constraint D (Fin n))
  target : ℚ

/-- `I` is an instance of `VCSP(Γ)`: every constraint uses a cost function of `Γ`. -/
def Instance.IsOver {D : Type} (I : Instance D) (Γ : Set (CostFn D)) : Prop :=
  ∀ C ∈ I.constraints, C.fn ∈ Γ

/-- `cost_I(π)`. -/
def Instance.cost {D : Type} (I : Instance D) (π : Fin I.n → D) : WithTop ℚ≥0 :=
  sysCost I.constraints π

/-- `Opt(I) = min_π cost_I(π)`, equal to `∞` when no finite-cost assignment exists. -/
noncomputable def Instance.opt {D : Type} [Fintype D] (I : Instance D) : WithTop ℚ≥0 :=
  Finset.univ.inf I.cost

/-- The decision problem `VCSP(Γ)`: is `Opt(I) ≤ t`? (A negative target is a no-instance.) -/
def Instance.Yes {D : Type} [Fintype D] (I : Instance D) : Prop :=
  ∃ q : ℚ≥0, I.opt = (q : WithTop ℚ≥0) ∧ (q : ℚ) ≤ I.target

/-- The primal graph (§3, p. 17): distinct variables are adjacent iff they occur together in the
scope of some constraint. -/
def Instance.primalGraph {D : Type} (I : Instance D) : SimpleGraph (Fin I.n) :=
  SimpleGraph.fromRel fun u v =>
    ∃ C ∈ I.constraints, (∃ i, C.scope i = u) ∧ ∃ j, C.scope j = v

/-- The available set `L_v` (Definition 3.2, p. 17): the intersection of the sets allowed by the
hard-list constraints imposed on `v` (`L_v = D` when there are none). -/
def Instance.avail {D : Type} (I : Instance D) (v : Fin I.n) : Set D :=
  {d | ∀ C ∈ I.constraints, C.fn ∈ hardLists D → ∀ i, C.scope i = v →
      C.fn.f (fun _ => d) ≠ ⊤}

/-- The instance obtained from `I` by adding the constraints `extra` (same variables and target). -/
def Instance.addConstraints {D : Type} (I : Instance D) (extra : List (Constraint D (Fin I.n))) :
    Instance D :=
  ⟨I.n, I.constraints ++ extra, I.target⟩

end ConservativeVCSP.Treewidth


