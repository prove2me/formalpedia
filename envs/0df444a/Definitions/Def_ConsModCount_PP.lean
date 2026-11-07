-- Prove2me | Definitions.Def_ConsModCount_PP
-- name    : ConsModCount_PP
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T07:27:09.04085+00:00
-- url     : https://prove2.me/theorems/b9bc8ccf-2c62-4e11-a642-19f0985cb388
-- title:
--   Primitive positive definability, gadgets and extension counts
-- statement:
--   A **primitive positive (pp) formula** over $H$ with free variables $x_1,\dots,x_k$ is an expression $\exists y_1\cdots\exists y_m\,\Phi$, where $\Phi$ is a finite conjunction of atoms $R_i(u_1,\dots,u_{k_i})$ and equalities $u=u'$ over the variables $x,y$. A relation $R\subseteq D^k$ is **pp-definable**, $R\in\mathrm{pp}(H)$, if $R=\{a\in D^k:\exists b\in D^m\ \Phi(a,b)\}$ for such a formula. The quantifier is ordinary existential quantification over $D$, not a modular counting quantifier.
--
--   An **unweighted $H$-gadget** with $k$ ports is an $H$-instance together with $k$ exposed variables (ports, which may coincide). Its **extension count** at $a\in D^k$ is the number of satisfying assignments of the whole instance whose values on the ports are $a$. A gadget is an **exact unique-witness gadget** for $R\subseteq D^k$ if its extension count is the indicator of $R$:
--
--   $$\mathrm{ext}(a)=\begin{cases}1,&a\in R,\\0,&a\notin R.\end{cases}$$
--
--   Gadgets are the reductions of the hardness half of the classification.
-- source:
--   Xie, Conservative Modular Counting at Every Odd Prime, STOC 2027 submission (manuscript sha256 c673b4cc58550963462480168a22eca7184c16aebf1faa02497d68c5a46d876a), §1, p.1 (PDF p.2) and §10, p.12 (PDF p.13): pp(H); §10, p.14 (PDF p.15): gadgets, exact unique witnesses; §12, p.21 (PDF p.22)

import Mathlib
import Definitions.Def_ConsModCount_Template

set_option autoImplicit false

namespace ConsModCount

/-- A **primitive positive formula** over `H` with `k` free variables: `m` existentially quantified
variables, a finite list of `H`-atoms and a finite list of equalities, all over the `k + m`
variables (free variables first). Xie, p.1 (PDF p.2) and p.12 (PDF p.13): "ordinary primitive
positive definability using conjunction, existential quantification, template relations, and
equality". -/
structure PPFormula {D : Type} (H : Template D) (k : ℕ) where
  /-- The number of existentially quantified variables. -/
  m : ℕ
  /-- The `H`-atoms `R_i(u₁, …, u_r)` (variables may repeat). -/
  atoms : List (Σ i : Fin H.s, Fin (H.arity i) → Fin (k + m))
  /-- The equality atoms `u = u'`. -/
  eqs : List (Fin (k + m) × Fin (k + m))

/-- A tuple `a ∈ D^k` satisfies the pp formula: some assignment `b ∈ D^m` of the quantified
variables (ordinary existential quantification over `D`) makes every atom and every equality
true. -/
def PPFormula.Holds {D : Type} {H : Template D} {k : ℕ} (φ : PPFormula H k) (a : Fin k → D) :
    Prop :=
  ∃ b : Fin φ.m → D,
    (∀ c ∈ φ.atoms, Fin.append a b ∘ c.2 ∈ H.rel c.1) ∧
    ∀ e ∈ φ.eqs, Fin.append a b e.1 = Fin.append a b e.2

/-- `R ∈ pp(H)`: `R ⊆ D^k` is defined by some pp formula over `H`. The quantifier is ordinary
existential quantification, not a modular counting quantifier (Xie, p.12, PDF p.13). -/
def PPDefinable {D : Type} (H : Template D) {k : ℕ} (R : Set (Fin k → D)) : Prop :=
  ∃ φ : PPFormula H k, ∀ a : Fin k → D, a ∈ R ↔ φ.Holds a

/-- An **unweighted `H`-gadget** with `k` exposed ports: an `H`-instance together with the
variables exposed as ports. Xie, §10, p.14 (PDF p.15) and §12, p.21 (PDF p.22).

**Formalization Note.** The port map need not be injective: ports may be identified. -/
structure Gadget {D : Type} (H : Template D) (k : ℕ) where
  /-- The underlying unweighted instance. -/
  inst : Instance H
  /-- The exposed ports. -/
  port : Fin k → Fin inst.n

/-- The **extension count** of a gadget at a port tuple `a ∈ D^k`: the number of satisfying
assignments of the whole gadget whose values on the ports are `a`, i.e. the number of satisfying
assignments to all auxiliary variables extending `a`. -/
noncomputable def Gadget.extCount {D : Type} {H : Template D} {k : ℕ} (G : Gadget H k)
    (a : Fin k → D) : ℕ :=
  Nat.card {σ : Fin G.inst.n → D // G.inst.Sat σ ∧ σ ∘ G.port = a}

/-- An **exact unique-witness gadget** for `R ⊆ D^k`: every tuple of `R` has exactly one
satisfying assignment to all auxiliary variables and every tuple outside `R` has none, i.e. the
extension count is the `0`–`1` indicator of `R`. Xie, p.14 (PDF p.15). -/
def IsExactGadget {D : Type} {H : Template D} {k : ℕ} (G : Gadget H k) (R : Set (Fin k → D)) :
    Prop := by
  classical
  exact ∀ a : Fin k → D, G.extCount a = if a ∈ R then 1 else 0

end ConsModCount


