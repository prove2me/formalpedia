-- Prove2me | Definitions.Def_OAI_Combinatorics_ParityLifts_WeightedDual
-- name    : OAI_Combinatorics_ParityLifts_WeightedDual
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-15T04:04:32.202881+00:00
-- url     : https://prove2.me/theorems/b000cfdf-37fa-4b77-af38-387b4d0b8307
-- title:
--   Weighted dual witnesses for the parity-lift equations
-- statement:
--   This file introduces the dual objects that certify unsolvability of the lift equations over $\mathbb{F}_2$.
--
--   Let $T$, $G$, $F$ be graphs on finite vertex sets $A$, $V$, $W$, with homomorphisms $\tau\colon G\to T$ and $\varphi\colon F\to G$. The lift equations of $\varphi$ have rows indexed by $W\sqcup\vec E(F)$ (vertices and darts of $F$) and unknowns $z_{x,u}$ indexed by $x\in W$ and $u\in N_T(\tau(\varphi(x)))$.
--
--   1. **Weights of a functional.** For a linear functional $f\colon\mathbb{F}_2^{W\sqcup\vec E(F)}\to\mathbb{F}_2$, with $e_\bullet$ the standard basis vector of a row, put
--   $$
--   s_f(x)=f(e_x),\qquad \rho_f(x,y)=f(e_{(x,y)}),\qquad r_f(x,y)=\begin{cases}\rho_f(x,y)+\rho_f(y,x)&\text{if } xy\in E(F),\\ 0&\text{otherwise.}\end{cases}
--   $$
--   The edge weight $r_f$ is symmetric and vanishes off the edges of $F$.
--   2. **Unit families.** For $x\in W$ and $u\in N_T(\tau(\varphi(x)))$, $\delta_{x,u}$ is the family of unknowns equal to $1$ at $(x,u)$ and to $0$ elsewhere.
--   3. **Weighted witnesses.** Let $a\colon F\to T$ be a graph homomorphism and $b\colon A\to\mathbb{F}_2$. A weighted witness for $(a,b)$ is a pair of functions $s\colon W\to\mathbb{F}_2$ (vertex weights) and $r\colon W\times W\to\mathbb{F}_2$ (edge weights) such that $r(x,y)=r(y,x)$ for all $x,y\in W$, $r(x,y)=0$ whenever $x$ and $y$ are not adjacent in $F$, and
--   $$
--   \sum_{\substack{y\in W\\ a(y)=u}}r(x,y)=s(x)\quad\text{for all } x\in W \text{ and } u\in N_T(a(x)),\qquad\qquad \sum_{x\in W}s(x)\,b(a(x))=1 .
--   $$
--
--   For $a=\tau\circ\varphi$, adding up the vertex equations with coefficients $s(x)$ and the edge equations with coefficients $r(x,y)$ produces the coefficient $s(x)+\sum_{y:\,a(y)=u}r(x,y)$ at the unknown $z_{x,u}$ and the right-hand side $\sum_x s(x)\,b(a(x))$; a weighted witness is therefore a combination of the lift equations that reads $0=1$. Results built on these definitions show that the lift equations for $\varphi$ and $b$ are unsolvable exactly when a weighted witness for $(\tau\circ\varphi,b)$ exists, and the separator argument of the parity-lift reduction works entirely with such witnesses.
--
--   **Formalization Note** Functionals are `Bit`-linear maps from the row space `EquationRow F` to `Bit`. Items 1 and 2 are `dualVertex`, `dualDart`, `dualEdge` and `variableUnit`; item 3 is the structure `WeightedWitness T F a b` with fields `vertex`, `edge`, `symmetric`, `supported`, `coordinate`, `odd`. The bijections `dartNeighborsEquiv` (darts as vertex-neighbour pairs) and `dartReverseEquiv` (dart reversal) are reindexing plumbing.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/ParityLifts/WeightedDual.lean

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/ParityLifts/WeightedDual.lean by skeleton subtraction
-- (upload_full_project.md Phase 3): Definitions bundle for the ParityLifts mission closure.
-- Kept: reachable definitions/instances and the theorems their bodies or the node statements cite.
-- Project imports rewritten to platform modules; otherwise byte-identical to the source.
import Mathlib
import Definitions.Def_ParityLifts
import Definitions.Def_OAI_Combinatorics_ParityLifts_LiftCounts

-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

namespace ParityWL

open scoped BigOperators

section WeightedDual

open scoped Classical

variable {A V W : Type} [Fintype A] [Fintype V] [Fintype W]
variable (T : SimpleGraph A) (G : SimpleGraph V) (F : SimpleGraph W)
variable (τ : G →g T) (φ : F →g G)

def dartNeighborsEquiv : F.Dart ≃ ((x : W) × F.neighborSet x) where
  toFun d := ⟨d.fst, ⟨d.snd, d.adj⟩⟩
  invFun d := ⟨(d.1, d.2.1), d.2.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

def dartReverseEquiv : F.Dart ≃ F.Dart :=
  SimpleGraph.Dart.symm_involutive.toPerm

noncomputable def dualVertex (f : (EquationRow F → Bit) →ₗ[Bit] Bit) (x : W) : Bit :=
  f (Pi.single (.inl x) 1)

noncomputable def dualDart (f : (EquationRow F → Bit) →ₗ[Bit] Bit) (d : F.Dart) : Bit :=
  f (Pi.single (.inr d) 1)

noncomputable def dualEdge (f : (EquationRow F → Bit) →ₗ[Bit] Bit) (x y : W) : Bit :=
  if h : F.Adj x y then
    dualDart F f ⟨(x, y), h⟩ + dualDart F f ⟨(y, x), h.symm⟩ else 0

noncomputable def variableUnit (x : W) (u : T.neighborSet (τ (φ x))) :
    Variables T G F τ φ :=
  fun y v => if y = x ∧ v.1 = u.1 then 1 else 0

/-- The supported, symmetric dual certificate of the *actual* parity-lift system. -/
structure WeightedWitness (a : F →g T) (b : A → Bit) where
  vertex : W → Bit
  edge : W → W → Bit
  symmetric : ∀ x y, edge x y = edge y x
  supported : ∀ x y, ¬ F.Adj x y → edge x y = 0
  coordinate : ∀ x (u : T.neighborSet (a x)),
    (∑ y, if a y = u.1 then edge x y else 0) = vertex x
  odd : (∑ x, vertex x * b (a x)) = 1

end WeightedDual

end ParityWL

end OAI


