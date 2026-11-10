-- Prove2me | Definitions.Def_ObfEF_Incremental_Derivation
-- name    : ObfEF_Incremental_Derivation
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-10T04:56:50.25305+00:00
-- url     : https://prove2.me/theorems/39e63af2-ba41-445c-b087-875fe8bf390c
-- title:
--   Derivations of width three for two circuits (Definition 3.5)
-- statement:
--   Let $C_0,C_1$ be circuits over $B$ with $il$ inputs and $ol$ outputs, with $k$th outputs $u^0_k,u^1_k$. Each noninput vertex $v$ of $C_b$ has a variable $y^b_v$; at the input vertex $v_r$, $y^b_{v_r}=x_r$. The **definition** of a noninput vertex is $\mathrm{eq}(y^b_v,t)$ with $t$ its instruction over the variables of its in-neighbours; an extension axiom $z\leftrightarrow\varphi$ **defines** $z$ by $\varphi$.
--
--   A **step** is a line together with a set of earlier lines, its premises, such that every assignment satisfying the premises satisfies the line. To **unfold** a variable defined earlier, replace it by the variables of its defining expression ($t$ for $y^b_v$, $\varphi$ for $z$). One may choose at most three variables of a step, each defined by an earlier line, and unfold the chosen variables until only unchosen variables remain; the **width** of the step is the least number of remaining variables over these choices.
--
--   A **derivation of width three** for $C_0$ and $C_1$ (Definition 3.5) is a list of formulas such that
--
--   1. its first lines are the definitions of the variables of the noninput vertices of $C_0$ and $C_1$;
--   2. every later line is an extension axiom $z\leftrightarrow\varphi$ whose variable $z$ differs from the input variables and is absent from $\varphi$ and from the earlier lines, and whose formula $\varphi$ has at most two variables, or it forms a step of width at most $3$ with at most three premises;
--   3. for every $k\in[ol]$ the formula $\mathrm{eq}\big(y^0_{u^0_k},y^1_{u^1_k}\big)$ is a line;
--   4. every variable is an input variable, the variable of a vertex, or the variable of an extension axiom.
--
--   Derivations of width three are the intermediate object between an Extended Frege proof (Lemma 3.6) and a sequence of incremental changes of support three (Theorem 3.10).
--
--   **Formalization Note.** $x_r$ is `var r` and $y^b_j$ (noninput vertex $j$ of $C_b$) is `var (il + 2j + b)`. Condition 1: the first $|C_0|+|C_1|$ lines are a permutation of the vertex definitions. Unfolding is the set `remaining Ch dv V` of unchosen variables reachable from the step's variables through chains of chosen variables, `dv c` being the variable set of the defining expression of `c`; its cardinality is taken in `ℕ∞` (`encard`).
-- source:
--   Abram, Datta, Dutta, Roy, Obfuscation via Proofs of Equivalence and Polynomial-Time Reductions to Falsifiable Assumptions, STOC 2027 submission (manuscript sha256 f9518747…), pp. 48-49, Definition 3.5

import Mathlib
import Definitions.Def_ObfEF_Incremental_Circuit
import Definitions.Def_ObfEF_Incremental_Formula
import Definitions.Def_ObfEF_Incremental_Eqv

/-!
# Derivations of width three (Definition 3.5)

Abram, Datta, Dutta, Roy, *Obfuscation via Proofs of Equivalence and Polynomial-Time Reductions to
Falsifiable Assumptions*, STOC 2027 submission (manuscript sha256 f9518747…), pp. 48–49,
Definition 3.5 and the paragraph before it.

Variables. For circuits `C₀, C₁ : Circuit (Fin il) ol` the input variable `x_r` is `var r`
(`r < il`), the variable `y^b_j` of noninput vertex `j` of `C_b` is `var (il + 2j + b)`, and the
variable of the input vertex `v_r` is `x_r`. The defining formula of noninput vertex `j` of `C_b`
is `eq(y^b_j, t)` with `t` its instruction over the variables of its in-neighbours
(`Circuit.instrF`). Every other variable must be the variable of an extension axiom line.

A derivation is a list `θ` of formulas (lines `0, …, |θ| - 1`). Line `i` is used with
`θ.getD i ⊥`; every index used is in range.
-/

namespace ObfEF.Incremental

open Fml

namespace Deriv

variable {il ol : ℕ}

/-- The number of `y^b_j`: `il + 2j + b`. -/
def yVar (il : ℕ) (b : Bool) (j : ℕ) : ℕ := il + 2 * j + if b then 1 else 0

/-- The variable of a vertex of `C_b`: `x_r` for the input `v_r`, `y^b_j` for noninput `j`. -/
def vtxVar (C : Circuit (Fin il) ol) (b : Bool) : Fin il ⊕ Fin C.size → Fml
  | .inl r => var r
  | .inr j => var (yVar il b j)

/-- The defining expression `t` of noninput vertex `j` of `C_b`. -/
def vertexExpr (C : Circuit (Fin il) ol) (b : Bool) (j : Fin C.size) : Fml :=
  C.instrF (vtxVar C b) (.inr j)

/-- The definition `eq(y^b_j, t)` of noninput vertex `j` of `C_b`. -/
def vertexDef (C : Circuit (Fin il) ol) (b : Bool) (j : Fin C.size) : Fml :=
  eqF (vtxVar C b (.inr j)) (vertexExpr C b j)

/-- The definitions of all noninput vertices of `C₀` and `C₁`. -/
def vertexDefs (C₀ C₁ : Circuit (Fin il) ol) : List Fml :=
  (List.finRange C₀.size).map (vertexDef C₀ false) ++ (List.finRange C₁.size).map (vertexDef C₁ true)

/-- `v` is the variable of a noninput vertex of `C₀` or `C₁`, with defining-variable set `D`. -/
def VertexDefines (C₀ C₁ : Circuit (Fin il) ol) (v : ℕ) (D : Finset ℕ) : Prop :=
  (∃ j : Fin C₀.size, v = yVar il false j ∧ D = (vertexExpr C₀ false j).vars) ∨
  (∃ j : Fin C₁.size, v = yVar il true j ∧ D = (vertexExpr C₁ true j).vars)

/-- Line `i` of `θ` is an extension axiom `z ↔ φ` admissible in a derivation: `z` differs from the
input variables and is absent from `φ` and from the earlier lines, and `φ` has at most two
variables. -/
def IsExtAt (il : ℕ) (θ : List Fml) (i z : ℕ) (φ : Fml) : Prop :=
  i < θ.length ∧ θ.getD i bot = iff (var z) φ ∧ il ≤ z ∧ z ∉ φ.vars ∧
    (∀ j < i, z ∉ (θ.getD j bot).vars) ∧ φ.vars.card ≤ 2

/-- `v` is defined by a line earlier than line `i`, and `D` is the set of variables of its
defining expression (`t` for a vertex variable, `φ` for an extension axiom `v ↔ φ`). -/
def DefinedBefore (C₀ C₁ : Circuit (Fin il) ol) (θ : List Fml) (i v : ℕ) (D : Finset ℕ) : Prop :=
  VertexDefines C₀ C₁ v D ∨
  ∃ j < i, C₀.size + C₁.size ≤ j ∧ ∃ φ : Fml, IsExtAt il θ j v φ ∧ D = φ.vars

/-- The variables remaining after the chosen variables `Ch` (with defining-variable sets `dv`) are
unfolded repeatedly in the variable set `V`: the unchosen variables reachable from `V` through
chains of chosen variables. -/
def remaining (Ch : Finset ℕ) (dv : ℕ → Finset ℕ) (V : Finset ℕ) : Set ℕ :=
  {u | u ∉ Ch ∧ ∃ v ∈ V, Relation.ReflTransGen (fun a b => a ∈ Ch ∧ b ∈ dv a) v u}

/-- The variables of the step formed by line `i` with premises `P`. -/
def stepVars (θ : List Fml) (i : ℕ) (P : Finset ℕ) : Finset ℕ :=
  (θ.getD i bot).vars ∪ P.biUnion fun p => (θ.getD p bot).vars

/-- The step (line `i`, premises `P`) has width at most 3: some choice of at most three variables
of the step, each defined by an earlier line, leaves at most three variables after unfolding. -/
def WidthLe3 (C₀ C₁ : Circuit (Fin il) ol) (θ : List Fml) (i : ℕ) (P : Finset ℕ) : Prop :=
  ∃ (Ch : Finset ℕ) (dv : ℕ → Finset ℕ), Ch.card ≤ 3 ∧ Ch ⊆ stepVars θ i P ∧
    (∀ c ∈ Ch, DefinedBefore C₀ C₁ θ i c (dv c)) ∧
    (remaining Ch dv (stepVars θ i P)).encard ≤ 3

/-- Line `i` and the earlier lines `P` form a step: every assignment satisfying the premises
satisfies the line. -/
def IsStep (θ : List Fml) (i : ℕ) (P : Finset ℕ) : Prop :=
  (∀ p ∈ P, p < i) ∧
    ∀ α : ℕ → Bool, (∀ p ∈ P, (θ.getD p bot).eval α = true) → (θ.getD i bot).eval α = true

end Deriv

open Deriv in
/-- `θ` is a derivation of width three for `C₀` and `C₁` (Definition 3.5):
1. its first lines are the definitions of the noninput vertices of `C₀` and `C₁` (in some order);
2. every later line is an admissible extension axiom, or forms a step of width at most 3 with at
   most three premises;
3. for every output `k`, `eq(y⁰_{u⁰_k}, y¹_{u¹_k})` is a line;
4. every variable is an input variable, the variable of a vertex, or the variable of an extension
   axiom line. -/
def IsDerivationW3 {il ol : ℕ} (C₀ C₁ : Circuit (Fin il) ol) (θ : List Fml) : Prop :=
  (C₀.size + C₁.size ≤ θ.length ∧ (θ.take (C₀.size + C₁.size)).Perm (vertexDefs C₀ C₁)) ∧
  (∀ i, C₀.size + C₁.size ≤ i → i < θ.length →
    (∃ (z : ℕ) (φ : Fml), IsExtAt il θ i z φ) ∨
    (∃ P : Finset ℕ, P.card ≤ 3 ∧ IsStep θ i P ∧ WidthLe3 C₀ C₁ θ i P)) ∧
  (∀ k : Fin ol, eqF (vtxVar C₀ false (C₀.out k)) (vtxVar C₁ true (C₁.out k)) ∈ θ) ∧
  (∀ ψ ∈ θ, ∀ v ∈ ψ.vars, v < il ∨ (∃ D, VertexDefines C₀ C₁ v D) ∨
    ∃ (j : ℕ) (φ : Fml), C₀.size + C₁.size ≤ j ∧ IsExtAt il θ j v φ)

end ObfEF.Incremental


