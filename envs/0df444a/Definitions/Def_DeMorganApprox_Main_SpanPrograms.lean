-- Prove2me | Definitions.Def_DeMorganApprox_Main_SpanPrograms
-- name    : DeMorganApprox_Main_SpanPrograms
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-08T11:59:11.645033+00:00
-- url     : https://prove2.me/theorems/c942c83b-01d8-4092-821f-076e9eaa54cf
-- title:
--   Definitions 3.1–3.2 — vector-form span programs, witnesses, witness parameters and the absolute norm
-- statement:
--   A **vector-form span program** (Definition 3.1) on the input variables $x_1,\dots,x_m$ consists of a real Euclidean space $H$, a unit **target** vector $\tau\in H$, and a finite list of unit vectors $v_1,\dots,v_N\in H$, each labelled *always available*, $x_i$, or $\neg x_i$. On input $x$, an always-available vector is available, an $x_i$-labelled vector is available exactly when $x_i=1$, and a $\neg x_i$-labelled vector exactly when $x_i=0$. Let $I_x$ be the set of available indices. The program **accepts** $x$ iff
--   $$\tau\in\operatorname{span}\{v_j: j\in I_x\}.$$
--   Let $V$ be the matrix with columns $v_1,\dots,v_N$ and $V_x$ the matrix whose $j$-th column is $v_j$ if $j\in I_x$ and $0$ otherwise. On an accepted input a **1-witness** is a coefficient vector $a$ with $V_xa=\tau$; on a rejected input a **0-witness** is $w\in H$ with $w^\top\tau=1$ and $w^\top V_x=0$. The program **computes** $f$ if it accepts exactly the inputs with $f(x)=1$.
--
--   For $A,B\ge1$ the target has **witness parameters** $(A,B)$ (Definition 3.2) if every accepted input has a 1-witness with $\|a\|_2^2\le A$ and every rejected input has a 0-witness with $\|w\|_2^2\le B$. It has **balanced witness bound** $S\ge1$ if it has witness parameters $(S,S)$. Witness sizes are squared Euclidean norms.
--
--   Finally, $\|\operatorname{abs}(V)\|\le K$ means that the matrix $\operatorname{abs}(V)$ of entrywise absolute values of the full matrix $V$ (all columns, regardless of input and label) satisfies $\|\operatorname{abs}(V)y\|_2\le K\|y\|_2$ for every coefficient vector $y$, i.e. its $\ell_2\to\ell_2$ operator norm is at most $K$ (§3.1).
--
--   These are the hypotheses of the extraction lemma (Lemma 4.1) and the invariants of the construction in §5.
--
--   **Formalization Note** $H$ is the coordinate space $\iota\to\mathbb R$ for a finite type $\iota$, with its standard basis, since $\operatorname{abs}(V)$ depends on the basis; the listed vectors are indexed by a finite type $J$. The raw structure `SpanProgram` carries only the data; unit norms are the separate predicate `IsVectorForm`. A 1-witness may take any values on unavailable columns, since $V_x$ zeroes them.
-- source:
--   Yichuan Wang, STOC 2027 submission #76 (October 2026), Definitions 3.1 and 3.2, PDF p. 11 (printed p. 9), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/76.pdf; §3.1 operator norm and abs(·), PDF p. 10 (printed p. 8)

import Mathlib
import Definitions.Def_DeMorganApprox_Main_Basic

namespace DeMorganApprox.Main

/-- The label of a listed vector (Definition 3.1, PDF p. 11): always available, `xᵢ`, or `¬xᵢ`. -/
inductive Label (m : ℕ) : Type where
  | always : Label m
  | pos (i : Fin m) : Label m
  | neg (i : Fin m) : Label m
  deriving DecidableEq

/-- Availability on input `x`: always; `xᵢ` exactly when `xᵢ = 1`; `¬xᵢ` exactly when `xᵢ = 0`. -/
def Label.avail {m : ℕ} : Label m → (Fin m → Bool) → Bool
  | always, _ => true
  | pos i, x => x i
  | neg i, x => !x i

/-- Raw data of a vector-form span program (Definition 3.1) on the Euclidean space `ι → ℝ`
with its standard basis: a target vector and a finite family of labelled vectors indexed by `J`.
Unit norms are a separate predicate, `IsVectorForm`. -/
structure SpanProgram (m : ℕ) (ι J : Type) where
  target : ι → ℝ
  vec : J → ι → ℝ
  label : J → Label m

/-- Squared Euclidean norm. -/
def sqNorm {α : Type} [Fintype α] (v : α → ℝ) : ℝ := ∑ a, v a ^ 2

namespace SpanProgram

variable {m : ℕ} {ι J : Type} [Fintype ι] [Fintype J]

/-- The target and every listed vector have Euclidean norm one. -/
def IsVectorForm (P : SpanProgram m ι J) : Prop :=
  sqNorm P.target = 1 ∧ ∀ j, sqNorm (P.vec j) = 1

/-- The program accepts `x` iff its target lies in the real span of the available vectors. -/
def Accepts (P : SpanProgram m ι J) (x : Fin m → Bool) : Prop :=
  P.target ∈ Submodule.span ℝ (P.vec '' {j | (P.label j).avail x = true})

/-- `V_x a`: the combination of the available vectors with coefficients `a`; columns of
unavailable vectors are zero. -/
def applyAvail (P : SpanProgram m ι J) (x : Fin m → Bool) (a : J → ℝ) : ι → ℝ :=
  fun i => ∑ j, if (P.label j).avail x then a j * P.vec j i else 0

/-- A 1-witness on input `x`: a coefficient vector `a` with `V_x a = τ`. -/
def IsOneWitness (P : SpanProgram m ι J) (x : Fin m → Bool) (a : J → ℝ) : Prop :=
  P.applyAvail x a = P.target

/-- A 0-witness on input `x`: `w` with `w⊤τ = 1` and `w⊤v_j = 0` for every available `v_j`. -/
def IsZeroWitness (P : SpanProgram m ι J) (x : Fin m → Bool) (w : ι → ℝ) : Prop :=
  ∑ i, w i * P.target i = 1 ∧
    ∀ j, (P.label j).avail x = true → ∑ i, w i * P.vec j i = 0

/-- Witness parameters `(A, B)` (Definition 3.2, PDF p. 11): `A, B ≥ 1`, every accepted input
has a 1-witness of squared norm at most `A`, and every rejected input has a 0-witness of
squared norm at most `B`. -/
def HasWitnessParams (P : SpanProgram m ι J) (A B : ℝ) : Prop :=
  1 ≤ A ∧ 1 ≤ B ∧
    ∀ x, (P.Accepts x → ∃ a, P.IsOneWitness x a ∧ sqNorm a ≤ A) ∧
      (¬ P.Accepts x → ∃ w, P.IsZeroWitness x w ∧ sqNorm w ≤ B)

/-- Balanced witness bound `S` (Definition 3.2): witness parameters `(S, S)`. -/
def HasBalancedBound (P : SpanProgram m ι J) (S : ℝ) : Prop :=
  P.HasWitnessParams S S

/-- The program computes `f`: it accepts exactly the inputs with `f x = 1`. -/
def Computes (P : SpanProgram m ι J) (f : (Fin m → Bool) → Bool) : Prop :=
  ∀ x, P.Accepts x ↔ f x = true

end SpanProgram

/-- `‖abs(V)‖ ≤ K` for the matrix `V` with columns `V j` (§3.1, PDF p. 10): for every coefficient
vector `y`, `‖abs(V) y‖₂ ≤ K ‖y‖₂`, where `abs(V)` takes entrywise absolute values. It is a
property of the full fixed matrix; labels play no role. -/
def AbsNormLE {ι J : Type} [Fintype ι] [Fintype J] (V : J → ι → ℝ) (K : ℝ) : Prop :=
  ∀ y : J → ℝ, Real.sqrt (∑ i, (∑ j, |V j i| * y j) ^ 2) ≤ K * Real.sqrt (∑ j, y j ^ 2)

end DeMorganApprox.Main


