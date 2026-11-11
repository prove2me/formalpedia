-- Prove2me | Definitions.Def_DistLTLSynth_Char_Model
-- name    : DistLTLSynth_Char_Model
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-10T21:14:59.030946+00:00
-- url     : https://prove2.me/theorems/e1e7e98c-cff3-43bb-b7b7-fc80f417939c
-- title:
--   Communication graphs Γ, input signals, views (Table 1), distributed algorithms, executions, Pref and left quotients
-- statement:
--   Two processes $1, 2$ compute in synchronous rounds $r \ge 1$. The set of **communication graphs** is $\Gamma = \{(1\to 2), (1\leftrightarrow 2), (1\leftarrow 2)\}$: in $(1\to2)$ only process $2$ hears from process $1$, in $(1\leftarrow 2)$ only process $1$ hears from $2$, in $(1\leftrightarrow2)$ both hear each other. $\Gamma$ is discrete and $\Gamma^\omega$ (infinite words, $w(0)$ being the round-1 letter) carries the product topology. A **message adversary** is any $A \subseteq \Gamma^\omega$.
--
--   Given input sets $X_1, X_2$, the **input signals** are $\Sigma = X_1 \times X_2 \times \Gamma$. **Views** are labeled tuples: $v_p(\varepsilon) = I_p$ and, for $h = h'\cdot(x_1,x_2,g)$ with $u = v_1(h')$, $v = v_2(h')$ (Table 1):
--   $$\begin{array}{c|cc} g & v_1(h) & v_2(h)\\\hline (1\to2) & N_1(x_1,u) & C_2(x_2,v,x_1,u)\\ (1\leftrightarrow2) & C_1(x_1,u,x_2,v) & C_2(x_2,v,x_1,u)\\ (1\leftarrow2) & C_1(x_1,u,x_2,v) & N_2(x_2,v)\end{array}$$
--   The constructors $I_1, I_2, N_1, N_2, C_1, C_2$ are distinct and injective (an inductive type).
--
--   A **distributed algorithm** $f=(f_1,f_2)$ assigns outputs $f_p(v)\in Y_p$ to views. On $h\in\Sigma^\omega$ the **execution** $\mathrm{exec}(f,h)\in(\Sigma\times\Omega)^\omega$, $\Omega=Y_1\times Y_2$, has round-$r$ letter $(h[r], (f_1(v_1(h[\ldots r])), f_2(v_2(h[\ldots r]))))$: the round-$r$ output sees round $r$'s input and messages. $\mathrm{Graph}$ projects to $\Gamma^\omega$. $f$ **realizes** $L \subseteq (\Sigma\times\Omega)^\omega$ under $A$ if $\mathrm{exec}(f,h)\in L$ for every $h\in\Sigma^\omega$ with $\mathrm{Graph}(h)\in A$.
--
--   $\mathrm{Pref}(A)$ is the set of finite prefixes of words of $A$ (a finite graph history is **live** under $A$ iff it is in $\mathrm{Pref}(A)$, Definition 6.14), and $h^{-1}A = \{k \mid h\cdot k\in A\}$ is the **left quotient**.
--
--   **Formalization Note.** Finite histories are lists in chronological order; `views` folds Table 1 over them. $f_p$ is total on view terms; its values on terms that are not process-$p$ views never enter an execution. `leftQuot h A` is defined for every $h$ (empty when $h\notin\mathrm{Pref}(A)$).
-- source:
--   Bollig, Bouyer-Decitre, Függer, Ghosh, Nowak, Sznajder, Distributed LTL Synthesis under Arbitrary Message Adversaries, STOC 2027 submission (PDF sha256 71476b49…), pp. 4–6 (PDF 5–7), §2.1–2.3, Table 1; p. 28 (PDF 29), Definition 6.14; p. 8 (PDF 9), left quotient

import Mathlib

namespace DistLTLSynth.Char

/-- The communication graphs `Γ = {(1 → 2), (1 ↔ 2), (1 ← 2)}` (§2.1, p. 5).
`oneToTwo` = `(1 → 2)`: only process 2 hears from process 1;
`both` = `(1 ↔ 2)`: both processes hear from each other;
`twoToOne` = `(1 ← 2)`: only process 1 hears from process 2.
The empty graph is not a communication graph. -/
inductive CommGraph : Type where
  | oneToTwo
  | both
  | twoToOne
  deriving DecidableEq, Encodable, Repr

instance : Fintype CommGraph :=
  Fintype.ofList [CommGraph.oneToTwo, CommGraph.both, CommGraph.twoToOne]
    (by intro g; cases g <;> simp)

/-- `Γ` is discrete; `Γ^ω = ℕ → CommGraph` then carries the product topology (§2.5, p. 7). -/
instance : TopologicalSpace CommGraph := ⊥

instance : DiscreteTopology CommGraph := ⟨rfl⟩

/-- Input signals `Σ := X₁ × X₂ × Γ` (§2.2, p. 5). -/
abbrev Signal (X1 X2 : Type) : Type := X1 × X2 × CommGraph

/-- Local views (§2.2, Table 1, p. 5). `I1`, `I2` are the initial views (the process
identifiers); `N1 x₁ u`, `N2 x₂ v` are the no-communication tuples and
`C1 x₁ u x₂ v`, `C2 x₂ v x₁ u` the communication tuples. Distinct constructors are distinct
and each constructor is injective, as the paper's labeled tuples. -/
inductive View (X1 X2 : Type) : Type where
  | I1 : View X1 X2
  | I2 : View X1 X2
  | N1 (x1 : X1) (u : View X1 X2) : View X1 X2
  | N2 (x2 : X2) (v : View X1 X2) : View X1 X2
  | C1 (x1 : X1) (u : View X1 X2) (x2 : X2) (v : View X1 X2) : View X1 X2
  | C2 (x2 : X2) (v : View X1 X2) (x1 : X1) (u : View X1 X2) : View X1 X2
  deriving DecidableEq, Encodable

/-- One row of Table 1: from the previous views `(u, v) = (v₁(h'), v₂(h'))` and the last
letter `(x₁, x₂, g)`, the views `(v₁(h' · (x₁, x₂, g)), v₂(h' · (x₁, x₂, g)))`. -/
def viewStep {X1 X2 : Type} (uv : View X1 X2 × View X1 X2) (a : Signal X1 X2) :
    View X1 X2 × View X1 X2 :=
  match a with
  | (x1, x2, CommGraph.oneToTwo) => (View.N1 x1 uv.1, View.C2 x2 uv.2 x1 uv.1)
  | (x1, x2, CommGraph.both) => (View.C1 x1 uv.1 x2 uv.2, View.C2 x2 uv.2 x1 uv.1)
  | (x1, x2, CommGraph.twoToOne) => (View.C1 x1 uv.1 x2 uv.2, View.N2 x2 uv.2)

/-- The pair of views at the end of a finite input signal history `h ∈ Σ*`, listed in
chronological order (`h.head` is round 1); `views [] = (I₁, I₂)`. -/
def views {X1 X2 : Type} (h : List (Signal X1 X2)) : View X1 X2 × View X1 X2 :=
  h.foldl viewStep (View.I1, View.I2)

/-- `v₁(h)`. -/
def view1 {X1 X2 : Type} (h : List (Signal X1 X2)) : View X1 X2 := (views h).1

/-- `v₂(h)`. -/
def view2 {X1 X2 : Type} (h : List (Signal X1 X2)) : View X1 X2 := (views h).2

/-- A distributed algorithm `f = (f₁, f₂)` (§2.3, p. 6): each process's output is a function
of its own local view only. The functions are total on the type of views; their values on
terms that are not views of the given process (`Views_p`) never enter an execution. -/
structure Algorithm (X1 X2 Y1 Y2 : Type) : Type where
  f1 : View X1 X2 → Y1
  f2 : View X1 X2 → Y2

/-- The length-`r` prefix `w[...r]` of an infinite word `w : ℕ → α`
(`w 0` is the letter of round 1). -/
def pre {α : Type} (w : ℕ → α) (r : ℕ) : List α := List.ofFn (fun i : Fin r => w i)

/-- The concatenation `u · w` of a finite word and an infinite word. -/
def append {α : Type} (u : List α) (w : ℕ → α) : ℕ → α :=
  fun n => if h : n < u.length then u[n] else w (n - u.length)

/-- `Graph : Σ^ω → Γ^ω`, the round-wise projection to the communication graph. -/
def graphOf {X1 X2 : Type} (h : ℕ → Signal X1 X2) : ℕ → CommGraph := fun n => (h n).2.2

/-- The graph history of an execution `e ∈ (Σ × Ω)^ω`. -/
def graphOfExec {X1 X2 Y1 Y2 : Type} (e : ℕ → Signal X1 X2 × (Y1 × Y2)) : ℕ → CommGraph :=
  fun n => (e n).1.2.2

/-- The execution `exec(f, h) ∈ (Σ × Ω)^ω` (§2.3, p. 6): its round-`r` letter (index `r - 1`)
is `(h[r], (f₁(v₁(h[...r])), f₂(v₂(h[...r]))))`, so the round-`r` output sees round `r`'s
input and messages. -/
def exec {X1 X2 Y1 Y2 : Type} (f : Algorithm X1 X2 Y1 Y2) (h : ℕ → Signal X1 X2) :
    ℕ → Signal X1 X2 × (Y1 × Y2) :=
  fun n => (h n, (f.f1 (view1 (pre h (n + 1))), f.f2 (view2 (pre h (n + 1)))))

/-- `f` LL-realizes the language `L ⊆ (Σ × Ω)^ω` under the message adversary `A ⊆ Γ^ω`:
`exec(f, h) ∈ L` for every `h ∈ Σ^ω` with `Graph(h) ∈ A` (inputs unrestricted). -/
def RealizesLang {X1 X2 Y1 Y2 : Type} (f : Algorithm X1 X2 Y1 Y2) (A : Set (ℕ → CommGraph))
    (L : Set (ℕ → Signal X1 X2 × (Y1 × Y2))) : Prop :=
  ∀ h : ℕ → Signal X1 X2, graphOf h ∈ A → exec f h ∈ L

/-- `Pref(A)`: the finite prefixes of words of `A`; a finite graph history is *live* under `A`
(Definition 6.14) iff it belongs to `Pref A`. -/
def Pref {α : Type} (A : Set (ℕ → α)) : Set (List α) :=
  {u | ∃ w ∈ A, pre w u.length = u}

/-- The left quotient `h⁻¹A := {k ∈ Γ^ω | h · k ∈ A}`. (The paper defines it for
`h ∈ Pref(A)`; for other `h` this set is empty.) -/
def leftQuot {α : Type} (h : List α) (A : Set (ℕ → α)) : Set (ℕ → α) :=
  {k | append h k ∈ A}

end DistLTLSynth.Char


