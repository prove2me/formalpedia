-- Prove2me | Definitions.Def_KoanaKPaths_Main_Circuits
-- name    : KoanaKPaths_Main_Circuits
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-09T08:36:17.579417+00:00
-- url     : https://prove2.me/theorems/b5fb68a2-c1ca-4f3d-aad6-3ec2dffe32d1
-- title:
--   §2 — noncommutative polynomials, homogeneous 0–1 right-skew circuits and $N(P)$
-- statement:
--   The **noncommutative polynomial ring** $\mathbb Z\langle x_0,x_1,\dots\rangle$ consists of integer combinations of finite **words** in the variable symbols; multiplication concatenates words. For a word $\tau=(\tau_1,\dots,\tau_i)$ write $x_\tau=x_{\tau_1}\cdots x_{\tau_i}$ and $c_\tau$ for its coefficient. The monomial $x_\tau$ is **multilinear** if the entries of $\tau$ are pairwise distinct, and for a polynomial $P$
--   $$N(P)=\sum_{\tau\ \text{multilinear}} c_\tau ,$$
--   which for a 0–1 polynomial (all coefficients in $\{0,1\}$) is the number of its multilinear monomials.
--
--   A **right-skew circuit** is a finite directed acyclic graph with a designated output gate. Each gate is a constant $0$ or $1$, a binary addition $g=h_1+h_2$, or a product $g=h\,x_j$ that multiplies the polynomial of a previous gate $h$ **on the right** by one variable. The polynomial computed at each gate and its **syntactic degree** are defined recursively: constants have degree $0$, $h\,x_j$ has degree one more than $h$, and $h_1+h_2$ has the larger of the two degrees. The circuit is **homogeneous** if the two inputs of every addition gate have the same degree, and it is a **0–1 circuit** if every gate (used or not) computes a 0–1 polynomial.
--
--   These are the objects of Theorem 2: the polynomial $P$ computed at the output gate of a homogeneous 0–1 right-skew circuit of degree $k\ge1$, and the count $N(P)$ to be approximated.
--
--   **Formalization Note** The ring is `MonoidAlgebra ℤ (FreeMonoid ℕ)`, variables are indexed by natural numbers (every circuit over $x_1,\dots,x_n$ is one over $\mathbb N$-indexed variables, with the same polynomial and $N(P)$). A circuit is a list of gates in a topological order, each referring to earlier gates by position, with an output position; `WellFormed` requires the references to point backwards and the output to exist. Shared subcircuits and unused gates are allowed.
-- source:
--   Tomohiro Koana, STOC 2027 submission #953 (October 2026), p. 4 (PDF p. 5), Section 2, paragraphs 'Polynomials and tensors' and 'Circuits'

import Mathlib

noncomputable section

namespace KoanaKPaths.Main

/-- The noncommutative polynomial ring `ℤ⟨x₀, x₁, …⟩` (§2, printed p. 4): integer combinations of
finite **words** in the variable symbols, i.e. the monoid algebra of the free monoid on `ℕ`.
Multiplication concatenates words, so `x_τ = x_{τ₁} ⋯ x_{τᵢ}` is the word `[τ₁, …, τᵢ]` and
different orders of the same variables are different monomials. -/
abbrev NCPoly := MonoidAlgebra ℤ (FreeMonoid ℕ)

/-- The coefficient `c_τ` of the monomial `x_τ` (the word `τ`) in `P`. -/
def wordCoeff (P : NCPoly) (τ : List ℕ) : ℤ := MonoidAlgebra.coeff P (FreeMonoid.ofList τ)

/-- The monomial `x_j` (a single variable, a word of length one). -/
def NCPoly.var (j : ℕ) : NCPoly := MonoidAlgebra.of ℤ (FreeMonoid ℕ) (FreeMonoid.of j)

/-- `N(P)`, §2, printed p. 4: the sum of the coefficients of the **multilinear** monomials of `P`,
those whose word has pairwise distinct entries. For a 0–1 polynomial this is the number of its
multilinear monomials. -/
def numMultilinear (P : NCPoly) : ℤ :=
  ∑ w ∈ (MonoidAlgebra.coeff P).support with (FreeMonoid.toList w).Nodup, MonoidAlgebra.coeff P w

/-- A gate of a right-skew circuit (§2, printed p. 4). Predecessors are referred to by their
position in the gate list.
* `const b` is the constant input gate `0` (`b = false`) or `1` (`b = true`);
* `add g₁ g₂` is the binary addition gate `g = h₁ + h₂` with `h₁, h₂` the gates at positions `g₁, g₂`;
* `mulVar g j` is the product gate `g = h · x_j`, multiplying the polynomial of the gate `h` at
  position `g` **on the right** by the variable `x_j`. -/
inductive Gate where
  | const (b : Bool)
  | add (g₁ g₂ : ℕ)
  | mulVar (g : ℕ) (j : ℕ)
  deriving DecidableEq

/-- A right-skew circuit: a directed acyclic graph listed in a topological order (every gate refers
only to earlier gates, see `Circuit.WellFormed`), with a designated output gate. Unused gates and
shared subcircuits are allowed. -/
structure Circuit where
  gates : List Gate
  output : ℕ

/-- Gate `g` at position `i` refers only to gates at earlier positions. -/
def Gate.RefsBelow (i : ℕ) : Gate → Prop
  | .const _ => True
  | .add g₁ g₂ => g₁ < i ∧ g₂ < i
  | .mulVar g _ => g < i

/-- One evaluation step: the polynomial and syntactic degree of a gate, given the values of all
earlier gates (in order). Constants have degree `0`; `h · x_j` has degree one more than `h`;
`h₁ + h₂` has the larger of the two degrees (§2, printed p. 4). -/
def gateValue (vals : List (NCPoly × ℕ)) : Gate → NCPoly × ℕ
  | .const b => (if b then 1 else 0, 0)
  | .add g₁ g₂ =>
      ((vals.getD g₁ (0, 0)).1 + (vals.getD g₂ (0, 0)).1,
        max (vals.getD g₁ (0, 0)).2 (vals.getD g₂ (0, 0)).2)
  | .mulVar g j => ((vals.getD g (0, 0)).1 * NCPoly.var j, (vals.getD g (0, 0)).2 + 1)

namespace Circuit

/-- The polynomial computed at, and the syntactic degree of, every gate, in gate order. -/
def values (C : Circuit) : List (NCPoly × ℕ) :=
  C.gates.foldl (fun acc g => acc ++ [gateValue acc g]) []

/-- The noncommutative polynomial computed at the gate at position `i`. -/
def poly (C : Circuit) (i : ℕ) : NCPoly := (C.values.getD i (0, 0)).1

/-- The syntactic degree of the gate at position `i`. -/
def deg (C : Circuit) (i : ℕ) : ℕ := (C.values.getD i (0, 0)).2

/-- The polynomial `P` computed by the circuit (at its output gate). -/
def outputPoly (C : Circuit) : NCPoly := C.poly C.output

/-- The circuit is a directed acyclic graph in topological order with an existing output gate. -/
def WellFormed (C : Circuit) : Prop :=
  C.output < C.gates.length ∧ ∀ (i : ℕ) (h : i < C.gates.length), (C.gates[i]'h).RefsBelow i

/-- Homogeneous (§2): the two inputs of every addition gate have the same syntactic degree. -/
def Homogeneous (C : Circuit) : Prop :=
  ∀ (i : ℕ) (h : i < C.gates.length) (g₁ g₂ : ℕ), C.gates[i]'h = .add g₁ g₂ → C.deg g₁ = C.deg g₂

/-- 0–1 circuit (§2): **every** gate (used or not) computes a polynomial all of whose
coefficients are `0` or `1`. -/
def ZeroOne (C : Circuit) : Prop :=
  ∀ i < C.gates.length, ∀ τ : List ℕ, wordCoeff (C.poly i) τ = 0 ∨ wordCoeff (C.poly i) τ = 1

/-- `C` is a homogeneous 0–1 right-skew circuit whose output gate has degree `k`; it computes the
noncommutative 0–1 polynomial `C.outputPoly` of degree `k` of Theorem 2. -/
def IsHomZeroOne (C : Circuit) (k : ℕ) : Prop :=
  C.WellFormed ∧ C.Homogeneous ∧ C.ZeroOne ∧ C.deg C.output = k

end Circuit

end KoanaKPaths.Main

end


