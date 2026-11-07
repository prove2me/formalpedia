-- Prove2me | Definitions.Def_FixpReciprocal_RGate
-- name    : FixpReciprocal_RGate
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T02:47:25.042229+00:00
-- url     : https://prove2.me/theorems/c8827c10-88ac-40a6-ae62-c490437615a3
-- title:
--   The gates of (1) and generalized circuits over them (Definition 3.3)
-- statement:
--   A **generalized circuit with the gates of (1)** is a list of $N\ge1$ gates, one for each variable $x_i$, of the form
--   $$x_i=[\![a\,x_j+b\,x_k+c]\!]\qquad\text{or}\qquad x_i=\frac{1}{1+\tau x_j},$$
--   with binary-encoded rationals $a,b,c$ and indices $j,k\in[N]$. Indices may repeat or equal $i$, and the dependency graph may contain cycles. A **solution** is a vector $x\in[0,1]^N$ satisfying every equation simultaneously.
--
--   A gate of arity zero is a **constant gate**. Here that is a clipped affine gate with $a=b=0$.
--
--   **Formalization Note** Indices are $0$-based. Since "Arguments with zero coefficients may be omitted, so constants and unary gates belong to $\mathcal A$" (p.11), a single constructor covers all of $\mathcal A$; a constant gate carries valid dummy indices. The rational $\tau$ is not part of a gate: it is a parameter of the semantics.
-- source:
--   Shimizu, FIXP-Completeness via Reciprocal Gates: Applications to Second-Price Auctions (STOC 2027 submission, sha256 ffcad4a7…), display (1), p.2 (PDF p.4); Definition 3.3 and display (4), pp.10–11 (PDF pp.12–13)

import Mathlib
import Definitions.Def_OnlineCRS_Combine_Sym
import Definitions.Def_FixpReciprocal_clip
import Definitions.Def_FixpReciprocal_frame
import Definitions.Def_FixpReciprocal_RealSearch

namespace FixpReciprocal

open OnlineCRS.Combine

/-- **The gates of (1):** the clipped affine gate `x_i = ⟦a x_j + b x_k + c⟧` and the reciprocal gate
`x_i = 1 / (1 + τ x_j)`, with input indices.

Shimizu, *FIXP-Completeness via Reciprocal Gates: Applications to Second-Price Auctions*, STOC 2027 submission (sha256 ffcad4a7…), display (1), p.2; display (4) and Definition 3.3, pp.10–11.

**Formalization Note.** Indices are 0-based. "Arguments with zero coefficients may be omitted, so constants
and unary gates belong to A" (p.11): one constructor `aff` covers all of `A`, a constant gate being
`aff 0 0 c j k` with valid dummy indices. `τ` is not part of a gate; it is a parameter of the semantics. -/
inductive RGate where
  | aff (a b c : ℚ) (j k : ℕ)
  | recip (j : ℕ)

/-- The right-hand side of the gate equation, for the wire values `v`. -/
noncomputable def RGate.eval (τ : ℚ) (v : ℕ → ℝ) : RGate → ℝ
  | .aff a b c j k => clip ((a : ℝ) * v j + (b : ℝ) * v k + (c : ℝ))
  | .recip j => reciprocal τ (v j)

/-- The gate's input indices are below `N`. -/
def RGate.ReadsBelow (N : ℕ) : RGate → Prop
  | .aff _ _ _ j k => j < N ∧ k < N
  | .recip j => j < N

/-- A gate of arity zero: a clipped affine gate with both coefficients zero. -/
def RGate.IsConstant : RGate → Prop
  | .aff a b _ _ _ => a = 0 ∧ b = 0
  | .recip _ => False

/-- **A circuit of gates of (1) (Definition 3.3):** `N ≥ 1` gates, indices in `[N]`. Repeated inputs, self-inputs
and cycles are allowed.

Shimizu, *FIXP-Completeness via Reciprocal Gates: Applications to Second-Price Auctions*, STOC 2027 submission (sha256 ffcad4a7…), Definition 3.3, pp.10–11. -/
def RValid (C : List RGate) : Prop :=
  1 ≤ C.length ∧ ∀ g ∈ C, g.ReadsBelow C.length

/-- **The solutions of a circuit (Definition 3.3):** assignments `x ∈ [0, 1]^N` satisfying every gate.

Shimizu, *FIXP-Completeness via Reciprocal Gates: Applications to Second-Price Auctions*, STOC 2027 submission (sha256 ffcad4a7…), Definition 3.3, p.11.

**Formalization Note.** This is a system of equations over one vector, so cycles and `i = j` are allowed,
never an in-order evaluation. -/
def RCircuitSol (τ : ℚ) (C : List RGate) : Set (Fin C.length → ℝ) :=
  {x | (∀ i, x i ∈ Set.Icc (0 : ℝ) 1) ∧ ∀ i : Fin C.length, x i = (C.get i).eval τ (lookup x)}

/-- Numeric form of a gate. -/
def RGate.code : RGate → ℕ × ℚ × ℚ × ℚ × ℕ × ℕ
  | .aff a b c j k => (0, a, b, c, j, k)
  | .recip j => (1, 0, 0, 0, j, 0)

theorem RGate.code_injective : Function.Injective RGate.code := by
  intro a b h
  cases a <;> cases b <;> simp_all [RGate.code]

/-- Binary encoding of a gate. -/
def encRGate (g : RGate) : List Sym :=
  fNat g.code.1 ++ fRat g.code.2.1 ++ fRat g.code.2.2.1 ++ fRat g.code.2.2.2.1 ++
    fNat g.code.2.2.2.2.1 ++ fNat g.code.2.2.2.2.2

/-- Binary encoding of a list of gates ("the coefficients are binary-encoded rationals", p.2). -/
def encRGates : List RGate → List Sym := fList encRGate

theorem encRGate_prefixFree : PrefixFree encRGate := by
  intro a b s t h
  simp only [encRGate, List.append_assoc] at h
  obtain ⟨h1, h⟩ := fNat_prefixFree h
  obtain ⟨h2, h⟩ := fRat_prefixFree h
  obtain ⟨h3, h⟩ := fRat_prefixFree h
  obtain ⟨h4, h⟩ := fRat_prefixFree h
  obtain ⟨h5, h⟩ := fNat_prefixFree h
  obtain ⟨h6, h⟩ := fNat_prefixFree h
  exact ⟨RGate.code_injective
    (Prod.ext h1 (Prod.ext h2 (Prod.ext h3 (Prod.ext h4 (Prod.ext h5 h6))))), h⟩

theorem encRGates_injective : Function.Injective encRGates :=
  encRGate_prefixFree.fList.injective

end FixpReciprocal


