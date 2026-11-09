-- Prove2me | Definitions.Def_MultiplierAssoc206_Resolution_Assoc
-- name    : MultiplierAssoc206_Resolution_Assoc
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-08T09:14:29.210693+00:00
-- url     : https://prove2.me/theorems/b639bb54-0345-4c3b-b6eb-31af1d3ea5a9
-- title:
--   The associativity formula $\mathsf{Assoc}_n$
-- statement:
--   Let $(\mathrm{Mul}_n)_n$ be a family of multiplier encodings. The **associativity formula** $\mathsf{Assoc}_n$ (Definition 3.1) has as variables the bits of three $n$-bit inputs $x,y,z$, the wires of four multipliers, and miter variables $e_0,\dots,e_{4n-1}$. Its clauses are:
--
--   1. $\mathrm{Mul}_n(x,y;xy)$ and $\mathrm{Mul}_n(y,z;yz)$, the **inner multipliers**, each with its own wires;
--   2. $\mathrm{Mul}_{2n}(xy,z;(xy)z)$ and $\mathrm{Mul}_{2n}(x,yz;x(yz))$, the **outer multipliers**, each with its own wires; input bit $k$ of $xy$ (resp. $yz$) *is* the output wire $k$ of the inner multiplier, and the $n$-bit inputs $z$ (resp. $x$) are zero-padded to $2n$ bits by substituting the constant $0$ for the input bits $k\ge n$;
--   3. the miter clauses encoding $e_i\leftrightarrow\big(((xy)z)_i\oplus(x(yz))_i\big)$ for $0\le i<4n$, namely the four clauses $\neg e_i\vee a\vee b$, $\neg e_i\vee\neg a\vee\neg b$, $e_i\vee\neg a\vee b$, $e_i\vee a\vee\neg b$ with $a=((xy)z)_i$, $b=(x(yz))_i$;
--   4. the long miter clause $e_0\vee\cdots\vee e_{4n-1}$.
--
--   For an exact family the formula is unsatisfiable, since it asserts $(xy)z\ne x(yz)$.
--
--   **Formalization Note** The clause sets of the encodings are embedded by renaming their variables (inner multipliers) and by a substitution sending the outer input bits to the inner output wires and the padding bits to the constant $0$ (outer multipliers). The paper says only "miter clauses encoding" the equivalences; the four width-3 clauses are the standard choice, so that every clause other than the long one has width at most $\max(3,w_0)$ for a width bound $w_0$ of the family.
-- source:
--   Vincent Liew, Associativity of Multiplication Is Hard for Resolution, STOC 2027 submission #206 (October 2026), source.pdf SHA-256 676dcc4be9158c52d07aec1c9d48f53fa38289ed1b4dcb34b53adc70dbdd5ead, PDF p.6 (printed p.5), Definition 3.1 and Figure 2 (PDF pp.6–7)

import Mathlib
import Definitions.Def_MultiplierAssoc206_Resolution_Multiplier

namespace MultiplierAssoc206.Resolution

open Classical

/-! # The associativity formula `Assoc_n`

Liew, *Associativity of Multiplication Is Hard for Resolution*, Definition 3.1 (PDF p. 6).
The formula consists of four multiplier encodings `Mul_n(x,y;xy)`, `Mul_n(y,z;yz)`,
`Mul_{2n}(xy,z;(xy)z)` and `Mul_{2n}(x,yz;x(yz))`, each with its own wires; the inputs of the
outer multipliers are the output wires of the inner ones, and the `n`-bit inputs `x`, `z` of the
outer multipliers are zero-padded to `2n` bits. Miter variables `e_i` (`i < 4n`) satisfy
`e_i ↔ ((xy)z)_i ⊕ (x(yz))_i`, and the long clause `e_0 ∨ ⋯ ∨ e_{4n-1}` asserts that the two
outputs differ. -/

/-- The variables of `Assoc_n`, for inner wire type `W₁` (of `Mul_n`) and outer wire type `W₂`
(of `Mul_{2n}`): the input bits of `x, y, z`, the wires of the four multipliers, and the miter
variables. -/
inductive AssocVar (W₁ W₂ : Type) (n : ℕ) where
  | x (i : Fin n) : AssocVar W₁ W₂ n
  | y (i : Fin n) : AssocVar W₁ W₂ n
  | z (i : Fin n) : AssocVar W₁ W₂ n
  /-- a wire of the inner multiplier `xy` -/
  | xy (w : W₁) : AssocVar W₁ W₂ n
  /-- a wire of the inner multiplier `yz` -/
  | yz (w : W₁) : AssocVar W₁ W₂ n
  /-- a wire of the outer multiplier `(xy)z` -/
  | xy_z (w : W₂) : AssocVar W₁ W₂ n
  /-- a wire of the outer multiplier `x(yz)` -/
  | x_yz (w : W₂) : AssocVar W₁ W₂ n
  /-- the miter variable `e_i` -/
  | e (i : Fin (4 * n)) : AssocVar W₁ W₂ n

section

variable (Mul : (n : ℕ) → MulEncoding n) (n : ℕ)

/-- The variable type of `Assoc_n` built from the family `Mul`. -/
abbrev AVar := AssocVar (Mul n).W (Mul (2 * n)).W n

/-- `Mul_n(x, y; xy)`, embedded in the variables of `Assoc_n`. -/
noncomputable def innerXY : CNF (AVar Mul n) :=
  (Mul n).cnf.rename fun v =>
    match v with
    | .x i => AssocVar.x i
    | .y i => AssocVar.y i
    | .wire w => AssocVar.xy w

/-- `Mul_n(y, z; yz)`, embedded in the variables of `Assoc_n`. -/
noncomputable def innerYZ : CNF (AVar Mul n) :=
  (Mul n).cnf.rename fun v =>
    match v with
    | .x i => AssocVar.y i
    | .y i => AssocVar.z i
    | .wire w => AssocVar.yz w

/-- An `n`-bit input zero-padded to `2n` bits, as a substitution target: bit `k < n` is the
given variable, bits `k ≥ n` are the constant `0`. -/
def padInput (v : Fin n → AVar Mul n) (k : Fin (2 * n)) : Bool ⊕ Literal (AVar Mul n) :=
  if h : (k : ℕ) < n then Sum.inr (v ⟨k, h⟩, true) else Sum.inl false

/-- `Mul_{2n}(xy, z; (xy)z)`: its first input bit `k` is the output wire `k` of `xy`; its
second input is `z` zero-padded to `2n` bits (the constant `0` is substituted). -/
noncomputable def outerXYZ : CNF (AVar Mul n) :=
  (Mul (2 * n)).cnf.subst fun v =>
    match v with
    | .x k => Sum.inr (AssocVar.xy ((Mul n).out k), true)
    | .y k => padInput Mul n AssocVar.z k
    | .wire w => Sum.inr (AssocVar.xy_z w, true)

/-- `Mul_{2n}(x, yz; x(yz))`: its first input is `x` zero-padded to `2n` bits; its second
input bit `k` is the output wire `k` of `yz`. -/
noncomputable def outerXYZ' : CNF (AVar Mul n) :=
  (Mul (2 * n)).cnf.subst fun v =>
    match v with
    | .x k => padInput Mul n AssocVar.x k
    | .y k => Sum.inr (AssocVar.yz ((Mul n).out k), true)
    | .wire w => Sum.inr (AssocVar.x_yz w, true)

/-- The output bit `i < 4n` of `(xy)z`. -/
def outXYZ (i : Fin (4 * n)) : AVar Mul n :=
  AssocVar.xy_z ((Mul (2 * n)).out ⟨i, by have := i.2; omega⟩)

/-- The output bit `i < 4n` of `x(yz)`. -/
def outXYZ' (i : Fin (4 * n)) : AVar Mul n :=
  AssocVar.x_yz ((Mul (2 * n)).out ⟨i, by have := i.2; omega⟩)

/-- The four width-3 clauses of `e_i ↔ ((xy)z)_i ⊕ (x(yz))_i`. -/
noncomputable def miterClauses (i : Fin (4 * n)) : CNF (AVar Mul n) :=
  let e := AssocVar.e i
  let a := outXYZ Mul n i
  let b := outXYZ' Mul n i
  {{(e, false), (a, true), (b, true)}, {(e, false), (a, false), (b, false)},
   {(e, true), (a, false), (b, true)}, {(e, true), (a, true), (b, false)}}

/-- The long miter clause `e_0 ∨ ⋯ ∨ e_{4n-1}`. -/
noncomputable def longMiterClause : Clause (AVar Mul n) :=
  Finset.univ.image fun i : Fin (4 * n) => (AssocVar.e i, true)

/-- Definition 3.1 (Associativity formula) `Assoc_n` for the encoding family `Mul`. -/
noncomputable def Assoc : CNF (AVar Mul n) :=
  innerXY Mul n ∪ innerYZ Mul n ∪ outerXYZ Mul n ∪ outerXYZ' Mul n ∪
    (Finset.univ.biUnion fun i => miterClauses Mul n i) ∪ {longMiterClause Mul n}

end

end MultiplierAssoc206.Resolution


