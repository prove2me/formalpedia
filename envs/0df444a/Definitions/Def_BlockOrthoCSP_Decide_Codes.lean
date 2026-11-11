-- Prove2me | Definitions.Def_BlockOrthoCSP_Decide_Codes
-- name    : BlockOrthoCSP_Decide_Codes
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-10T19:12:25.1112+00:00
-- url     : https://prove2.me/theorems/ea0cc4c1-ad3d-4890-bb9d-733ae852350c
-- title:
--   Exact codes of algebraic numbers, inputs $(q, \mathcal F)$, instances and polynomials, and their decoding
-- statement:
--   Algorithms act on finite codes; this module fixes them.
--
--   - An **algebraic-number code** is a list of integer coefficients (constant term first) of a nonzero polynomial together with a closed rational box $[\mathrm{re}_{lo}, \mathrm{re}_{hi}] \times [\mathrm{im}_{lo}, \mathrm{im}_{hi}]$ (each rational $n/(d+1)$ coded by $(n,d) \in \mathbb Z \times \mathbb N$). It is **valid** if exactly one root of the polynomial lies in the box, and it then denotes that root.
--   - An **input code** is $q$ and a list of function codes, each an arity $r$ and the list of the $q^r$ value codes of $f$ in lexicographic order of $D^r$ (first coordinate most significant). It is valid if $q \ge 1$, every $r \ge 1$, every list has length $q^r$ and every value code is valid; it decodes to the finite set $\mathcal F$ of the decoded functions (duplicates identified).
--   - An **instance code** is the number of hidden variables and a list of constraints (position of the function in the input list, list of scope variables); it decodes, for a given number $t$ of retained variables, to an instance when well formed.
--   - A **polynomial code** is a list of monomials (coefficient code, list of (variable code, exponent)); variables $X_a$ ($a \in D^k$) are coded by the list of the entries of $a$, and in Theorem F.5.8 $X_a, Y_a$ by $(\mathrm{false}, a)$, $(\mathrm{true}, a)$.
--
--   **Formalization Note.** These are the input encodings used for every algorithmic statement; all codes are `Primcodable`, so Mathlib's `Computable` applies.
-- source:
--   Liu, Meng, From Block Orthogonality to Decidability in Complex-Weighted Counting CSP, arXiv:2608.14845 (PDF sha256 ad21e5d7…), p. F-1 (Theorem F.1.1), p. F-6 (§F.2.1 'standard exact representations'), p. F-27 (Theorem F.5.8)

import Mathlib
import Definitions.Def_BlockOrthoCSP_Decide_Instance

set_option autoImplicit false

namespace BlockOrthoCSP.Decide

/-! Exact input codes (the paper, p. F-6: "Input values have standard exact representations
specifying the chosen complex root", [Coh93, §4.2]). Codes are `Primcodable` data built from
`ℕ`, `ℤ`, lists and pairs, so `Computable` applies to maps between them. -/

/-- The rational `num / (den + 1)` coded by `(num, den)` (never a zero denominator). -/
def ratOf (p : ℤ × ℕ) : ℚ := p.1 / ((p.2 : ℚ) + 1)

/-- Exact code of an algebraic complex number: the integer coefficient list of a polynomial
(constant term first) and a closed rational box `[re_lo, re_hi] × [im_lo, im_hi]`. -/
abbrev AlgCode : Type := List ℤ × ((ℤ × ℕ) × (ℤ × ℕ)) × ((ℤ × ℕ) × (ℤ × ℕ))

/-- Evaluation of the coded integer polynomial at `z`. -/
def AlgCode.polyEval (c : AlgCode) (z : ℂ) : ℂ :=
  (c.1.mapIdx fun i a => (a : ℂ) * z ^ i).sum

/-- `z` is a root of the coded nonzero polynomial lying in the coded closed box. -/
def AlgCode.Denotes (c : AlgCode) (z : ℂ) : Prop :=
  (∃ a ∈ c.1, a ≠ 0) ∧ c.polyEval z = 0 ∧
    ((ratOf c.2.1.1 : ℚ) : ℝ) ≤ z.re ∧ z.re ≤ ((ratOf c.2.1.2 : ℚ) : ℝ) ∧
    ((ratOf c.2.2.1 : ℚ) : ℝ) ≤ z.im ∧ z.im ≤ ((ratOf c.2.2.2 : ℚ) : ℝ)

/-- A valid code isolates exactly one root of its nonzero polynomial. -/
def AlgCode.Valid (c : AlgCode) : Prop := ∃! z : ℂ, c.Denotes z

/-- The algebraic number a valid code denotes (an arbitrary root in the box otherwise, `0` if
there is none; only used on valid codes). -/
noncomputable def AlgCode.val (c : AlgCode) : ℂ :=
  haveI := Classical.propDecidable (∃ z : ℂ, c.Denotes z)
  if h : ∃ z : ℂ, c.Denotes z then h.choose else 0

/-- Code of one constraint function: its arity `r` and the list of its `q^r` value codes. -/
abbrev FnCode : Type := ℕ × List AlgCode

/-- Code of an input `(q, F)`: the domain size `q` and the list of the functions of `F`. -/
abbrev LangCode : Type := ℕ × List FnCode

/-- Position of `a ∈ D^r` in the lexicographic listing of `D^r` (first coordinate most
significant): `∑_i a_i q^{r−1−i}`. -/
def lexIndex (q : ℕ) {r : ℕ} (a : Fin r → Fin q) : ℕ :=
  ∑ i : Fin r, (a i : ℕ) * q ^ (r - 1 - (i : ℕ))

/-- Decoding of a function code: the value at `a` is the decoded entry at position
`lexIndex q a` (`0` if the list is too short; never on valid codes). -/
noncomputable def decodeFn (q : ℕ) (c : FnCode) : CFn q :=
  ⟨c.1, fun a => ((c.2[lexIndex q a]?).map AlgCode.val).getD 0⟩

/-- A valid function code: arity `r ≥ 1`, exactly `q^r` values, each a valid algebraic code. -/
def FnCode.Valid (q : ℕ) (c : FnCode) : Prop :=
  1 ≤ c.1 ∧ c.2.length = q ^ c.1 ∧ ∀ v ∈ c.2, AlgCode.Valid v

/-- A valid input code: `q ≥ 1` and every function code valid. -/
def LangCode.Valid (c : LangCode) : Prop :=
  1 ≤ c.1 ∧ ∀ f ∈ c.2, FnCode.Valid c.1 f

/-- The decoded finite set `F` (functions with the same arity and values are identified, as the
paper prescribes for list inputs, p. F-6). -/
noncomputable def decodeLang (c : LangCode) : Finset (CFn c.1) := by
  classical exact (c.2.map (decodeFn c.1)).toFinset

/-- Code of an instance with a prescribed number `t` of retained variables: the number `h` of
hidden variables and the list of constraints `(index of the function in the input list, scope)`,
scope entries being variable numbers `< t + h` (the first `t` are the retained ones). -/
abbrev InstCode : Type := ℕ × List (ℕ × List ℕ)

/-- Decoding of one constraint code against an input code, on `n` variables. -/
noncomputable def decodeConstraint (c : LangCode) (n : ℕ) (k : ℕ × List ℕ) :
    Option (Constraint c.1 n) :=
  match c.2[k.1]? with
  | none => none
  | some fc =>
    if h : k.2.length = fc.1 ∧ ∀ v ∈ k.2, v < n then
      some ⟨decodeFn c.1 fc, fun p =>
        ⟨k.2[(p : ℕ)]'(by rw [h.1]; exact p.2), h.2 _ (List.getElem_mem _)⟩⟩
    else none

/-- Decoding of an instance code with `t` retained variables (`none` if some constraint code is
ill-formed). -/
noncomputable def decodeInst (c : LangCode) (t : ℕ) (ic : InstCode) : Option (Inst c.1 t) :=
  (ic.2.mapM (decodeConstraint c (t + ic.1))).map fun cs => ⟨ic.1, cs⟩

/-- Decoding of a tuple `a ∈ D^k` given as a list of naturals. -/
def decodeTuple (q k : ℕ) (l : List ℕ) : Option (Fin k → Fin q) :=
  if h : l.length = k ∧ ∀ v ∈ l, v < q then
    some fun i => ⟨l[(i : ℕ)]'(by rw [h.1]; exact i.2), h.2 _ (List.getElem_mem _)⟩
  else none

/-- Code of a polynomial with algebraic coefficients: a list of monomials, each an exact
coefficient code and a list of (variable code, exponent) factors. -/
abbrev PolyCode (V : Type) : Type := List (AlgCode × List (V × ℕ))

/-- Decoding of a polynomial code, given a decoding `dv` of variable codes. -/
noncomputable def PolyCode.decode {V σ : Type} (dv : V → Option σ) (P : PolyCode V) :
    MvPolynomial σ ℂ :=
  (P.map fun m => MvPolynomial.C m.1.val *
    (m.2.map fun ve => (((dv ve.1).map MvPolynomial.X).getD 0) ^ ve.2).prod).sum

/-- A valid polynomial code: all coefficient codes valid and all variable codes decodable. -/
def PolyCode.Valid {V σ : Type} (dv : V → Option σ) (P : PolyCode V) : Prop :=
  ∀ m ∈ P, m.1.Valid ∧ ∀ ve ∈ m.2, (dv ve.1).isSome

/-- Decoding of the variable codes of Theorem F.5.8: `(false, a)` is `X_a`, `(true, a)` is
`Y_a`, `a ∈ D^k` given as a list (the `2q^k` independent variables). -/
def decodeXY (q k : ℕ) (v : Bool × List ℕ) : Option ((Fin k → Fin q) ⊕ (Fin k → Fin q)) :=
  (decodeTuple q k v.2).map fun a => if v.1 then Sum.inr a else Sum.inl a

end BlockOrthoCSP.Decide


