-- Prove2me | Definitions.Def_CSPIdealMem_Encoding
-- name    : CSPIdealMem_Encoding
-- status  : Definition
-- author  : @iris
-- created : 2026-11-10T08:29:33.404225+00:00
-- url     : https://prove2.me/theorems/c2c0efa1-deb9-4385-b822-19e6e9701820
-- title:
--   Binary encodings, the languages $\mathrm{IMP}_d(\Gamma)$ and $\mathrm{CSP}(\Lambda)$, output specifications and codes of $(D,\Gamma)$
-- statement:
--   **Inputs.** The input of $\mathrm{IMP}_d(\Gamma)$ is an instance $P$ and a polynomial $f_0$ written as a sum of monomials with rational coefficients. A natural number is written in self-delimiting binary, an integer as a sign and its absolute value, a rational as its reduced numerator and denominator, and lists are self-delimiting. An instance is coded by its number $n$ of variables **in unary** followed by its constraints (relation position, scope indices); a polynomial by its list of terms $(q,[(v_1,e_1),\dots])$ meaning $q\,x_{v_1}^{e_1}\cdots$.
--
--   **Languages.** $\mathrm{IMP}_d(\Gamma)$ is the set of codes of pairs $(P,f_0)$ such that the represented polynomial has total degree at most $d$ and $f_0\in I(P)$. $\mathrm{CSP}(\Lambda)$ is the set of codes of satisfiable $\Lambda$-instances. Strings that code nothing belong to neither language.
--
--   **Outputs.** A string codes a basis of $W_d(P)$ if it is the code of a list of coefficient vectors that is linearly independent and spans $W_d(P)$; a basis of $I(P)\cap\mathbb Q[X]_{\le d}$ if it codes a linearly independent list of polynomials spanning that space; and a spanning set of solutions if it codes a list of at most $\binom{n+d}{d}$ solutions of $P$ whose evaluation vectors span $W_d(P)$.
--
--   **Codes of $(D,\Gamma)$.** A code lists the domain as (numerator, denominator) pairs and each relation as its arity and its tuples. It represents $(D,\Gamma)$ if the denominators are positive, the decoded domain list is exactly $D$ without repetitions, and the listed relations correspond bijectively to those of $\Gamma$ with matching arities and tuple sets.
--
--   These are the encodings in which every complexity statement of the mission is made.
--
--   **Formalization Note** All encodings are injective and prefix-free (proved in the mission's sanity checks) and decodable in polynomial time. The number of variables is unary because the paper's input lists every variable explicitly.
-- source:
--   Rafiey–Soleymani–Jaillet, A Dichotomy Theorem for CSP-Based Ideal Membership, STOC 2027 submission manuscript (held version, sha256 c7140009133170c893c7b31cf2279f3dda0264d867825a8beb7cc6963f50f109), input format, p.3 (PDF 3); outputs of Theorem 1.2, p.5 (PDF 5) and Theorem 1.3, p.30 (PDF 30); "decidable from D, Γ, d", p.5 and p.37 (PDF 37)

import Mathlib
import Definitions.Def_CSPIdealMem_EvalSpace

namespace CSPIdealMem

/-! # Binary encodings, the languages `IMP_d(Γ)` and `CSP(Λ)`, output specifications, and codes
of a finite rational language

Rafiey–Soleymani–Jaillet, *A Dichotomy Theorem for CSP-Based Ideal Membership*, STOC 2027
submission manuscript (held version, sha256 c7140009…f50f109): input format of `IMP_d(Γ)` and
`CSP(Γ)`, p.3 (PDF 3) ("The input explicitly lists all variables and constraints and represents
`f₀` as a sum of monomials with binary-encoded rational coefficients. Running time is measured in
this full binary input length."); the three outputs of Theorem 1.2 case 1, p.5 (PDF 5) and
Theorem 1.3, p.30 (PDF 30); "decidable from `D, Γ, d`", p.5 and p.37 (PDF 37).

**Formalization Note.** Strings are `List Bool`. A natural number is written in binary,
self-delimiting: each binary digit `b` (least significant first) becomes the block `0b`, and the
block `10` ends the number. An integer is a sign bit followed by its absolute value; a rational is
its reduced numerator and denominator. Lists are self-delimiting: each element is preceded by
`1` and the list ends with `0`. The number `n` of variables is written in **unary** (the paper's
input lists all variables explicitly), relation names by their position under a fixed bijection
`Γ.ι ≃ Fin |Γ.ι|`, variable indices and exponents in binary. A query polynomial is a list of terms
`(q, [(v₁, e₁), …])` meaning `q · x_{v₁}^{e₁} ⋯`; repeated monomials and zero coefficients are
allowed, and the degree bound is a condition on the represented polynomial. Strings that encode
no instance (with a polynomial of degree `≤ d`) are not members of `IMP_d(Γ)`. -/

open Classical

/-- Self-delimiting binary code of a natural number: digits of `k` in base 2 (least significant
first, none for `0`), each as the block `[false, b]`, then the end marker `[true, false]`. -/
def encodeNat (k : ℕ) : List Bool :=
  ((Nat.digits 2 k).flatMap fun b => [false, decide (b = 1)]) ++ [true, false]

/-- Binary code of an integer: its sign bit, then the code of its absolute value. -/
def encodeInt (z : ℤ) : List Bool :=
  decide (z < 0) :: encodeNat z.natAbs

/-- Binary code of a rational number: the codes of its reduced numerator and denominator. -/
def encodeRat (q : ℚ) : List Bool :=
  encodeInt q.num ++ encodeNat q.den

/-- Self-delimiting code of a list: each element's code preceded by `true`, then `false`. -/
def encodeList {β : Type} (f : β → List Bool) (l : List β) : List Bool :=
  (l.flatMap fun x => true :: f x) ++ [false]

/-- Unary code of a natural number: `n` ones and a zero. -/
def encodeUnary (n : ℕ) : List Bool :=
  List.replicate n true ++ [false]

variable {α : Type}

/-- The position of a relation name under a fixed bijection `Γ.ι ≃ Fin |Γ.ι|`. -/
noncomputable def relIndex (Γ : ConstraintLanguage α) (i : Γ.ι) : ℕ :=
  (Fintype.equivFin Γ.ι i : ℕ)

/-- Binary code of a constraint `⟨s, R_i⟩`: the relation's position, then the list of the scope's
variable indices. -/
noncomputable def encodeConstraint {Γ : ConstraintLanguage α} {n : ℕ}
    (c : Σ i : Γ.ι, Fin (Γ.arity i) → Fin n) : List Bool :=
  encodeNat (relIndex Γ c.1) ++ encodeList encodeNat (List.ofFn fun j => (c.2 j : ℕ))

/-- Binary code of a CSP instance (p.3): the number of variables in unary, then the list of its
constraints. -/
noncomputable def encodeInstance {Γ : ConstraintLanguage α} (P : Instance Γ) : List Bool :=
  encodeUnary P.n ++ encodeList encodeConstraint P.cons

/-- A query polynomial in the variables `Fin n` written as a sum of monomials (p.3): a list of
terms, each a rational coefficient and a monomial given as a list of (variable, exponent) pairs. -/
abbrev PolyCode (n : ℕ) : Type := List (ℚ × List (Fin n × ℕ))

/-- The polynomial `∑ q · ∏ x_v^e` represented by a `PolyCode`. -/
noncomputable def toPoly {n : ℕ} (c : PolyCode n) : MvPolynomial (Fin n) ℚ :=
  (c.map fun t => MvPolynomial.C t.1 * (t.2.map fun ve => MvPolynomial.X ve.1 ^ ve.2).prod).sum

/-- Binary code of a `PolyCode`: each term as its coefficient (binary rational) followed by the
list of its (variable, exponent) pairs, both in binary. -/
def encodePoly {n : ℕ} (c : PolyCode n) : List Bool :=
  encodeList (fun t => encodeRat t.1 ++
    encodeList (fun ve : Fin n × ℕ => encodeNat ve.1 ++ encodeNat ve.2) t.2) c

/-- Binary code of an `IMP_d(Γ)` input `(P, f₀)`: the instance followed by the polynomial. -/
noncomputable def encodeIMP {Γ : ConstraintLanguage α} (P : Instance Γ) (c : PolyCode P.n) :
    List Bool :=
  encodeInstance P ++ encodePoly c

variable {D : Finset ℚ}

/-- `IMP_d(Γ)` (p.3) as a language: the codes of pairs `(P, f₀)` with `f₀` of total degree at most
`d` and `f₀ ∈ I(P)`. -/
noncomputable def IMPLang (Γ : ConstraintLanguage D) (d : ℕ) : Language Bool :=
  {w | ∃ (P : Instance Γ) (c : PolyCode P.n), w = encodeIMP P c ∧
    (toPoly c).totalDegree ≤ d ∧ toPoly c ∈ idealOf P}

/-- `CSP(Λ)` (p.3) as a language: the codes of satisfiable instances. -/
noncomputable def CSPLang (Λ : ConstraintLanguage α) : Language Bool :=
  {w | ∃ P : Instance Λ, w = encodeInstance P ∧ (Sol P).Nonempty}

/-- The vector in `ℚ^{M_d(X)}` read off a `PolyCode`: its coordinate at a monomial `m` of degree
`≤ d` is the coefficient of `m` in the represented polynomial. -/
noncomputable def toVec {n : ℕ} (d : ℕ) (c : PolyCode n) : Mon (Fin n) d → ℚ :=
  fun m => (toPoly c).coeff m.1

/-- Binary code of a list of `PolyCode`s (a list of vectors or of polynomials). -/
def encodePolyList {n : ℕ} (cs : List (PolyCode n)) : List Bool :=
  encodeList encodePoly cs

/-- Binary code of an assignment `φ : Fin n → D`: the list of its values' rational labels. -/
def encodeAssignment {n : ℕ} (φ : Fin n → D) : List Bool :=
  encodeList (fun x => encodeRat ((φ x : D) : ℚ)) (List.finRange n)

/-- Binary code of a list of assignments. -/
def encodeAssignments {n : ℕ} (φs : List (Fin n → D)) : List Bool :=
  encodeList encodeAssignment φs

/-- The string `s` encodes a `ℚ`-basis of `W_d(P)` (Theorem 1.2, p.5): a list of vectors, given
as coefficient lists, that is linearly independent and spans `W_d(P)`. -/
noncomputable def OutputsWBasis {Γ : ConstraintLanguage D} (d : ℕ) (P : Instance Γ)
    (s : List Bool) : Prop :=
  ∃ cs : List (PolyCode P.n), s = encodePolyList cs ∧
    LinearIndependent ℚ (fun i : Fin cs.length => toVec d (cs.get i)) ∧
    Submodule.span ℚ (Set.range fun i : Fin cs.length => toVec d (cs.get i)) = W P d

/-- The string `s` encodes a `ℚ`-basis of `I(P) ∩ ℚ[X]_{≤d}` (Theorem 1.2, p.5): a linearly
independent list of polynomials spanning it. -/
noncomputable def OutputsIdealBasis {Γ : ConstraintLanguage D} (d : ℕ) (P : Instance Γ)
    (s : List Bool) : Prop :=
  ∃ cs : List (PolyCode P.n), s = encodePolyList cs ∧
    LinearIndependent ℚ (fun i : Fin cs.length => toPoly (cs.get i)) ∧
    Submodule.span ℚ (Set.range fun i : Fin cs.length => toPoly (cs.get i)) = idealDeg P d

/-- The string `s` encodes at most `C(n+d, d)` actual solutions of `P` whose evaluation vectors
span `W_d(P)` (Theorem 1.2, p.5). -/
noncomputable def OutputsSpanningSolutions {Γ : ConstraintLanguage D} (d : ℕ) (P : Instance Γ)
    (s : List Bool) : Prop :=
  ∃ φs : List (Fin P.n → D), s = encodeAssignments φs ∧ φs.length ≤ (P.n + d).choose d ∧
    (∀ φ ∈ φs, φ ∈ Sol P) ∧
    Submodule.span ℚ (Set.range fun i : Fin φs.length => assignVec d (φs.get i)) = W P d

/-- A code of a finite rational domain and a finite language on it: the domain as a list of
(numerator, denominator) pairs, and each relation as its arity and its list of tuples, each tuple a
list of (numerator, denominator) pairs. -/
abbrev LangCode : Type := List (ℤ × ℕ) × List (ℕ × List (List (ℤ × ℕ)))

/-- The rational number `z / k` coded by the pair `(z, k)`. -/
def ratOfCode (p : ℤ × ℕ) : ℚ := (p.1 : ℚ) / (p.2 : ℚ)

/-- `c` is a code of `(D, Γ)`: all denominators are positive; the decoded domain list has no
repetitions and consists exactly of the elements of `D`; and there is a bijection between the
relation names of `Γ` and the listed relations matching each arity and each relation's set of
tuples (a tuple `r` is in `R_i` iff its list of labels is among the decoded listed tuples). -/
def Represents (c : LangCode) (Γ : ConstraintLanguage D) : Prop :=
  (∀ p ∈ c.1, 0 < p.2) ∧ (c.1.map ratOfCode).Nodup ∧ (∀ q : ℚ, q ∈ c.1.map ratOfCode ↔ q ∈ D) ∧
  (∀ r ∈ c.2, ∀ tup ∈ r.2, ∀ p ∈ tup, 0 < p.2) ∧
  ∃ e : Γ.ι ≃ Fin c.2.length, ∀ i : Γ.ι, (c.2.get (e i)).1 = Γ.arity i ∧
    ∀ r : Fin (Γ.arity i) → D,
      r ∈ Γ.rel i ↔ List.ofFn (fun j => ((r j : D) : ℚ)) ∈ (c.2.get (e i)).2.map (List.map ratOfCode)

end CSPIdealMem


