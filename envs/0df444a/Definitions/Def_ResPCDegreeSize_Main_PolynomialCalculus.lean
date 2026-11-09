-- Prove2me | Definitions.Def_ResPCDegreeSize_Main_PolynomialCalculus
-- name    : ResPCDegreeSize_Main_PolynomialCalculus
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-08T08:19:20.399546+00:00
-- url     : https://prove2.me/theorems/db60f428-0e18-4a9c-b724-8ed69bc9f501
-- title:
--   Polynomial calculus: CNF encodings, the degree-$D$ closure $\mathcal C_D(Q)$, multilinearization and the polynomial-clause encoding
-- statement:
--   Fix a prime $p$ and Boolean variables $x_1,\dots,x_n$, and write $\mathbb F_p[x]=\mathbb F_p[x_1,\dots,x_n]$ and $V_k=\mathbb F_p[x]_{\le k}$ for the polynomials of total degree at most $k$.
--
--   A literal is $x_i$ or $\neg x_i$, a clause $J$ is a finite set of literals and a CNF $F$ is a finite set of clauses. The empty clause and tautological clauses are allowed. The width $w(F)$ is the largest clause size, $0$ for the empty CNF, and $F$ is unsatisfiable when no assignment in $\{0,1\}^n$ satisfies all its clauses.
--
--   The literal polynomial of $x_i$ is $x_i$ and that of $\neg x_i$ is $1-x_i$. The falsity polynomial of a clause is
--   $$Q_J=\prod_{l\in J}(1-l),$$
--   and the encoding of $F$ is
--   $$\mathcal Q(F)=\mathrm{Bool}\cup\{Q_J:J\in F\},\qquad \mathrm{Bool}=\{x_i^2-x_i:i\in[n]\}.$$
--
--   Write $Q\vdash_D f$ when $f$ has a degree-$D$ polynomial calculus derivation from $Q$: every line has total degree at most $D$ and is an element of $Q$, a linear combination $\alpha g+\beta h$ of earlier lines with $\alpha,\beta\in\mathbb F_p$, or a product $x_ig$ of an earlier line with a variable. The set $\mathcal C_D(Q)=\{f:Q\vdash_D f\}$ is a linear subspace of $V_D$. This is not ideal membership: the degree bound applies to every intermediate line.
--
--   The multilinearization $\mathrm{ML}(f)$ replaces each positive exponent of each monomial of $f$ by $1$ and adds the coefficients; a polynomial is multilinear when all exponents of all its monomials are at most $1$.
--
--   A polynomial equation system (Remark 1.2) is $F=\{F_1,\dots,F_m\}$ with $F_i=\bigvee_{j=1}^{w_i}(H_{i,j}=0)$. Its encoding is
--   $$\mathcal Q(F)=\mathrm{Bool}\cup\{Q_{F_1},\dots,Q_{F_m}\},\qquad Q_{F_i}=\mathrm{ML}\Bigl(\prod_{j=1}^{w_i}H_{i,j}\Bigr),$$
--   and $F$ is unsatisfiable when no point of $\{0,1\}^n$ satisfies every $F_i$.
--
--   These objects are reusable for any work on polynomial calculus over a prime field.
--
--   **Formalization Note** Variables are indexed by `Fin n`. `PCDerivable` is an inductive predicate with one constructor per rule; a derivation tree flattens to the source's sequence. A constructor makes $0$ derivable, as "linear subspace" requires. `CD` is the corresponding submodule of the whole polynomial ring, contained in $V_D$. `ML` is constructive, not chosen by uniqueness.
-- source:
--   Pang, A Degree–Size Relation for Resolution over Polynomials, 2026 preprint (STOC 2027 submission #128; SHA-256 d026926040f9df67b9f5a3212fe878d8a10b50dd70b04f14b63b62a9dcb9d32f), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/128.pdf, Section 1, eq. (1) and Remark 1.2, eq. (3), PDF p. 2 (printed p. 1); Section 2, Fact 2.2, PDF p. 4 (printed p. 3)

import Mathlib

namespace ResPCDegreeSize.Main

open MvPolynomial

noncomputable section

/-- `F_p[x₁,…,xₙ]`. -/
abbrev Poly (n p : ℕ) := MvPolynomial (Fin n) (ZMod p)

/-- `V_k = F_p[x]_{≤k}`: the polynomials of total degree at most `k`. -/
abbrev V (n p k : ℕ) : Submodule (ZMod p) (Poly n p) :=
  MvPolynomial.restrictTotalDegree (Fin n) (ZMod p) k

/-- A literal: the variable `var`, positive (`xᵢ`) when `pos = true`, negated (`¬xᵢ`) otherwise. -/
structure Literal (n : ℕ) where
  var : Fin n
  pos : Bool
  deriving DecidableEq

/-- A clause is a finite set of literals; the empty clause and tautologies are allowed. -/
abbrev Clause (n : ℕ) := Finset (Literal n)

/-- A CNF is a finite set of clauses. -/
abbrev CNF (n : ℕ) := Finset (Clause n)

/-- The width `w(F)`: the largest clause size, `0` for the empty CNF. -/
def width {n : ℕ} (F : CNF n) : ℕ := F.sup Finset.card

/-- The assignment `a` satisfies the clause `J`: some literal of `J` is true under `a`. -/
def SatisfiesClause {n : ℕ} (a : Fin n → Bool) (J : Clause n) : Prop :=
  ∃ l ∈ J, a l.var = l.pos

/-- `F` is unsatisfiable: no assignment in `{0,1}ⁿ` satisfies every clause. -/
def Unsatisfiable {n : ℕ} (F : CNF n) : Prop :=
  ¬ ∃ a : Fin n → Bool, ∀ J ∈ F, SatisfiesClause a J

/-- The literal polynomial: `xᵢ` for `xᵢ`, and `1 - xᵢ` for `¬xᵢ`. -/
def litPoly {n : ℕ} (p : ℕ) (l : Literal n) : Poly n p :=
  if l.pos then X l.var else 1 - X l.var

/-- The falsity polynomial `Q_J = ∏_{l ∈ J} (1 - l)`. -/
def falsityPoly {n : ℕ} (p : ℕ) (J : Clause n) : Poly n p :=
  ∏ l ∈ J, (1 - litPoly p l)

/-- `Bool = {xᵢ² - xᵢ : i ∈ [n]}`. -/
def boolAxioms (n p : ℕ) : Set (Poly n p) :=
  Set.range fun i : Fin n => X i ^ 2 - X i

/-- The encoding `Q(F) = Bool ∪ {Q_J : J ∈ F}`. -/
def encoding {n : ℕ} (p : ℕ) (F : CNF n) : Set (Poly n p) :=
  boolAxioms n p ∪ {q | ∃ J ∈ F, q = falsityPoly p J}

/-- `Q ⊢_D f`: `f` has a degree-`D` polynomial calculus derivation from `Q`. Every line has total
degree at most `D`: an axiom of `Q` of degree at most `D`, a linear combination of earlier lines,
or the product of an earlier line with a variable when that product has degree at most `D`.
The zero polynomial is always derivable, as the source's "linear subspace" requires. -/
inductive PCDerivable {n p : ℕ} (Q : Set (Poly n p)) (D : ℕ) : Poly n p → Prop
  | ax {f : Poly n p} (hf : f ∈ Q) (hd : f.totalDegree ≤ D) : PCDerivable Q D f
  | zero : PCDerivable Q D 0
  | lin {g h : Poly n p} (α β : ZMod p) (hg : PCDerivable Q D g) (hh : PCDerivable Q D h) :
      PCDerivable Q D (C α * g + C β * h)
  | mulX {g : Poly n p} (i : Fin n) (hg : PCDerivable Q D g)
      (hd : (X i * g).totalDegree ≤ D) : PCDerivable Q D (X i * g)

/-- `C_D(Q) = {f : Q ⊢_D f}` as an `F_p`-submodule of `F_p[x]`. -/
def CD {n p : ℕ} (Q : Set (Poly n p)) (D : ℕ) : Submodule (ZMod p) (Poly n p) where
  carrier := {f | PCDerivable Q D f}
  zero_mem' := PCDerivable.zero
  add_mem' := by
    intro a b ha hb
    have h := PCDerivable.lin (1 : ZMod p) 1 ha hb
    simpa using h
  smul_mem' := by
    intro c f hf
    have h := PCDerivable.lin c 0 hf hf
    simpa [MvPolynomial.smul_eq_C_mul] using h

/-- The exponent vector with every positive exponent replaced by `1`. -/
def squash {n : ℕ} (m : Fin n →₀ ℕ) : Fin n →₀ ℕ :=
  m.mapRange (fun e => min e 1) (by simp)

/-- `ML(f)`: reduce every positive exponent of every monomial of `f` to `1`, adding coefficients. -/
def ML {n p : ℕ} (f : Poly n p) : Poly n p :=
  ∑ m ∈ f.support, monomial (squash m) (coeff m f)

/-- `f` is multilinear: every monomial of `f` has all exponents at most `1`. -/
def IsMultilinear {n p : ℕ} (f : Poly n p) : Prop :=
  ∀ m ∈ f.support, ∀ i, m i ≤ 1

/-- The point of `F_pⁿ` with `0/1` coordinates given by a Boolean assignment. -/
def cubePoint {n : ℕ} (p : ℕ) (a : Fin n → Bool) : Fin n → ZMod p :=
  fun i => if a i then 1 else 0

/-- Remark 1.2, eq. (3): the encoding of a polynomial equation system `F = {F₁,…,F_m}` with
`Fᵢ = ⋁_{j ≤ wᵢ} (H i j = 0)`, namely `Q(F) = Bool ∪ {Q_{F₁},…,Q_{F_m}}`,
`Q_{Fᵢ} = ML(∏_j H i j)`. -/
def polyEncoding {n p m : ℕ} {w : Fin m → ℕ} (H : ∀ i, Fin (w i) → Poly n p) : Set (Poly n p) :=
  boolAxioms n p ∪ Set.range fun i => ML (∏ j, H i j)

/-- The system `F = {F₁,…,F_m}` is unsatisfiable: no point of `{0,1}ⁿ` satisfies every
`Fᵢ = ⋁_j (H i j = 0)`. -/
def PolyUnsatisfiable {n p m : ℕ} {w : Fin m → ℕ} (H : ∀ i, Fin (w i) → Poly n p) : Prop :=
  ¬ ∃ a : Fin n → Bool, ∀ i, ∃ j, eval (cubePoint p a) (H i j) = 0

end

end ResPCDegreeSize.Main


