-- Prove2me | Definitions.Def_IntQuotHNP_Supplement_ECHNP
-- name    : IntQuotHNP_Supplement_ECHNP
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T07:04:52.180243+00:00
-- url     : https://prove2.me/theorems/a1a0be4b-d39d-4797-9564-3665e04787c6
-- title:
--   Definition 5.1 and Lemma 5.3 — EC-HNP inputs, constraints, admissibility (11), the lattice polynomials, sampling, $\Delta_N$, $\rho_N$
-- statement:
--   Let $p>3$ be prime and $E/\mathbb F_p$ the nonsingular curve $w^2=z^3+a_Ez+b_E$, with group law $+$ and identity $\mathcal O$; for a finite point $\pi_1(z,w)=z$ and $\pi_2(z,w)=w$. A **public EC-HNP input** consists of a generator $R_0$ of a subgroup $G$ of known order $M$, integers $N\ge5$ and $1\le X<p$, queries $Q_1,\dots,Q_N\in G$, and for each $i$ either a **finite observation** $v_i\in\mathbb Z$ or an **infinity observation**; optionally leading-bit intervals $[v_i,u_i]$ with at most $X$ canonical values; and the description of a promised restriction on the hidden point, decided by a polynomial-time **verifier**.
--
--   A point $y\in E(\mathbb F_p)$ **satisfies the input constraints** when for every $i$: an infinity observation gives $y+Q_i=\mathcal O$; a finite observation gives $y+Q_i\ne\mathcal O$,
--   $$
--   [\pi_1(y+Q_i)-v_i]_p\in\{0,\dots,X-1\},
--   $$
--   and, with leading bits, $v_i\le\pi_1(y+Q_i)\le u_i$; and the verifier accepts $y$. The input is **promised** when some point satisfies them, and **admissible** when
--   $$
--   Q_i\ne\mathcal O,\qquad Q_j-Q_i\notin E[2]\quad(i\ne j). \tag{11}
--   $$
--
--   For a finite input put $a_{ij}=\pi_1(Q_j-Q_i)$, $b_{ij}=\pi_2(Q_j-Q_i)$ and $F_{ij}=z_iz_j-a_{ij}(z_i+z_j)$. For $i<j<N$, $\kappa_{ij}$ is the value of $F_{ij}-\tfrac{b_{ij}}{b_{iN}}F_{iN}+\tfrac{b_{ij}}{b_{jN}}F_{jN}$ at $z_h=\pi_1(Q_h)$, and $P_{ij}$ is obtained by subtracting $\kappa_{ij}$, lifting the coefficients to canonical integers and substituting $z_h=v_h+x_h$. With $px_hx_N$ ($h<N$) and $px_h$ ($h\in[N]$) these are the $N(N+1)/2$ polynomials of Lemma 5.3.
--
--   In the **sampling model** a point $y^*$ is fixed, the queries $Q_i=s_iR_0$ are independent and uniform in $G$, tuples failing (11) are rejected, infinity observations occur exactly where $y^*+Q_i=\mathcal O$, and an **approximation rule** gives the $v_i$ (and intervals) as any function of the accepted tuple satisfying the constraints at $y^*$. Finally $\Delta_N=X^{5N-6}/M^{N-2}$ and $\rho_N=(N-2)/(5N-6)$.
--
--   **Formalization Note** The curve is Mathlib's affine Weierstrass curve over `ZMod p` with $a_1=a_2=a_3=0$; nonsingularity is the condition $4a_E^3+27b_E^2\ne0$ of the promise. Because $Q_j-Q_i\in E(\mathbb F_p)$, membership in $E[2]$ (over an algebraic closure) is $2(Q_j-Q_i)=\mathcal O$ in $E(\mathbb F_p)$. The restriction is any property decided by a deterministic verifier machine run on the input code followed by the point's code; points are coded by their canonical coordinates, with a separate code for $\mathcal O$. The paper's index $i\in[N]$ is the Lean index $i-1$, and its last index $N$ is Lean `N - 1`.
-- source:
--   Kang, Lee, Provable Recovery from Integer Quotients: Improved Bounds for Nonlinear Hidden Number Problems, STOC 2027 submission (manuscript sha256 605f9dd3…), §5, p.29 (PDF p.30); Definition 5.1, pp.29–30 (PDF pp.30–31); Theorem 5.2, p.30 (PDF p.31); Lemma 5.3, pp.30–31 (PDF pp.31–32); §5.1, p.31 (PDF p.32)

import Mathlib
import Definitions.Def_MatchingFPRAS
import Definitions.Def_IntQuotHNP_Supplement_LasVegas
import Definitions.Def_IntQuotHNP_Supplement_CoeffMap
import Definitions.Def_IntQuotHNP_Supplement_Recovery

namespace IntQuotHNP

namespace Supplement

open OAI.MatchingFPRAS

variable {p : ℕ} [Fact p.Prime]

/-- **The short Weierstrass curve `w² = z³ + a_E z + b_E` over `𝔽_p`** (§5, p.29).
Kang, Lee, *Provable Recovery from Integer Quotients: Improved Bounds for Nonlinear Hidden Number
Problems*, STOC 2027 submission (manuscript sha256 605f9dd3…), §5, p.29 (PDF p.30): "Let p > 3 be
prime and let E/𝔽_p be the nonsingular curve w² = ϕ(z) = z³ + a_E z + b_E. Here a_E, b_E ∈ ℤ_p. …
E(𝔽_p) consists of the point O and the pairs (z, w) ∈ ℤ_p² satisfying the curve equation modulo p.
Write + for its group operation, with identity O".

**Formalization Note.** Mathlib's affine Weierstrass curve over `ZMod p` with `a₁ = a₂ = a₃ = 0`,
`a₄ = a_E`, `a₆ = b_E`; its type of points `Point` (with `0 = O`) carries the chord-and-tangent
group law. Nonsingularity (`4a_E³ + 27b_E² ≠ 0`) is a clause of `ECPromised`. -/
def ecCurve (aE bE : ZMod p) : WeierstrassCurve.Affine (ZMod p) :=
  ({ a₁ := 0, a₂ := 0, a₃ := 0, a₄ := aE, a₆ := bE } : WeierstrassCurve (ZMod p)).toAffine

/-- **The first coordinate `π₁`** of a finite point (`π₁(z, w) = z`); `π₁(O)` is never used. -/
def pi1 {W : WeierstrassCurve.Affine (ZMod p)} : W.Point → ZMod p
  | .zero => 0
  | .some x _ _ => x

/-- **The second coordinate `π₂`** of a finite point (`π₂(z, w) = w`); `π₂(O)` is never used. -/
def pi2 {W : WeierstrassCurve.Affine (ZMod p)} : W.Point → ZMod p
  | .zero => 0
  | .some _ y _ => y

/-- **The code of a point** (§5.1, p.31: "Encode finite points by their canonical coordinates and
use a separate encoding for O"): `O ↦ 4`; `(z, w) ↦ 5`, then the canonical residues of `z` and `w`
written with `encodeNat`. -/
def pointCode {W : WeierstrassCurve.Affine (ZMod p)} : W.Point → List Symbol
  | .zero => [4]
  | .some x y _ => [5] ++ encodeNat x.val ++ encodeNat y.val

/-- **The canonical code of a finite set of points**: the point codes in increasing lexicographic
order, concatenated. Point codes are self-delimiting, so the code determines the set. -/
def encodePointSet {W : WeierstrassCurve.Affine (ZMod p)} (s : Finset W.Point) : List Symbol :=
  ((s.image pointCode).sort (· ≤ ·)).flatten

/-- **A public EC-HNP input** (Definition 5.1).
Kang, Lee, STOC 2027 submission (manuscript sha256 605f9dd3…), Definition 5.1, p.29 (PDF p.30):
"The public parameters are E/𝔽_p, a subgroup G = ⟨R₀⟩ of known order M, and integers N ≥ 5 and
1 ≤ X < p. The input consists of queries Q₁, . . . , Q_N ∈ G and, for each index i, either a finite
observation with an integer v_i or an infinity observation. … For leading-bit observations, the
input also specifies the integer interval determined by the revealed bits. It has left endpoint
v_i … Any promised subgroup or coset restriction on y∗ is supplied with a polynomial-time verifier
and is part of the input constraints."

The record holds the curve coefficients, the generator `R₀`, its order `M`, `N`, `X`, the queries,
for each index `obs i = some v_i` (finite observation) or `none` (infinity observation), optional
right endpoints `u_i` of the leading-bit intervals `[v_i, u_i]`, and the description `restr` of the
promised restriction (read by the verifier).

**Formalization Note.** The prime `p` is a parameter of the type. The paper's index `i ∈ [N]` is
the Lean index `i − 1 ∈ Fin N`. Which records are genuine inputs is `ECPromised`. -/
structure ECInput (p : ℕ) [Fact p.Prime] where
  /-- the coefficient `a_E` -/
  aE : ZMod p
  /-- the coefficient `b_E` -/
  bE : ZMod p
  /-- the generator `R₀` of `G` -/
  R0 : (ecCurve aE bE).Point
  /-- the public order `M` of `R₀` -/
  M : ℕ
  /-- the number `N` of queries -/
  N : ℕ
  /-- the error bound `X` -/
  X : ℕ
  /-- the queries `Q₁, …, Q_N` -/
  Q : Fin N → (ecCurve aE bE).Point
  /-- the observations: `some v_i` (finite) or `none` (infinity) -/
  obs : Fin N → Option ℤ
  /-- optional right endpoints `u_i` of the leading-bit intervals `[v_i, u_i]` -/
  ub : Option (Fin N → ℤ)
  /-- the description of the promised restriction on `y∗` -/
  restr : List Bool

/-- **The tape code of an EC-HNP input**: `p`, `a_E`, `b_E`, `R₀`, `M`, `N`, `X`, then for each
index the query and its observation (`6` for infinity, `encodeInt v_i` for a finite one), then the
interval endpoints (`6` if none, else `7` and the `u_i`), then the restriction description. -/
def ecEncodeInput (I : ECInput p) : List Symbol :=
  encodeNat p ++ encodeNat I.aE.val ++ encodeNat I.bE.val ++ pointCode I.R0 ++ encodeNat I.M ++
    encodeNat I.N ++ encodeNat I.X ++
    (List.ofFn fun i => pointCode (I.Q i) ++
      match I.obs i with
      | none => [6]
      | some v => encodeInt v).flatten ++
    (match I.ub with
      | none => [6]
      | some u => [7] ++ (List.ofFn fun i => encodeInt (u i)).flatten) ++
    encodeBits I.restr

/-- **A polynomial-time verifier** for restrictions: a deterministic machine that halts on every
word `w` within `C(1 + |w|)^K` ticks with `[2]` (accept) or `[1]` (reject) on the tape.
Kang, Lee, STOC 2027 submission (manuscript sha256 605f9dd3…), Definition 5.1, p.29 (PDF p.30):
"Any promised subgroup or coset restriction on y∗ is supplied with a polynomial-time verifier". -/
def IsVerifier (V : MTMachine) (C : ℝ) (K : ℕ) : Prop :=
  Deterministic V ∧ ∀ w : List Symbol, ∃ (b : Bool) (t : ℕ),
    (t : ℝ) ≤ C * (1 + w.length) ^ K ∧ RunsWithin V w [if b then 2 else 1] t

/-- **A point passes the promised restriction**: the verifier, run on the input code followed by
the point's code, accepts. -/
def PassesRestr (V : MTMachine) (I : ECInput p) (y : (ecCurve I.aE I.bE).Point) : Prop :=
  ∃ t, RunsWithin V (ecEncodeInput I ++ pointCode y) [2] t

/-- **A point satisfies the input constraints** (Definition 5.1, (10)).
Kang, Lee, STOC 2027 submission (manuscript sha256 605f9dd3…), Definition 5.1, p.29 (PDF p.30):
"For a finite observation, y∗ + Q_i ≠ O and z∗_i = π₁(y∗ + Q_i) ≡ v_i + x∗_i (mod p),
x∗_i ∈ {0, . . . , X − 1}. (10) An infinity observation is supplied exactly when y∗ + Q_i = O. …
For leading-bit observations, the input also specifies the integer interval determined by the
revealed bits. It has left endpoint v_i, contains at most X canonical values, and contains z∗_i.";
§5.1, p.31: "[ẑ_i − v_i]_p ∈ B_i (i ∈ [N]). For leading bits, also require ẑ_i to lie in its
original integer interval. Finally, apply the verifier for any promised restriction."

For every index: an infinity observation forces `y + Q_i = O`; a finite observation `v_i` forces
`y + Q_i ≠ O`, `[π₁(y + Q_i) − v_i]_p ∈ {0, …, X − 1}` and, with leading bits,
`v_i ≤ π₁(y + Q_i) ≤ u_i` as integers; and `y` passes the restriction verifier.

**Formalization Note.** `π₁(y + Q_i)` is its canonical residue in `{0, …, p − 1}`; the congruence
(10) is `(π₁ − v_i) mod p < X` with the nonnegative integer remainder, `v_i` any integer. -/
def ECSatisfies (V : MTMachine) (I : ECInput p) (y : (ecCurve I.aE I.bE).Point) : Prop :=
  (∀ i, match I.obs i with
    | none => y + I.Q i = 0
    | some v => y + I.Q i ≠ 0 ∧ (((pi1 (y + I.Q i)).val : ℤ) - v) % (p : ℤ) < I.X ∧
        ∀ u, I.ub = some u → v ≤ ((pi1 (y + I.Q i)).val : ℤ) ∧
          ((pi1 (y + I.Q i)).val : ℤ) ≤ u i) ∧
  PassesRestr V I y

open Classical in
/-- The number of canonical values `z ∈ {0, …, p − 1}` in the integer interval `[v, u]`. -/
noncomputable def canonicalCount (p : ℕ) (v u : ℤ) : ℕ :=
  ((Finset.range p).filter fun z => v ≤ (z : ℤ) ∧ (z : ℤ) ≤ u).card

/-- **A promised EC-HNP input** (§5 and Definition 5.1).
Kang, Lee, STOC 2027 submission (manuscript sha256 605f9dd3…), §5, p.29 (PDF p.30): "Let p > 3 be
prime and let E/𝔽_p be the nonsingular curve"; Definition 5.1: "a subgroup G = ⟨R₀⟩ of known order
M, and integers N ≥ 5 and 1 ≤ X < p. The input consists of queries Q₁, . . . , Q_N ∈ G … It is
promised to have a hidden point y∗ ∈ E(𝔽_p) satisfying these observations. … [the interval]
contains at most X canonical values".

**Formalization Note.** Every clause is a conjunct: `p > 3`, `4a_E³ + 27b_E² ≠ 0` (nonsingular for
`p > 3`), `N ≥ 5`, `1 ≤ X < p`, `M` the order of `R₀`, queries in `⟨R₀⟩`, each leading-bit interval
of a finite observation with at most `X` canonical values, and a point satisfying all constraints
(including the restriction). The restriction is any property decided by the verifier; subgroup and
coset restrictions are instances. -/
def ECPromised (V : MTMachine) (I : ECInput p) : Prop :=
  3 < p ∧ 4 * I.aE ^ 3 + 27 * I.bE ^ 2 ≠ 0 ∧ 5 ≤ I.N ∧ 1 ≤ I.X ∧ I.X < p ∧
    I.M = addOrderOf I.R0 ∧ (∀ i, I.Q i ∈ AddSubgroup.zmultiples I.R0) ∧
    (∀ u, I.ub = some u → ∀ i v, I.obs i = some v → canonicalCount p v (u i) ≤ I.X) ∧
    ∃ y, ECSatisfies V I y

/-- **An admissible input** ((11)).
Kang, Lee, STOC 2027 submission (manuscript sha256 605f9dd3…), Definition 5.1, p.29 (PDF p.30):
"The queries must satisfy Q_i ≠ O, Q_j − Q_i ∉ E[2] (i ≠ j), E[2] = {T ∈ E(𝔽̄_p) : 2T = O}. Here 𝔽̄_p
is an algebraic closure."

**Formalization Note.** `Q_j − Q_i` is a point of `E(𝔽_p)`, and the inclusion `E(𝔽_p) → E(𝔽̄_p)` is
an injective group homomorphism, so `Q_j − Q_i ∈ E[2]` exactly when `2(Q_j − Q_i) = O` in
`E(𝔽_p)`. -/
def ECAdmissible (I : ECInput p) : Prop :=
  (∀ i, I.Q i ≠ 0) ∧ ∀ i j, i ≠ j → 2 • (I.Q j - I.Q i) ≠ 0

/-- **A finite input**: all observations are finite (Definition 5.1: "We call an input finite when
all its observations are finite"). -/
def ECFinite (I : ECInput p) : Prop :=
  ∀ i, I.obs i ≠ none

/-- **Index set of the EC-HNP polynomials** (Lemma 5.3): the pairs `i < j < N` (paper indices;
Lean `i < j` with `j + 1 < N`), the indices `h < N` (Lean `h + 1 < N`) for `p x_h x_N`, and all
`h ∈ [N]` for `p x_h`. It has `N(N + 1)/2` elements. -/
abbrev ECIdx (N : ℕ) : Type :=
  {ij : Fin N × Fin N // ij.1 < ij.2 ∧ ij.2.val + 1 < N} ⊕ {h : Fin N // h.val + 1 < N} ⊕ Fin N

/-- The paper's last index `N` (Lean `N − 1`), built from any index. -/
def lastIdx {N : ℕ} (i : Fin N) : Fin N := ⟨N - 1, by have := i.isLt; omega⟩

/-- **The source relation `F_ij = z_i z_j − a_ij(z_i + z_j)`**, `a_ij = π₁(Q_j − Q_i)` (§5.1,
p.30), as a polynomial in `z` over `𝔽_p`. -/
noncomputable def ecF (I : ECInput p) (i j : Fin I.N) : MvPolynomial (Fin I.N) (ZMod p) :=
  MvPolynomial.X i * MvPolynomial.X j -
    MvPolynomial.C (pi1 (I.Q j - I.Q i)) * (MvPolynomial.X i + MvPolynomial.X j)

/-- **The combination `F_ij − (b_ij/b_iN)F_iN + (b_ij/b_jN)F_jN`** of (13), `b_ij = π₂(Q_j − Q_i)`.
Kang, Lee, STOC 2027 submission (manuscript sha256 605f9dd3…), Lemma 5.3, p.30 (PDF p.31). -/
noncomputable def ecG (I : ECInput p) (i j : Fin I.N) : MvPolynomial (Fin I.N) (ZMod p) :=
  ecF I i j - MvPolynomial.C (pi2 (I.Q j - I.Q i) / pi2 (I.Q (lastIdx i) - I.Q i)) *
      ecF I i (lastIdx i) +
    MvPolynomial.C (pi2 (I.Q j - I.Q i) / pi2 (I.Q (lastIdx i) - I.Q j)) * ecF I j (lastIdx i)

/-- **The constant `κ_ij`** of (13): the value of the combination at `y = O`, i.e. at
`z_h = π₁(Q_h)`.
Kang, Lee, STOC 2027 submission (manuscript sha256 605f9dd3…), Lemma 5.3, p.30 (PDF p.31): "The
constant κ_ij is computed by evaluating the identity at y = O, since every Q_h is finite." -/
noncomputable def ecKappa (I : ECInput p) (i j : Fin I.N) : ZMod p :=
  MvPolynomial.eval (fun h => pi1 (I.Q h)) (ecG I i j)

/-- The canonical integer lift of a polynomial over `𝔽_p`: each coefficient is replaced by its
representative in `{0, …, p − 1}`. -/
noncomputable def liftZ {σ : Type*} (f : MvPolynomial σ (ZMod p)) : MvPolynomial σ ℤ :=
  ∑ s ∈ f.support, MvPolynomial.monomial s ((MvPolynomial.coeff s f).val : ℤ)

/-- **The polynomial `P_ij`** of Lemma 5.3.
Kang, Lee, STOC 2027 submission (manuscript sha256 605f9dd3…), Lemma 5.3, p.31 (PDF p.32):
"Subtract κ_ij, lift the coefficients to their canonical integer representatives, and substitute
z_h = v_h + x_h to obtain P_ij." -/
noncomputable def ecPij (I : ECInput p) (i j : Fin I.N) : MvPolynomial (Fin I.N) ℤ :=
  MvPolynomial.bind₁ (fun h => MvPolynomial.C ((I.obs h).getD 0) + MvPolynomial.X h)
    (liftZ (ecG I i j - MvPolynomial.C (ecKappa I i j)))

/-- **The EC-HNP polynomial family** (Lemma 5.3).
Kang, Lee, STOC 2027 submission (manuscript sha256 605f9dd3…), Lemma 5.3, p.31 (PDF p.32):
"Together with px_hx_N for h < N and px_h for h ∈ [N], these give m = N(N + 1)/2 polynomials of
degree at most two."

**Formalization Note.** Defined for finite inputs, where every `obs h = some v_h`. The position of
`p x₁` in the family does not affect any statement here. -/
noncomputable def ecPolys (I : ECInput p) : ECIdx I.N → MvPolynomial (Fin I.N) ℤ
  | .inl ij => ecPij I ij.1.1 ij.1.2
  | .inr (.inl h) => MvPolynomial.C (p : ℤ) * MvPolynomial.X h.1 * MvPolynomial.X (lastIdx h.1)
  | .inr (.inr h) => MvPolynomial.C (p : ℤ) * MvPolynomial.X h

open Classical in
/-- **The accepted query tuples** (sampling model of §5).
Kang, Lee, STOC 2027 submission (manuscript sha256 605f9dd3…), Definition 5.1, p.29 (PDF p.30):
"Sample the queries independently and uniformly from G by scalar multiplication of R₀, rejecting
tuples that fail (11)."

The tuples `s ∈ (ℤ_M)^N`, `M` the order of `R₀`, whose queries `Q_i = s_i R₀` satisfy (11).

**Formalization Note.** `s ↦ (s_i R₀)_i` is a bijection `(ℤ_M)^N → G^N`, so the uniform
distribution on accepted `s` is the uniform distribution on accepted query tuples. -/
noncomputable def ecAccepted {aE bE : ZMod p} (R0 : (ecCurve aE bE).Point) (N : ℕ) :
    Finset (Fin N → Fin (addOrderOf R0)) :=
  Finset.univ.filter fun s => (∀ i, (s i : ℕ) • R0 ≠ 0) ∧
    ∀ i j, i ≠ j → 2 • ((s j : ℕ) • R0 - (s i : ℕ) • R0) ≠ 0

/-- An approximation rule: the finite approximations `v_i` and optional interval endpoints `u_i`
as a function of the whole query tuple. -/
abbrev ECRule {aE bE : ZMod p} (R0 : (ecCurve aE bE).Point) (N : ℕ) : Type :=
  (Fin N → Fin (addOrderOf R0)) → (Fin N → ℤ) × Option (Fin N → ℤ)

open Classical in
/-- **The sampled EC-HNP input** for the hidden point `y`, the query tuple `s` and a rule:
infinity observations exactly where `y + Q_i = O` (retained), finite observations `v_i` from the
rule elsewhere. -/
noncomputable def ecSampled {aE bE : ZMod p} (R0 : (ecCurve aE bE).Point) (N X : ℕ)
    (restr : List Bool) (y : (ecCurve aE bE).Point) (rule : ECRule R0 N)
    (s : Fin N → Fin (addOrderOf R0)) : ECInput p where
  aE := aE
  bE := bE
  R0 := R0
  M := addOrderOf R0
  N := N
  X := X
  Q := fun i => (s i : ℕ) • R0
  obs := fun i => if y + (s i : ℕ) • R0 = 0 then none else some ((rule s).1 i)
  ub := (rule s).2
  restr := restr

/-- **An admissible approximation rule** for the hidden point `y`.
Kang, Lee, STOC 2027 submission (manuscript sha256 605f9dd3…), §5, p.30 (PDF p.31): "The
approximations may be functions of all the queries, provided they satisfy (10) for this y∗ and,
for leading bits, the specified integer intervals."

For every accepted tuple the resulting input satisfies the constraints at `y` (so (10) holds, `y`
lies in the intervals and passes the restriction) and every leading-bit interval of a finite
observation has at most `X` canonical values. -/
def ECIsRule (V : MTMachine) {aE bE : ZMod p} (R0 : (ecCurve aE bE).Point) (N X : ℕ)
    (restr : List Bool) (y : (ecCurve aE bE).Point) (rule : ECRule R0 N) : Prop :=
  ∀ s ∈ ecAccepted R0 N, ECSatisfies V (ecSampled R0 N X restr y rule s) y ∧
    ∀ u, (rule s).2 = some u → ∀ i, y + (s i : ℕ) • R0 ≠ 0 →
      canonicalCount p ((rule s).1 i) (u i) ≤ X

/-- **`Δ_N = X^{5N−6}/M^{N−2}`** of (12) (Theorem 5.2, p.30), as a real number. -/
noncomputable def ecDelta (N X M : ℕ) : ℝ :=
  (X : ℝ) ^ (5 * N - 6) / (M : ℝ) ^ (N - 2)

/-- **`ρ_N = (N − 2)/(5N − 6)`** of Theorem 5.2 (p.30). -/
noncomputable def rhoN (N : ℕ) : ℝ :=
  ((N : ℝ) - 2) / (5 * N - 6)

end Supplement

end IntQuotHNP


