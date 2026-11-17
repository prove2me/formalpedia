-- Prove2me | Definitions.Def_IntQuotHNP_Supplement_Recovery
-- name    : IntQuotHNP_Supplement_Recovery
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T07:03:40.475194+00:00
-- url     : https://prove2.me/theorems/7a19d3ec-71c0-4c16-b639-5c900e3f7d8e
-- title:
--   §3.1 and Definition 3.1 — application data, requirements (i)–(iv), reconstructors, and $K=1+12\sqrt d\,4^m$
-- statement:
--   An **application** of the common recovery framework with $k$ error variables and $m$ polynomials assigns to every public input $I$ a prime $p$, an integer $X\ge1$, an **error box** $\mathcal B=\prod_{i=1}^k\mathcal B_i$ of nonempty integer intervals $\mathcal B_i\subseteq[-X,X]$, polynomials $P_1,\dots,P_m\in\mathbb Z[x_1,\dots,x_k]$, and **original input constraints** on a secret $y$ and an error vector $x$. A secret **satisfies the input constraints** when some $x\in\mathcal B$ is consistent with it. Secrets have canonical binary codes, and a finite set of secrets is coded by its members' codes in increasing lexicographic order.
--
--   The **requirements**, with a polynomial bound $C_0(\log p)^{K_0}$, are, for every input:
--
--   1. (i) $P_m=px_1$ and every $P_i$ has total degree at most two;
--   2. (ii) $P_i(x)\equiv0\pmod p$ for all $i$ whenever $x\in\mathcal B$ is consistent with some secret;
--   3. (iii) $\Phi(P_1),\dots,\Phi(P_m)$ are linearly independent over $\mathbb R$;
--   4. (iv) the input code has length at most $C_0(\log p)^{K_0}$, and a deterministic machine computes $p$, $X$, $\mathcal B$ and the full polynomials $P_i$ within $C_0(\log p)^{K_0}$ ticks;
--
--   and secret codes are injective, of length at most $C_0(\log p)^{K_0}$ for secrets satisfying the constraints.
--
--   A **reconstructor** with constant $r\ge1$ is a randomized machine that, given the input and $a\in\mathcal B_1$, returns a set $R(a)$ of at most $r$ secrets such that, over its internal randomness: every element of $R(a)$ satisfies the input constraints with probability one; for every secret $y$ and consistent $x\in\mathcal B$, $\Pr[y\in R(x_1)]=1$; and its expected bit time is at most $C_0(\log p)^{K_0}$ for every input and every $a\in\mathcal B_1$.
--
--   Finally $K=1+12\sqrt d\,4^m$ is the constant of (2).
--
--   **Formalization Note** The paper's indices $1,\dots,k$ are $0,\dots,k-1$ in Lean, so $x_1$ is `x 0` and $P_m$ is `P (Fin.rev 0)`. A polynomial of degree at most two is written out by its constant, linear and quadratic coefficients. The prime modulus is the standing assumption of Definition 2.1. Reading: the deterministic construction step of (iv) also writes out $p$, $X$ and the box, which belong to the public input and are needed by the algorithm.
-- source:
--   Kang, Lee, Provable Recovery from Integer Quotients: Improved Bounds for Nonlinear Hidden Number Problems, STOC 2027 submission (manuscript sha256 605f9dd3…), §3.1, p.16 (PDF p.17); Definition 3.1, p.16 (PDF p.17); eq. (2), p.20 (PDF p.21)

import Mathlib
import Definitions.Def_MatchingFPRAS
import Definitions.Def_IntQuotHNP_Supplement_LasVegas
import Definitions.Def_IntQuotHNP_Supplement_CoeffMap

namespace IntQuotHNP

namespace Supplement

open MeasureTheory OAI.MatchingFPRAS

/-- A binary word written on the tape: `true ↦ 2`, `false ↦ 1`, then the delimiter `3`. -/
def encodeBits (w : List Bool) : List Symbol :=
  w.map (fun b => if b then (2 : Symbol) else 1) ++ [3]

/-- **The canonical code of a finite set of secrets.**
Kang, Lee, *Provable Recovery from Integer Quotients: Improved Bounds for Nonlinear Hidden Number
Problems*, STOC 2027 submission (manuscript sha256 605f9dd3…), Definition 3.1 (iii), p.16
(PDF p.17): "Its elements have canonical binary encodings of length poly(log p)"; Algorithm 1,
p.18: "Output: Y: all secrets satisfying the original input constraints".

Given the binary code `encS y` of each secret, the code of a finite set `s` lists the codes of its
elements in increasing lexicographic order, each written with `encodeBits`.

**Formalization Note.** Sorting makes the code canonical: when `encS` is injective, two sets have
the same code exactly when they are equal. -/
def encodeSet {Sec : Type*} (encS : Sec → List Bool) (s : Finset Sec) : List Symbol :=
  ((s.image encS).sort (· ≤ ·)).flatMap encodeBits

/-- **The code of a polynomial of total degree at most two** in `k` variables: its constant
coefficient, the coefficients of `x_j` (`j` increasing), then those of `x_i x_j` for `i ≤ j`
(lexicographic), each written with `encodeInt`. On polynomials of total degree at most two this
lists every coefficient. -/
noncomputable def polyCode {k : ℕ} (f : MvPolynomial (Fin k) ℤ) : List Symbol :=
  encodeInt (MvPolynomial.coeff 0 f) ++
    (List.ofFn fun j : Fin k => encodeInt (MvPolynomial.coeff (Finsupp.single j 1) f)).flatten ++
    (List.ofFn fun i : Fin k => (List.ofFn fun j : Fin k =>
      if i ≤ j then encodeInt (MvPolynomial.coeff (Finsupp.single i 1 + Finsupp.single j 1) f)
      else []).flatten).flatten

/-- **The data supplied by an application of the common recovery framework** (§3.1).
Kang, Lee, STOC 2027 submission (manuscript sha256 605f9dd3…), §3.1, p.16 (PDF p.17): "Let
B = ∏_{i=1}^k B_i ⊆ [−X, X]^k ∩ ℤ^k be the input's error box, where X ≥ 1 and each B_i is a
nonempty integer interval. A secret y and an error vector x ∈ B are consistent with the input if
together they satisfy the constraints in the application's problem definition. … Each application
specifies P = (P₁, . . . , P_m)^T ∈ ℤ[x]^m".

An application with `k` error variables and `m` polynomials consists of:
1. a type `Inp` of public inputs and a type `Sec` of secrets;
2. the tape code `encI I` of each public input and the canonical binary code `encS y` of each
   secret;
3. for each public input `I`: the modulus `p I`, the bound `X I`, the error box
   `B(I) = ∏ᵢ [lo I i, hi I i] ∩ ℤ`, and the polynomials `P I 0, …, P I (m − 1)`;
4. the original input constraints `Cons I y x` on a secret `y` and an error vector `x`.

**Formalization Note.** The paper's index `i ∈ [k]` is the Lean index `i − 1 ∈ Fin k`, so `x₁` is
`x 0` and `P_m` is `P I (Fin.rev 0)`. Which data are admissible is the separate predicate
`Requirements`. -/
structure Application (k m : ℕ) where
  /-- public inputs -/
  Inp : Type
  /-- secrets -/
  Sec : Type
  /-- the tape code of a public input -/
  encI : Inp → List Symbol
  /-- the canonical binary code of a secret -/
  encS : Sec → List Bool
  /-- the modulus `p` -/
  p : Inp → ℕ
  /-- the error bound `X` -/
  X : Inp → ℕ
  /-- left endpoints of the error intervals `B_i` -/
  lo : Inp → Fin k → ℤ
  /-- right endpoints of the error intervals `B_i` -/
  hi : Inp → Fin k → ℤ
  /-- the polynomials `P₁, …, P_m` -/
  P : Inp → Fin m → MvPolynomial (Fin k) ℤ
  /-- the original input constraints on a secret and an error vector -/
  Cons : Inp → Sec → (Fin k → ℤ) → Prop

variable {k m : ℕ}

/-- `x ∈ B(I)`: every coordinate lies in its error interval. -/
def InBox (A : Application k m) (I : A.Inp) (x : Fin k → ℤ) : Prop :=
  ∀ i, A.lo I i ≤ x i ∧ x i ≤ A.hi I i

/-- **A secret satisfies the original input constraints**: some `x ∈ B` is consistent with it. -/
def Satisfies (A : Application k m) (I : A.Inp) (y : A.Sec) : Prop :=
  ∃ x, InBox A I x ∧ A.Cons I y x

/-- The deterministic output of the construction step for an input: `p`, `X`, the endpoints of
the error intervals and the polynomials `P₁, …, P_m` (`polyCode`), in this order. -/
noncomputable def dataCode (A : Application k m) (I : A.Inp) : List Symbol :=
  encodeNat (A.p I) ++ encodeNat (A.X I) ++
    (List.ofFn fun i => encodeInt (A.lo I i) ++ encodeInt (A.hi I i)).flatten ++
    (List.ofFn fun i => polyCode (A.P I i)).flatten

/-- The scaled coefficient vectors `Φ(P₁), …, Φ(P_m)` of an input (Definition 2.3). -/
noncomputable def basisOf (A : Application k m) (I : A.Inp) :
    Fin m → EuclideanSpace ℝ (mons (A.P I)) :=
  fun i => Phi (A.X I) (A.P I) (A.P I i)

/-- The target vector `v_tar = Φ(p x₁)` of an input (§3.3, p.19). -/
noncomputable def vtarOf [NeZero k] (A : Application k m) (I : A.Inp) :
    EuclideanSpace ℝ (mons (A.P I)) :=
  Phi (A.X I) (A.P I) (MvPolynomial.C (A.p I : ℤ) * MvPolynomial.X 0)

/-- **The constant `K = 1 + 12√d·4^m` of (2).**
Kang, Lee, STOC 2027 submission (manuscript sha256 605f9dd3…), eq. (2), p.20 (PDF p.21):
"where K = 1 + 12√d 4^m depends only on m, d." -/
noncomputable def Kmd (m d : ℕ) : ℝ :=
  1 + 12 * Real.sqrt d * 4 ^ m

/-- **The polynomial requirements (i)–(iv)** of §3.1, with polynomial bounds `C (log p)^K`.
Kang, Lee, STOC 2027 submission (manuscript sha256 605f9dd3…), §3.1, p.16 (PDF p.17):
"(i) P_m = px₁, and every P_i has total degree at most two. (ii) For every secret y and every
corresponding x ∈ B consistent with the input, P_i(x) ≡ 0 (mod p) for all i ∈ [m]. (iii) The
vectors Φ(P₁), . . . , Φ(P_m) are linearly independent over ℝ, where Φ is the scaled coefficient
map of Definition 2.3 for this family and X. (iv) The public input has binary encoding length
poly(log p), and the full polynomials P_i can be constructed deterministically in poly(log p) bit
time."

`Requirements A C K MP` says, for every public input `I`:
1. `p` is prime, `X ≥ 1`, and `B` is a product of nonempty integer intervals inside `[−X, X]`;
2. (i) `P_m = p·x₁` and every `P_i` has total degree at most two;
3. (ii) `p ∣ P_i(x)` for all `i` whenever `x ∈ B` and some secret `y` satisfies `Cons I y x`;
4. (iii) the vectors `Φ(P₁), …, Φ(P_m)` are linearly independent over `ℝ`;
5. (iv) the input code has length at most `C (log p)^K`, and the deterministic machine `MP`
   outputs `dataCode A I` (the polynomials, with `p`, `X` and `B`) within `C (log p)^K` ticks;
and secret codes are injective, of length at most `C (log p)^K` for every secret satisfying the
input constraints (Definition 3.1 (iii), last sentence).

**Formalization Note.** `p` prime is the standing assumption of the paper (Definition 2.1: "The
public parameters are a prime p"). Reading: "constructed deterministically" is a deterministic
machine `MP` on the same machine model; it also writes out `p`, `X` and the box `B`, which are part
of the public input and are needed by the algorithm. -/
def Requirements [NeZero k] [NeZero m] (A : Application k m) (C : ℝ) (K : ℕ)
    (MP : MTMachine) : Prop :=
  Function.Injective A.encS ∧ Deterministic MP ∧
  ∀ I : A.Inp,
    (A.p I).Prime ∧ 1 ≤ A.X I ∧
    (∀ i, -(A.X I : ℤ) ≤ A.lo I i ∧ A.lo I i ≤ A.hi I i ∧ A.hi I i ≤ A.X I) ∧
    A.P I (Fin.rev 0) = MvPolynomial.C (A.p I : ℤ) * MvPolynomial.X 0 ∧
    (∀ i, (A.P I i).totalDegree ≤ 2) ∧
    (∀ y x, InBox A I x → A.Cons I y x → ∀ i, (A.p I : ℤ) ∣ MvPolynomial.eval x (A.P I i)) ∧
    LinearIndependent ℝ (basisOf A I) ∧
    ((A.encI I).length : ℝ) ≤ C * Real.log (A.p I) ^ K ∧
    (∃ t : ℕ, (t : ℝ) ≤ C * Real.log (A.p I) ^ K ∧ RunsWithin MP (A.encI I) (dataCode A I) t) ∧
    (∀ y, Satisfies A I y → ((A.encS y).length : ℝ) ≤ C * Real.log (A.p I) ^ K)

/-- **A reconstructor** (Definition 3.1), with constant `r` and cost bound `C (log p)^K`.
Kang, Lee, STOC 2027 submission (manuscript sha256 605f9dd3…), Definition 3.1, p.16 (PDF p.17): "A
reconstructor is a procedure R that, given the public input and a ∈ B₁, returns a set R(a) of at
most r secret candidates, where r ≥ 1 is a fixed constant. It satisfies: (i) Every element of R(a)
satisfies the original input constraints with probability one. (ii) For every secret y and
corresponding x ∈ B consistent with the input, Pr[y ∈ R(x₁)] = 1. (iii) For every public input and
every a ∈ B₁, computing R(a) has uniform expected bit cost poly(log p). … Probabilities and
expectations here are over reconstruction randomness."

`IsReconstructor A r C K MR` says that the randomized machine `MR`, run on the input code followed
by the integer `a`, satisfies for every public input `I` and every `a ∈ B₁`:
1. with probability one it halts with the code of a set of at most `r` secrets, each satisfying the
   input constraints;
2. for every secret `y` and `x ∈ B` with `Cons I y x` and `x₁ = a`, with probability one its output
   set contains `y`;
3. its expected bit time is at most `C (log p)^K`.

**Formalization Note.** `R(a)` is the set whose code `encodeSet` the machine leaves on the tape.
"With probability one" is `∀ᵐ` under the fair-coin measure, and (ii) is quantified as in the paper,
`∀ y x` outside the almost-sure statement. -/
def IsReconstructor (A : Application k m) [NeZero k] (r : ℕ) (C : ℝ) (K : ℕ)
    (MR : MTMachine) : Prop :=
  ∀ (I : A.Inp) (a : ℤ), A.lo I 0 ≤ a → a ≤ A.hi I 0 →
    (∀ᵐ ω ∂coinMeasure, ∃ s : Finset A.Sec, s.card ≤ r ∧ (∀ y ∈ s, Satisfies A I y) ∧
      OutputsOn MR (A.encI I ++ encodeInt a) ω (encodeSet A.encS s)) ∧
    (∀ y x, InBox A I x → A.Cons I y x → x 0 = a →
      ∀ᵐ ω ∂coinMeasure, ∃ s : Finset A.Sec, y ∈ s ∧
        OutputsOn MR (A.encI I ++ encodeInt a) ω (encodeSet A.encS s)) ∧
    expectedTime MR (A.encI I ++ encodeInt a) ≤ ENNReal.ofReal (C * Real.log (A.p I) ^ K)

end Supplement

end IntQuotHNP


