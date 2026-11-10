-- Prove2me | Definitions.Def_MerkleROM_VerifierLowerBound_commitment
-- name    : MerkleROM_VerifierLowerBound_commitment
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-09T22:30:22.476556+00:00
-- url     : https://prove2.me/theorems/736e8f4d-a9c5-4d6f-ae2e-e14d0211d6fc
-- title:
--   Vector commitments, query-only security and asymptotic families
-- statement:
--   A family $\Sigma=(\mathsf{Commit},\mathsf{Verify})$ supports every security parameter $\lambda$ and vector length $n$. Its oracle has input length $\theta(\lambda)$ and output length $\lambda$. A randomized committer receives $x\in\{0,1\}^n$ and returns a fixed-length commitment $c\in\{0,1\}^{m(\lambda,n)}$ and $n$ finite binary witnesses. The verifier receives $(c,i,b,\pi)$ and is a deterministic adaptive oracle algorithm. All executions respect query bounds $Q(\lambda,n)$ and $k(\lambda,n)$ polynomial in $\lambda+n$; local computation is unrestricted. Commitment length itself is not assumed polynomial.
--
--   A real function $\nu$ taking values in $[0,1]$ is negligible when
--
--   $$\forall C>0\ \forall d\in\mathbb N\ \exists\lambda_0\ \forall\lambda\ge\lambda_0,\qquad \nu(\lambda)<\frac{1}{C(\lambda+1)^d}.$$
--
--   Completeness requires one negligible bound common to every honest vector and every polynomially bounded length family, on the probability that any honest opening fails. Position binding quantifies over every polynomial-query randomized adversary and length family. Its actual experiment checks that one adversarial commitment has two accepted different bits at one valid index, under the same sampled oracle. Invalid indices lose. The adversary's output and coins are computed through its oracle tree, rather than supplied as oracle-dependent advice.
--
--   The growth predicates express polynomial bounds, a polynomial relation between $\theta$ and $\lambda$, eventual positive input length and $n=\Omega(\lambda)$. They impose no fixed polynomial degree. These definitions expose the complete security assumptions needed by the lower bound.
-- source:
--   Miranda Christ, Oliver Korten, Tal Malkin, Noam Mazor, Shyamal Patel, STOC 2027 submission #1169 (October 2026), Merkle Trees Minimize Verifier Complexity in the ROM, p.14, §4.1, Definitions 1–2; p.2, footnote 6; p.21, Theorem 1. https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1169.pdf

import Definitions.Def_MerkleROM_VerifierLowerBound_oracle

set_option autoImplicit false
noncomputable section

namespace MerkleROM.VerifierLowerBound

/-- Polynomial bounds have constants chosen before the security parameter. -/
def PolynomiallyBounded (f : ℕ → ℕ) : Prop :=
  ∃ C d N : ℕ, ∀ l ≥ N, f l ≤ C * (l + 1)^d

/-- Testing positive monomials is equivalent to testing every positive polynomial. -/
def Negligible (f : ℕ → ℝ) : Prop :=
  (∀ l, 0 ≤ f l ∧ f l ≤ 1) ∧
  ∀ C : ℝ, 0 < C → ∀ d : ℕ, ∃ N, ∀ l ≥ N, f l < 1 / (C * (l + 1 : ℝ)^d)

def OmegaSecurity (n : ℕ → ℕ) : Prop :=
  ∃ C : ℕ, 0 < C ∧ ∃ N, ∀ l ≥ N, l ≤ C * n l

/-- Section 4's polynomial relation, including positive input lengths eventually. -/
def OracleLengths (theta : ℕ → ℕ) : Prop :=
  PolynomiallyBounded theta ∧
  (∃ C d N : ℕ, ∀ l ≥ N, l ≤ C * (theta l + 1)^d) ∧
  (∃ N, ∀ l ≥ N, 0 < theta l)

structure HonestOutput (n m : ℕ) where
  commitment : Bits m
  witnesses : Fin n → StringBits

/-- Both algorithms receive only their public inputs and black-box oracle replies. -/
structure Scheme (theta lam n m : ℕ) where
  commit : Bits n → PMF (Tree (Bits theta) (Bits lam) (HonestOutput n m))
  verify : Bits m → Fin n → Bool → StringBits → Tree (Bits theta) (Bits lam) Bool

def QueryBounds {theta lam n m : ℕ} (S : Scheme theta lam n m) (Q k : ℕ) : Prop :=
  (∀ x, RandomBounded Q (S.commit x)) ∧
  ∀ c i b w, Bounded k (S.verify c i b w)

/-- One family supports every input-vector length. Local computation is unrestricted. -/
structure SchemeFamily where
  theta : ℕ → ℕ
  size : ℕ → ℕ → ℕ
  commitQueries : ℕ → ℕ → ℕ
  verifyQueries : ℕ → ℕ → ℕ
  scheme : (l n : ℕ) → Scheme (theta l) l n (size l n)

def Efficient (F : SchemeFamily) : Prop :=
  (∀ l n, QueryBounds (F.scheme l n) (F.commitQueries l n) (F.verifyQueries l n)) ∧
  (∃ C d : ℕ, ∀ l n, F.commitQueries l n ≤ C * (l+n+1)^d) ∧
  (∃ C d : ℕ, ∀ l n, F.verifyQueries l n ≤ C * (l+n+1)^d)

def honestLaw {theta lam n m : ℕ} (S : Scheme theta lam n m) (x : Bits n) :
    PMF ((Bits theta → Bits lam) × HonestOutput n m) :=
  (uniformOracle theta lam).bind fun R => (S.commit x).map fun t => (R,t.run R)

def completenessFailure {theta lam n m : ℕ} (S : Scheme theta lam n m) (x : Bits n) : ℝ :=
  probability (honestLaw S x) fun z =>
    ∃ i, (S.verify z.2.commitment i (x i) (z.2.witnesses i)).run z.1 = false

/-- The same negligible bound applies to every vector, not a bound selected after x. -/
def Complete (F : SchemeFamily) : Prop :=
  ∃ nu : ℕ → ℝ, Negligible nu ∧
    ∀ n : ℕ → ℕ, PolynomiallyBounded n → ∀ l (x : Bits (n l)),
      completenessFailure (F.scheme l (n l)) x ≤ nu l

structure Forgery (m : ℕ) where
  commitment : Bits m
  index : ℕ
  bit : Bool
  otherBit : Bool
  witness : StringBits
  otherWitness : StringBits

def wins {theta lam n m : ℕ} (S : Scheme theta lam n m)
    (R : Bits theta → Bits lam) (f : Forgery m) : Prop :=
  f.bit ≠ f.otherBit ∧ ∃ i : Fin n, i.val = f.index ∧
    (S.verify f.commitment i f.bit f.witness).run R = true ∧
    (S.verify f.commitment i f.otherBit f.otherWitness).run R = true

def bindingProbability {theta lam n m : ℕ} (S : Scheme theta lam n m)
    (A : PMF (Tree (Bits theta) (Bits lam) (Forgery m))) : ℝ :=
  probability ((uniformOracle theta lam).bind fun R =>
    A.map fun t => (R,t.run R)) fun z => wins S z.1 z.2

/-- Unbounded local computation, all polynomial query budgets, adversarial commitments,
and two openings checked under one shared sampled oracle. -/
def PositionBinding (F : SchemeFamily) : Prop :=
  ∀ n : ℕ → ℕ, PolynomiallyBounded n →
  ∀ q : ℕ → ℕ, PolynomiallyBounded q →
  ∀ A : (l : ℕ) → PMF (Tree (Bits (F.theta l)) (Bits l) (Forgery (F.size l (n l)))),
    (∀ l, RandomBounded (q l) (A l)) →
    Negligible (fun l => bindingProbability (F.scheme l (n l)) (A l))

def Secure (F : SchemeFamily) : Prop :=
  Efficient F ∧ Complete F ∧ PositionBinding F

end MerkleROM.VerifierLowerBound


