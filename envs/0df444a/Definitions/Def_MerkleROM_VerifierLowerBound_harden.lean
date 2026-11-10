-- Prove2me | Definitions.Def_MerkleROM_VerifierLowerBound_harden
-- name    : MerkleROM_VerifierLowerBound_harden
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-09T22:31:54.229025+00:00
-- url     : https://prove2.me/theorems/af58703a-2646-4dbb-9b3e-b7afdb8244f8
-- title:
--   Certification, hardness and Algorithm 1
-- statement:
--   Fix a commitment $c$ and a consistent table $T$. An index-bit pair is certified if at most $k$ entries of $T$ form an accepting transcript for that pair. An index is certified if at least one bit is certified. The table is $p$-hard if no deterministic $p$-query search has success probability exceeding $1/p$ in the uniform extending-oracle experiment. Success means finding an accepted witness for an uncertified index and querying all of its inputs. Randomized searches give the same hardness condition by averaging their deterministic trees.
--
--   Algorithm 1 performs at most
--
--   $$3pn^2\lambda+1$$
--
--   tests. Each test checks double certification, then hardness, then whether it is the final test. Otherwise it runs the first successful search in a fixed well-order of trees, appends its query answers, queries its alleged witness, and appends those answers too. Candidate witnesses are typed to contain at most $k$ entries; an invalid alleged opening can be represented by failure. The result records its returned table, all calls actually made, and its binding, hard or fail status.
--
--   The extending-oracle law has an explicit default on an inconsistent table; every theorem using it assumes consistency, and actual executions preserve it. No probability estimate or hardness guarantee is assumed by the procedure.
-- source:
--   Miranda Christ, Oliver Korten, Tal Malkin, Noam Mazor, Shyamal Patel, STOC 2027 submission #1169 (October 2026), Merkle Trees Minimize Verifier Complexity in the ROM, pp.16–17, Definitions 6–8 and Algorithm 1. https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1169.pdf

import Definitions.Def_MerkleROM_VerifierLowerBound_normalization

set_option autoImplicit false
noncomputable section

namespace MerkleROM.VerifierLowerBound

/-- Totalization on an inconsistent table is unused in every theorem and execution. -/
def tableLaw {theta lam : ℕ} (T : Table (Bits theta) (Bits lam)) :
    PMF (Bits theta → Bits lam) := by
  classical
  exact if h : Consistent T then extendingOracle T h else pure (fun _ _ => false)

structure Candidate (theta lam n k : ℕ) where
  index : Fin n
  bit : Bool
  witness : Table (Bits theta) (Bits lam)
  sizeBound : witness.length ≤ k

/-- Table entries themselves exhibit an accepting original execution. -/
def CertifiedBit {theta lam n m : ℕ} (S : Scheme theta lam n m) (k : ℕ)
    (c : Bits m) (T : Table (Bits theta) (Bits lam)) (i : Fin n) (b : Bool) : Prop :=
  ∃ W : Table (Bits theta) (Bits lam), W.length ≤ k ∧
    (∀ z ∈ W, z ∈ T) ∧ AcceptingTranscript S c i b W

def Certified {theta lam n m : ℕ} (S : Scheme theta lam n m) (k : ℕ)
    (c : Bits m) (T : Table (Bits theta) (Bits lam)) (i : Fin n) : Prop :=
  ∃ b, CertifiedBit S k c T i b

def DoubleCertified {theta lam n m : ℕ} (S : Scheme theta lam n m) (k : ℕ)
    (c : Bits m) (T : Table (Bits theta) (Bits lam)) : Prop :=
  ∃ i, CertifiedBit S k c T i false ∧ CertifiedBit S k c T i true

def newWitness {theta lam n m : ℕ} (S : Scheme theta lam n m) (k : ℕ)
    (c : Bits m) (T : Table (Bits theta) (Bits lam)) (R : Bits theta → Bits lam)
    (out : Option (Candidate theta lam n k)) (trace : Table (Bits theta) (Bits lam)) : Prop :=
  ∃ o, out = some o ∧ o.witness.length ≤ k ∧
    ¬Certified S k c T o.index ∧ AcceptingTranscript S c o.index o.bit o.witness ∧
    Extends R o.witness ∧ ∀ q ∈ tableDomain o.witness, q ∈ tableDomain trace

def searchSuccess {theta lam n m : ℕ} (S : Scheme theta lam n m) (k : ℕ)
    (c : Bits m) (T : Table (Bits theta) (Bits lam))
    (a : Tree (Bits theta) (Bits lam) (Option (Candidate theta lam n k))) : ℝ :=
  probability (tableLaw T) fun R => newWitness S k c T R (a.run R) (a.transcript R)

/-- The algorithm must find AND query the alleged accepting witness. -/
def Hard {theta lam n m : ℕ} (S : Scheme theta lam n m) (k p : ℕ)
    (c : Bits m) (T : Table (Bits theta) (Bits lam)) : Prop :=
  ¬∃ a : Tree (Bits theta) (Bits lam) (Option (Candidate theta lam n k)),
    Bounded p a ∧ 1/(p : ℝ) < searchSuccess S k c T a

/-- Fixed choice depends on c and T, never on unobserved oracle answers. -/
def easySearch {theta lam n m : ℕ} (S : Scheme theta lam n m) (k p : ℕ)
    (c : Bits m) (T : Table (Bits theta) (Bits lam))
    (h : ¬Hard S k p c T) : Tree (Bits theta) (Bits lam) (Option (Candidate theta lam n k)) :=
  fixedChoice (fun a => Bounded p a ∧ 1/(p : ℝ) < searchSuccess S k c T a)
    (Classical.not_not.mp h)

inductive HardenStatus where
  | binding | hard | fail
  deriving DecidableEq

structure HardenResult (theta lam : ℕ) where
  table : Table (Bits theta) (Bits lam)
  queries : Table (Bits theta) (Bits lam)
  status : HardenStatus

/-- Algorithm 1. A final test is performed after fuel many search attempts. -/
def hardenSteps {theta lam n m : ℕ} (S : Scheme theta lam n m) (k p : ℕ)
    (c : Bits m) (R : Bits theta → Bits lam) :
    ℕ → Table (Bits theta) (Bits lam) → HardenResult theta lam
  | fuel,T => by
    classical
    exact if DoubleCertified S k c T then ⟨T,[],.binding⟩
    else if h : Hard S k p c T then ⟨T,[],.hard⟩
    else match fuel with
    | 0 => ⟨T,[],.fail⟩
    | f+1 =>
      let a := easySearch S k p c T h
      let tr := a.transcript R
      let alleged := match a.run R with
        | none => []
        | some o => o.witness.map Prod.fst
      let checked := alleged.map (fun q => (q,R q))
      let out := hardenSteps S k p c R f (T ++ tr ++ checked)
      ⟨out.table, tr ++ checked ++ out.queries,out.status⟩

def harden {theta lam n m : ℕ} (S : Scheme theta lam n m) (k p : ℕ)
    (c : Bits m) (T : Table (Bits theta) (Bits lam)) (R : Bits theta → Bits lam) :=
  hardenSteps S k p c R (3*p*n^2*lam) T

end MerkleROM.VerifierLowerBound


