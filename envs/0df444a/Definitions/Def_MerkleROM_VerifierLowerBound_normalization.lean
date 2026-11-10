-- Prove2me | Definitions.Def_MerkleROM_VerifierLowerBound_normalization
-- name    : MerkleROM_VerifierLowerBound_normalization
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-09T22:31:19.598285+00:00
-- url     : https://prove2.me/theorems/22c60ab8-e8b3-44e6-a727-34a712831a66
-- title:
--   Operational transcript normalization
-- statement:
--   For an original deterministic verifier, a transcript is a list $W=((q_1,a_1),\ldots,(q_k,a_k))$. An accepting transcript is consistent and contains the entire accepting execution of some original binary witness. The existential search is over the original acceptance relation, not merely over consistent answers.
--
--   The normalized verifier queries every listed input nonadaptively, checks that the actual answers equal those listed, and checks existence of the original accepting witness. The normalized committer first runs the original committer and then each original honest verification to obtain the corresponding transcript. Short transcripts are padded by actual dummy queries, to give
--
--   $$|\pi_i'|=(\theta+\lambda)k.$$
--
--   Malformed encodings are rejected. Fixed-size block encoding and decoding are specified explicitly, and the commitment is retained verbatim. The family transformation records the new committer bound $Q+kn$ and unchanged verifier bound $k$; preservation of security and these bounds is a theorem item, not an axiom in this definition.
--
--   This is the source's Fact 1 construction and supplies the normalized scheme used by the communication experiment.
-- source:
--   Miranda Christ, Oliver Korten, Tal Malkin, Noam Mazor, Shyamal Patel, STOC 2027 submission #1169 (October 2026), Merkle Trees Minimize Verifier Complexity in the ROM, p.15, Fact 1 and its construction. https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1169.pdf

import Definitions.Def_MerkleROM_VerifierLowerBound_commitment

set_option autoImplicit false
noncomputable section

namespace MerkleROM.VerifierLowerBound

variable {X Y A : Type}

def withTranscript : Tree X Y A → Tree X Y (A × Table X Y)
  | .done a => .done (a,[])
  | .probe x next => .probe x (fun y =>
      treeMap (fun out => (out.1,(x,y)::out.2)) (withTranscript (next y)))

def tableOracle {theta lam : ℕ} (T : Table (Bits theta) (Bits lam)) : Bits theta → Bits lam := by
  classical
  exact fun q => (T.lookup q).getD (fun _ => false)

def encodeTable {theta lam : ℕ} (T : Table (Bits theta) (Bits lam)) : StringBits :=
  T.flatMap fun z => List.ofFn z.1 ++ List.ofFn z.2

def bitsFromList (n : ℕ) (s : StringBits) : Bits n := fun i => s[i.val]?.getD false

def decodeTable (theta lam : ℕ) : ℕ → StringBits → Option (Table (Bits theta) (Bits lam))
  | 0, s => if s.isEmpty then some [] else none
  | k+1, s => if s.length < theta+lam then none else do
      let tail ← decodeTable theta lam k (s.drop (theta+lam))
      pure ((bitsFromList theta s, bitsFromList lam (s.drop theta)) :: tail)

/-- Existence of an ORIGINAL accepting witness whose execution is wholly answered by W. -/
def AcceptingTranscript {theta lam n m : ℕ} (S : Scheme theta lam n m)
    (c : Bits m) (i : Fin n) (b : Bool) (W : Table (Bits theta) (Bits lam)) : Prop :=
  Consistent W ∧ ∃ w : StringBits,
    (S.verify c i b w).run (tableOracle W) = true ∧
    ∀ z ∈ (S.verify c i b w).transcript (tableOracle W), z ∈ W

def normalizedVerifier {theta lam n m : ℕ} (S : Scheme theta lam n m) (k : ℕ)
    (c : Bits m) (i : Fin n) (b : Bool) (w : StringBits) : Tree (Bits theta) (Bits lam) Bool := by
  classical
  exact match decodeTable theta lam k w with
  | none => .done false
  | some W => treeMap (fun actual => decide (actual = W ∧ AcceptingTranscript S c i b W))
      (readQueries (W.map Prod.fst))

/-- Pad by actual dummy queries; total verification-and-padding cost is at most k. -/
def normalizedWitness {theta lam n m : ℕ} (S : Scheme theta lam n m) (k : ℕ)
    (c : Bits m) (i : Fin n) (b : Bool) (w : StringBits) :
    Tree (Bits theta) (Bits lam) StringBits :=
  treeBind (withTranscript (S.verify c i b w)) fun z =>
    treeMap (fun pad => encodeTable (z.2 ++ pad))
      (readQueries (List.replicate (k-z.2.length) (fun _ => false)))

def collectWitnesses {theta lam n m : ℕ} (S : Scheme theta lam n m) (k : ℕ)
    (x : Bits n) (o : HonestOutput n m) : List (Fin n) →
    Tree (Bits theta) (Bits lam) (List (Fin n × StringBits))
  | [] => .done []
  | i::is => treeBind (normalizedWitness S k o.commitment i (x i) (o.witnesses i)) fun w =>
      treeMap (fun tail => (i,w)::tail) (collectWitnesses S k x o is)

def normalizeScheme {theta lam n m : ℕ} (S : Scheme theta lam n m) (k : ℕ) :
    Scheme theta lam n m := by
  classical
  exact {
    commit := fun x => (S.commit x).map fun a => treeBind a fun o =>
      treeMap (fun ws => (⟨o.commitment,fun i => (ws.lookup i).getD []⟩ : HonestOutput n m))
        (collectWitnesses S k x o (List.ofFn (fun i : Fin n => i)))
    verify := normalizedVerifier S k }

def normalizeFamily (F : SchemeFamily) : SchemeFamily := {
  theta := F.theta
  size := F.size
  commitQueries := fun l n => F.commitQueries l n + F.verifyQueries l n * n
  verifyQueries := F.verifyQueries
  scheme := fun l n => normalizeScheme (F.scheme l n) (F.verifyQueries l n) }

end MerkleROM.VerifierLowerBound


