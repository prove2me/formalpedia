-- Prove2me | Definitions.Def_MerkleROM_VerifierLowerBound_protocol
-- name    : MerkleROM_VerifierLowerBound_protocol
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-09T22:32:36.191187+00:00
-- url     : https://prove2.me/theorems/1829ad16-9b12-4ca1-9719-80d6c5cb1032
-- title:
--   Algorithm 2, actual errors, round tables and decoder
-- statement:
--   The communication experiment first applies Fact 1 to the original scheme. Consequently $Q$ below includes its extra $kn$ committer queries. Alice samples a uniform vector, commits, checks every honest opening under the shared oracle, and either records completeness error or sends $c$. Bob begins with an empty table. The hardness parameter is
--
--   $$p=Q+2kn+n^3.$$
--
--   Each of the $k$ rounds runs Algorithm 1 and propagates its hardening or binding failure. With its returned table, Alice greedily chooses uncertified indices in increasing index order whose residual honest query sets are pairwise disjoint. She records disjointness error if their number is at least $\ell+\lambda$, where $\ell$ is the number of bits already sent. Otherwise she sends their union of query inputs, encoded with delimiters and padded to $2k\theta(\ell+\lambda)$ bits. Bob decodes the actual binary message, queries those inputs, and extends his table. Wrong-bit certification and double certification produce binding error; unique certification of every index produces Bob's output.
--
--   The state contains actual messages, queries, reached round snapshots and the decoder's result. Bob's decoder depends only on $c$ and his table. Error probabilities average over the sampled oracle, honest vector and independent committer randomness. With zero rounds, no round snapshot or round message is created; the main theorem still includes zero-query verifiers. The message-cap predicate is an eventual bound over the support of this actual experiment, rather than an independence assumption about transcripts.
--
--   These definitions make the four errors and both bookkeeping facts properties of one operational protocol.
-- source:
--   Miranda Christ, Oliver Korten, Tal Malkin, Noam Mazor, Shyamal Patel, STOC 2027 submission #1169 (October 2026), Merkle Trees Minimize Verifier Complexity in the ROM, p.18, Algorithm 2; pp.19–22, error analyses and Facts 2–3. https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1169.pdf

import Definitions.Def_MerkleROM_VerifierLowerBound_harden

set_option autoImplicit false
noncomputable section

namespace MerkleROM.VerifierLowerBound

variable {theta lam n m : ℕ}

def residual (W T : Table (Bits theta) (Bits lam)) : Finset (Bits theta) :=
  tableDomain W \ tableDomain T

def honestTables (S : Scheme theta lam n m) (x : Bits n) (o : HonestOutput n m)
    (R : Bits theta → Bits lam) : Fin n → Table (Bits theta) (Bits lam) :=
  fun i => (S.verify o.commitment i (x i) (o.witnesses i)).transcript R

/-- Increasing index order is fixed before the random oracle is sampled. -/
def greedyDisjoint (S : Scheme theta lam n m) (k : ℕ) (c : Bits m)
    (W : Fin n → Table (Bits theta) (Bits lam)) (T : Table (Bits theta) (Bits lam)) :
    Finset (Fin n) := by
  classical
  exact (List.ofFn (fun i : Fin n => i)).foldl (fun chosen i =>
    if ¬Certified S k c T i ∧ ∀ j ∈ chosen, Disjoint (residual (W i) T) (residual (W j) T)
    then insert i chosen else chosen) ∅

def unionResidual (W : Fin n → Table (Bits theta) (Bits lam))
    (T : Table (Bits theta) (Bits lam)) (chosen : Finset (Fin n)) : Finset (Bits theta) := by
  classical
  exact chosen.biUnion (fun i => residual (W i) T)

/-- A true bit marks each theta-bit query; a false bit ends the list. Padding is zero.
The factor 2 in Algorithm 2 accommodates this delimiter encoding when theta is positive. -/
def encodeQueries (qs : List (Bits theta)) (budget : ℕ) : StringBits :=
  let raw := qs.flatMap (fun q => true :: List.ofFn q) ++ [false]
  raw ++ List.replicate (budget-raw.length) false

def decodeQueries (theta : ℕ) : ℕ → StringBits → List (Bits theta)
  | 0,_ => []
  | _+1,[] => []
  | _+1,false::_ => []
  | fuel+1,true::s => if s.length < theta then []
      else bitsFromList theta s :: decodeQueries theta fuel (s.drop theta)

def decodedQueries (theta : ℕ) (s : StringBits) : List (Bits theta) :=
  decodeQueries theta s.length s

/-- Bob's output uses only public c and his own table. -/
def decodeVector (S : Scheme theta lam n m) (k : ℕ) (c : Bits m)
    (T : Table (Bits theta) (Bits lam)) : Option (Bits n) := by
  classical
  exact if (∀ i, Certified S k c T i) ∧ ¬DoubleCertified S k c T
    then some (fun i => decide (CertifiedBit S k c T i true)) else none

inductive ProtocolStatus where
  | running | success | completenessError | hardeningError | bindingError | disjointnessError
  deriving DecidableEq

structure RoundSnapshot (theta lam : ℕ) where
  round : ℕ
  table : Table (Bits theta) (Bits lam)
  bitsSent : ℕ

structure ProtocolState (theta lam n : ℕ) where
  table : Table (Bits theta) (Bits lam)
  messages : List StringBits
  rounds : List (RoundSnapshot theta lam)
  queries : Table (Bits theta) (Bits lam)
  status : ProtocolStatus
  output : Option (Bits n)

def bitsSent (st : ProtocolState theta lam n) : ℕ :=
  (st.messages.map List.length).sum

/-- Algorithm 2's round transition. Hardening, messages, aborts and decoder are computed. -/
def protocolRounds (S : Scheme theta lam n m) (k p : ℕ) (x : Bits n)
    (o : HonestOutput n m) (W : Fin n → Table (Bits theta) (Bits lam))
    (R : Bits theta → Bits lam) : ℕ → ℕ → ProtocolState theta lam n → ProtocolState theta lam n
  | 0,_,st => st
  | fuel+1,round,st => by
    classical
    let h := harden S k p o.commitment st.table R
    let hs := {st with table := h.table,queries := st.queries ++ h.queries}
    exact match h.status with
    | .fail => {hs with status := .hardeningError}
    | .binding => {hs with status := .bindingError}
    | .hard =>
      let chosen := greedyDisjoint S k o.commitment W h.table
      if chosen.card ≥ bitsSent st + lam then {hs with status := .disjointnessError}
      else
        let qs := (unionResidual W h.table chosen).toList
        let message := encodeQueries qs (2*k*theta*(bitsSent st+lam))
        let received := decodedQueries theta message
        let replies := received.map (fun q => (q,R q))
        let nextTable := h.table ++ replies
        let sent := {hs with messages := st.messages ++ [message]}
        if ∃ i, CertifiedBit S k o.commitment nextTable i (!(x i)) then
          {sent with status := .bindingError}
        else
          let next := {sent with
            table := nextTable
            queries := hs.queries ++ replies}
          if DoubleCertified S k o.commitment nextTable then
            {next with status := .bindingError}
          else
            let completed := {next with rounds := st.rounds ++ [⟨round,nextTable,bitsSent next⟩]}
            match decodeVector S k o.commitment nextTable with
            | some v => {completed with status := .success,output := some v}
            | none => protocolRounds S k p x o W R fuel (round+1) completed

def protocolRun (S : Scheme theta lam n m) (Q k : ℕ) (x : Bits n)
    (a : Tree (Bits theta) (Bits lam) (HonestOutput n m)) (R : Bits theta → Bits lam) :
    ProtocolState theta lam n := by
  classical
  let o := a.run R
  let W := honestTables S x o R
  let queries := a.transcript R ++ (List.ofFn W).flatten
  let initial : ProtocolState theta lam n := ⟨[],[],[],queries,.running,none⟩
  exact if ∃ i, (S.verify o.commitment i (x i) (o.witnesses i)).run R = false
    then {initial with status := .completenessError}
    else protocolRounds S k (Q+2*k*n+n^3) x o W R k 1
      {initial with messages := [List.ofFn o.commitment]}

def protocolLaw (S : Scheme theta lam n m) (Q k : ℕ) : PMF (ProtocolState theta lam n) :=
  (PMF.uniformOfFintype (Bits n)).bind fun x =>
  (uniformOracle theta lam).bind fun R =>
  (S.commit x).map fun a => protocolRun S Q k x a R

/-- The source protocol is run AFTER Fact 1. Thus Q includes the extra kn
normalization queries; the second kn verification work is performed at initialization. -/
def errorProbability (F : SchemeFamily) (n : ℕ → ℕ) (status : ProtocolStatus) (l : ℕ) : ℝ :=
  let G := normalizeFamily F
  probability (protocolLaw (G.scheme l (n l)) (G.commitQueries l (n l))
    (G.verifyQueries l (n l))) (fun st => st.status = status)

def MessageCap (F : SchemeFamily) (n : ℕ → ℕ) : Prop :=
  let G := normalizeFamily F
  ∃ N, ∀ l ≥ N, ∀ st ∈ (protocolLaw (G.scheme l (n l)) (G.commitQueries l (n l))
    (G.verifyQueries l (n l))).support, bitsSent st ≤ n l

end MerkleROM.VerifierLowerBound


