-- Prove2me | Definitions.Def_AMRangeAvoid_Characterization_Protocol
-- name    : AMRangeAvoid_Characterization_Protocol
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-08T11:01:07.735741+00:00
-- url     : https://prove2.me/theorems/e9d8ab38-36e3-4a14-9e65-55e60f552fd2
-- title:
--   The shifted-hash SSLB verifier of Theorem 3.3
-- statement:
--   The named SSLB verifier rejects malformed inputs and the branch $4\tau>2^n$. Otherwise set
--   $$d=12n,\ N=dn,\ k=2d-1+\lfloor\log_2(\tau^d)\rfloor,\ R=k(N+1),\ \ell=R+1,\ t=\ell R+2.$$
--   Arthur supplies $t$ independent $R$-bit challenges, each a row-major binary matrix and target vector. Merlin supplies $\ell$ shifts, then for each challenge an $h=\lceil\log_2\ell\rceil$-bit index, a concatenation of $d$ objects, and their membership witnesses. Invalid indices reject; legal indices are zero-based encodings of the source's indices $1,\ldots,\ell$. For every challenge, shifting by its selected shift must give a matrix/target pair with $A's=b'$, and every supplied object/witness pair must satisfy $P$.
--
--   Both full message lengths are fixed at
--   $$p(L)=4{,}000{,}000(L+1)^{12},$$
--   where $L$ includes all input descriptions. Only the raw prefixes are read. Length mismatches reject. The raw lengths are $Q=tR$ and $\ell R+t(h+dn+db)$ for witness width $b$. Integer bounds ensure that these fit the padding on every valid active-branch input. The arithmetic evaluator and predicate have operational bodies; the polynomial certificate is mathematical data. Efficiency, completeness and soundness are theorem obligations, not fields of this definition. Both Theorems 3.3 and 3.5 refer to this same verifier.
-- source:
--   Zeyong Li, STOC 2027 submission #502 (October 2026), Theorem 3.3 and its protocol, printed pp.15–16 (PDF pp.17–18); Definition 2.2, printed p.10 (PDF p.12), for length-only polynomial normalization; https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/502.pdf

import Definitions.Def_AMRangeAvoid_Characterization_SSLB

/-! The actual shifted-hash verifier in the proof of Theorem 3.3, shared by
Theorems 3.3 and 3.5. Li, STOC 2027 submission #502, printed pp.15–16
(PDF pp.17–18). All formulas and all checks are operational.
-/
namespace AMRangeAvoid.Characterization

structure ProtocolParameters where
  d : ℕ
  N : ℕ
  k : ℕ
  R : ℕ
  ell : ℕ
  t : ℕ
  h : ℕ
  deriving DecidableEq, Repr, Inhabited

def parameters (I : SSLBInstance) : ProtocolParameters :=
  let d := 12 * I.n
  let N := d * I.n
  let k := 2 * d - 1 + floorLog2 (I.threshold ^ d)
  let R := k * (N + 1)
  let ell := R + 1
  let t := ell * R + 2
  ⟨d, N, k, R, ell, t, ceilLog2 ell⟩

def ProtocolParameters.rawRandom (a : ProtocolParameters) : ℕ := a.t * a.R

def ProtocolParameters.blockResponse (a : ProtocolParameters) (w : ℕ) : ℕ :=
  a.h + a.N + a.d * w

def ProtocolParameters.rawResponse (a : ProtocolParameters) (w : ℕ) : ℕ :=
  a.ell * a.R + a.t * a.blockResponse w

/-- Consecutive little-endian bits, padded with zero only on malformed short data. -/
def slice (b : Bits) (start count : ℕ) : Bits :=
  (List.range count).map (fun j => b.getD (start + j) false)

/-- F₂ dot product, with row-major matrix data in the challenge. -/
def dotRow (a : ProtocolParameters) (rho s : Bits) (row : ℕ) : Bool :=
  (List.range a.N).foldl
    (fun v j => Bool.xor v (rho.getD (row * a.N + j) false && s.getD j false)) false

/-- One response block: an index, d objects, then d membership witnesses.
An invalid h-bit index rejects; legal indices 0,…,ell−1 represent 1,…,ell.
-/
def checkResponseBlock (I : SSLBInstance) (a : ProtocolParameters)
    (r w : Bits) (i : ℕ) : Bool :=
  let start := a.ell * a.R + i * a.blockResponse I.witness
  let j := bitsNat (slice w start a.h)
  let s := slice w (start + a.h) a.N
  let rho := (List.range a.R).map (fun q =>
    Bool.xor (r.getD (i * a.R + q) false) (w.getD (j * a.R + q) false))
  decide (j < a.ell) &&
    (List.range a.k).all (fun row => dotRow a rho s row == rho.getD (a.k * a.N + row) false) &&
    (List.range a.d).all (fun u =>
      let object := slice s (u * I.n) I.n
      let witness := slice w (start + a.h + a.N + u * I.witness) I.witness
      (I.membership.eval (object ++ witness)).getD 0 false)

/-- A single length polynomial bounds both raw messages and makes lengths depend
only on the full encoded input length. Extra random and response bits are ignored.
-/
def protocolBound (L : ℕ) : ℕ := 4000000 * (L + 1) ^ 12

noncomputable def protocolLength : LengthPolynomial where
  polynomial := Polynomial.C 4000000 * (Polynomial.X + 1) ^ 12
  value := protocolBound
  spec := by
    intro n
    simp [protocolBound]

def protocolAccept (x r w : Bits) : Bool :=
  if r.length = protocolBound x.length ∧ w.length = protocolBound x.length then
    match decodeSSLB x with
    | none => false
    | some I =>
      if 4 * I.threshold ≤ 2 ^ I.n then
        let a := parameters I
        if a.rawRandom ≤ r.length ∧ a.rawResponse I.witness ≤ w.length then
          (List.range a.t).all (checkResponseBlock I a r w)
        else false
      else false
  else false

/-- One named verifier is used in both source theorems. No correctness or runtime
property is stored as a field: these are precisely the content of Theorem 3.3. -/
noncomputable def sslbVerifier : AMVerifier where
  random := protocolLength
  response := protocolLength
  run := protocolAccept

end AMRangeAvoid.Characterization


