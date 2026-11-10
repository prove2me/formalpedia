-- Prove2me | Definitions.Def_QuantumWork1289_Metering_construction
-- name    : QuantumWork1289_Metering_construction
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-10T04:37:37.447199+00:00
-- url     : https://prove2.me/theorems/53a70ef4-a9d9-4364-86c4-e0d80f7de4d0
-- title:
--   Construction 2 parameters, proof parser and checker
-- statement:
--   Let $\lambda\ge1$ be the security parameter and $a>0$ the fixed difficulty constant. The public setup includes a polynomially bounded nonce-length function $\rho$ satisfying $\rho(\lambda)\ge d_{\max}(\lambda)+\lambda+4$, where
--
--   $$d_{\max}(\lambda)=\min\{\lambda,\lfloor a\log_2\lambda\rfloor\},\qquad\Lambda_d=\lambda+2^d.$$
--
--   A code family supplies its finite alphabet size, block length, actual Boolean membership test and public description. At parameter $\Lambda_d$ write $N_d$ for the block length and $\Sigma_d$ for the alphabet. The description is a fixed string associated with the family; the code is not represented by a codeword enumeration.
--
--   Public parameters serialize $(1^\lambda,\rho,d_{\max},\operatorname{desc}(\mathcal C))$. Length framing gives unambiguous encodings of $(pp,prev,tx,d,r,i,\sigma)$. A raw proof must contain exactly $\rho$ nonce bits followed by $N_d$ symbols of width $\lceil\log_2|\Sigma_d|\rceil$. The parser rejects wrong lengths, trailing data and out-of-alphabet symbols. For the parsed $(r,w)$, the checker rejects an invalid difficulty and accepts exactly when
--
--   $$w\in\mathcal C_d\quad\text{and}\quad\operatorname{first}(H_{qz}(pp,prev,tx,d,r,i,w_i))=0\quad(1\le i\le N_d).$$
--
--   The oracle still returns all $\lambda$ bits to the miner. Abort and malformed proofs reject. There is no selector target or prefix search. This defines the actual acceptance event used by the goal. The family interface does not contain a solver, hardness premise, list-recovery certificate or success inequality; list recovery is a separate theorem hypothesis.
-- source:
--   Mohammed Barhoush, Proof of Quantum Work with Classical Verification, STOC 2027 submission #1289 (October 2026), p. 11, §3.1; p. 18, Definition 6; p. 23, Construction 2, Eqs. (9)–(12)

import Mathlib
import Definitions.Def_QuantumWork1289_Metering_listRecovery
set_option autoImplicit false

namespace QuantumWork1289.Metering

abbrev Bits := List Bool
abbrev OracleAnswer (security : ℕ) := Fin security → Bool

/-- A finite-alphabet code family, with a fixed public description and actual membership test.
No hardness, solver, candidate-count bound or success estimate is a field. -/
structure CodeFamily where
  alphabetSize : ℕ → ℕ
  length : ℕ → ℕ
  member : (k : ℕ) → (Fin (length k) → Fin (alphabetSize k)) → Bool
  description : Bits

/-- The actual code at parameter k, as a set rather than a supplied counting certificate. -/
def familyCode (F : CodeFamily) (k : ℕ) : Set (Fin (F.length k) → Fin (F.alphabetSize k)) :=
  {w | F.member k w = true}

/-- Section 3.1 difficulty range; security=1 and d=0 are permitted. -/
noncomputable def maxDifficulty (security : ℕ) (a : ℝ) : ℕ :=
  min security ⌊a * Real.logb 2 (security : ℝ)⌋₊

/-- Global public parameters, including the polynomially bounded nonce-length function.
This bound is global in security; the theorem's fixed instance does not choose its exponent. -/
structure Setup where
  security : ℕ
  positiveSecurity : 0 < security
  a : ℝ
  positiveScale : 0 < a
  nonceLength : ℕ → ℕ
  polynomialNonce : ∃ b k : ℕ, ∀ l, nonceLength l ≤ b * (l + 1) ^ k
  nonceRoom : ∀ l, 0 < l → maxDifficulty l a + l + 4 ≤ nonceLength l

/-- The exact family parameter Λ_d = security + 2^d. -/
def codeParameter (p : Setup) (d : ℕ) : ℕ := p.security + 2 ^ d

/-- Self-delimiting framing for strings: unary length followed by the payload. -/
def frame (s : Bits) : Bits := List.replicate s.length true ++ false :: s

def pack (ss : List Bits) : Bits := ss.flatMap frame

/-- Gen's serialized public string (1^security, ρ, d_max, desc(C)). -/
noncomputable def publicParameters (p : Setup) (F : CodeFamily) : Bits :=
  pack [List.replicate p.security true, (p.nonceLength p.security).bits,
    (maxDifficulty p.security p.a).bits, F.description]

/-- The source leaves tuple framing unspecified. Every component is framed; natural numbers
use canonical binary, and coordinates use the paper's one-based numbering. -/
noncomputable def puzzleAddress (p : Setup) (F : CodeFamily) (prev tx : Bits)
    (d : ℕ) (r : Bits) (i σ : ℕ) : Bits :=
  pack [publicParameters p F, prev, tx, d.bits, r, (i + 1).bits, σ.bits]

/-- Little-endian binary decoding; no default on an out-of-range symbol. -/
def bitsValue : Bits → ℕ
  | [] => 0
  | b :: bs => (if b then 1 else 0) + 2 * bitsValue bs

/-- Fixed-width proof parser: exactly ρ nonce bits and N symbols of ceil(log₂|Σ|) bits.
Trailing material and out-of-alphabet binary values reject. -/
noncomputable def parseProof (ρ N s : ℕ) (raw : Bits) :
    Option (Bits × (Fin N → Fin s)) := by
  classical
  let width := Nat.clog 2 s
  let value := fun i : Fin N => bitsValue ((raw.drop (ρ + i.val * width)).take width)
  exact if raw.length = ρ + N * width then
    if h : ∀ i, value i < s then
      some (raw.take ρ, fun i => ⟨value i, h i⟩)
    else none
  else none

/-- Construction 2's full deterministic checker, including actual parsing, membership and
all N first-bit tests of the security-bit random oracle. Abort and malformed proofs reject. -/
noncomputable def checker (p : Setup) (F : CodeFamily) (prev tx : Bits)
    (d : ℕ) (H : Bits → OracleAnswer p.security) (π : Option Bits) : Prop :=
  d ≤ maxDifficulty p.security p.a ∧ match π with
  | none => False
  | some raw => match parseProof (p.nonceLength p.security) (F.length (codeParameter p d))
      (F.alphabetSize (codeParameter p d)) raw with
    | none => False
    | some (r, w) => F.member (codeParameter p d) w = true ∧
        ∀ i, H (puzzleAddress p F prev tx d r i.val (w i).val)
          ⟨0, p.positiveSecurity⟩ = false

end QuantumWork1289.Metering


