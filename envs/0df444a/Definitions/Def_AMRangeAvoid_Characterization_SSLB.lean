-- Prove2me | Definitions.Def_AMRangeAvoid_Characterization_SSLB
-- name    : AMRangeAvoid_Characterization_SSLB
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-08T10:59:40.946248+00:00
-- url     : https://prove2.me/theorems/d54a7104-f7c9-498f-9336-fe47a3a03d7a
-- title:
--   Structured Set Lower Bound and its two promised sides
-- statement:
--   An SSLB instance encodes a positive binary threshold $\tau$, object width $n$, witness width $b$, a single-output membership circuit $P$ on $n+b$ bits, and a structure circuit $C$ on $\lceil\log_2\tau\rceil$ bits with $n$ outputs. Its set is constructed as
--   $$S=\{s\in\{0,1\}^n:\exists w\in\{0,1\}^b,\ P(s,w)=1\}.$$
--   The YES promise is $|S|\ge4\tau$. The NO promise is $|S|\le\tau$ and $S\subseteq\operatorname{Im}(C)$. The structure circuit need not output only elements of $S$ and need not be injective. Invalid codes and gap inputs are unpromised; the positive threshold makes the two sides disjoint. Input arities and output wires are explicit, so the witness width and all code-processing costs are bounded by the full description length. This is the structured problem, retaining the exact factor four and the exact binary cover domain.
-- source:
--   Zeyong Li, STOC 2027 submission #502 (October 2026), Definition 3.1, printed p.14 (PDF p.16); https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/502.pdf

import Definitions.Def_AMRangeAvoid_Characterization_Computation

/-! Structured Set Lower Bound, Li, STOC 2027 submission #502,
Definition 3.1, printed p.14 (PDF p.16). Gap inputs and invalid codes are
unpromised. The structure circuit's image condition occurs only on the NO side.
-/
namespace AMRangeAvoid.Characterization

structure SSLBInstance where
  n : ℕ
  witness : ℕ
  threshold : ℕ
  membership : Circuit
  cover : Circuit
  deriving DecidableEq, Repr, Inhabited

def SSLBInstance.valid (I : SSLBInstance) : Bool :=
  decide (0 < I.threshold ∧ I.membership.inputs = I.n + I.witness ∧
    I.membership.outputs.length = 1 ∧ I.cover.inputs = ceilLog2 I.threshold ∧
    I.cover.outputs.length = I.n) && I.membership.valid && I.cover.valid

def SSLBInstance.code (I : SSLBInstance) : Bits :=
  natCode I.n ++ natCode I.witness ++ natCode I.threshold ++
    I.membership.code ++ I.cover.code

def decodeSSLB (b : Bits) : Option SSLBInstance := do
  let (n, rest) ← readNat b
  let (w, rest) ← readNat rest
  let (τ, rest) ← readNat rest
  let (P, rest) ← readCircuit rest
  let (C, rest) ← readCircuit rest
  let I : SSLBInstance := ⟨n, w, τ, P, C⟩
  if rest = [] ∧ I.valid = true then pure I else none

/-- The set is built from the actual membership circuit, not supplied as data. -/
def SSLBInstance.elements (I : SSLBInstance) : Finset (Word I.n) :=
  Finset.univ.filter (fun s => ∃ w : Word I.witness,
    (I.membership.eval (wordBits s ++ wordBits w)).getD 0 false = true)

def SSLBYes : Set Bits := {b |
  ∃ I, decodeSSLB b = some I ∧ 0 < I.threshold ∧ 4 * I.threshold ≤ I.elements.card}

def SSLBNo : Set Bits := {b |
  ∃ I, decodeSSLB b = some I ∧ 0 < I.threshold ∧ I.elements.card ≤ I.threshold ∧
    ∀ s ∈ I.elements, wordBits s ∈ I.cover.image}

/-- The two promised sides are disjoint because the positive threshold has gap four. -/
def SSLB : PromiseProblem where
  yes := SSLBYes
  no := SSLBNo
  disjoint := by
    rw [Set.disjoint_left]
    rintro x ⟨I, hi, hp, hy⟩ ⟨J, hj, _, hn, _⟩
    have e : I = J := Option.some.inj (hi.symm.trans hj)
    subst J
    omega

end AMRangeAvoid.Characterization


