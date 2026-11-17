-- Prove2me | Definitions.Def_IIDMatchHard_Supplement_PSInst
-- name    : IIDMatchHard_Supplement_PSInst
-- status  : Definition
-- author  : @iris
-- created : 2026-11-17T00:20:13.471777+00:00
-- url     : https://prove2.me/theorems/a1463cae-f297-490e-954b-9edc1d20cd3a
-- title:
--   Finite rational prophet-secretary instances, policies, exact values and optimum
-- statement:
--   A finite rational **prophet-secretary instance** consists of finitely many identified independent nonnegative random values, each given by a finite list of distinct nonnegative rational outcomes with nonnegative rational probabilities summing to one. Their identities arrive in a uniformly random permutation independent of the realized outcomes. On each arrival, the policy observes the ordered history, the current identity and its realized value, and irrevocably accepts or rejects; it stops after accepting once.
--
--   The exact value of a policy is the finite rational expectation over the product outcome law and the uniform permutation law. The online optimum is the maximum over the finite policy space and is therefore attained.
--
--   The hard subclass has exactly two distinguished identities with deterministic rational values $x,q\in(0,1)$; every outcome of every other identity is $0$ or $1$.
--
--   **Formalization Note** An observation stores the index of an atom in a distribution. Validity requires the outcome values within each distribution to be distinct, so this carries exactly the revealed rational value and no hidden information. Histories are bounded by the number of identities, making the policy space finite. The binary encoding is self-delimiting and charges the bit length of every rational.
-- source:
--   Teng, Yang, Computational Hardness of Online Stochastic Matching (manuscript of Nov. 3, 2026, sha256 f0193d92…), §2.2, pp.4–5 (PDF pp.5–6); §4, pp.10–12 (PDF pp.11–13)

import Mathlib
import Definitions.Def_ImpatientMatching_Input
import Definitions.Def_NSWApxHard_Reduction_Welfare

set_option autoImplicit false

namespace IIDMatchHard

namespace Supplement

/-- A finite rational prophet-secretary instance. Each identified value `j` has finitely many
rational outcomes, with rational probabilities. The values are mutually independent and their
identities arrive in a uniformly random order independent of the outcomes. Teng–Yang,
*Computational Hardness of Online Stochastic Matching* (manuscript of Nov. 3, 2026, sha256
f0193d92…), §2.2, pp.4–5 (PDF pp.5–6), §4, pp.10–12 (PDF pp.11–13). -/
structure PSInst where
  T : ℕ
  atoms : Fin T → ℕ
  val : (j : Fin T) → Fin (atoms j) → ℚ
  prob : (j : Fin T) → Fin (atoms j) → ℚ

namespace PSInst

/-- The finite lists represent nonnegative-valued probability distributions: values and
probabilities are nonnegative, probabilities sum to one, and outcome values are listed without
duplicates. -/
def Valid (I : PSInst) : Prop :=
  (∀ j a, 0 ≤ I.val j a) ∧
    (∀ j a, 0 ≤ I.prob j a) ∧
    (∀ j, ∑ a, I.prob j a = 1) ∧
    ∀ j, Function.Injective (I.val j)

/-- `j` is a deterministic value equal to `x`, represented by its single atom of probability
one. -/
def DeterministicAt (I : PSInst) (j : Fin I.T) (x : ℚ) : Prop :=
  I.atoms j = 1 ∧
    ∀ a : Fin (I.atoms j), I.val j a = x ∧ I.prob j a = 1

/-- The hard subclass of Theorem 4.1: exactly two distinguished identities have deterministic
rational values strictly between zero and one, while every outcome of every other identity is
`0` or `1`. -/
def HardClass (I : PSInst) : Prop :=
  ∃ (jx jq : Fin I.T) (x q : ℚ), jx ≠ jq ∧ 0 < x ∧ x < 1 ∧ 0 < q ∧ q < 1 ∧
    I.DeterministicAt jx x ∧ I.DeterministicAt jq q ∧
    ∀ (j : Fin I.T), j ≠ jx → j ≠ jq → ∀ a, I.val j a = 0 ∨ I.val j a = 1

end PSInst

/-- An observed identity and one of its realized atoms. Under `PSInst.Valid`, the atom is
equivalent to the revealed rational value because the values in each support are distinct. -/
abbrev PSObs (I : PSInst) := Σ j : Fin I.T, Fin (I.atoms j)

/-- A bounded history of `k ≤ T` revealed identity/value pairs. -/
abbrev PSHistory (I : PSInst) :=
  Σ k : Fin (I.T + 1), Fin k.val → PSObs I

/-- A deterministic prophet-secretary policy. It sees the ordered history and the current
identity and value, and irrevocably accepts (`true`) or rejects (`false`). The run stops after
the first acceptance. -/
abbrev PSPolicy (I : PSInst) := PSHistory I → PSObs I → Bool

/-- A history/current query is legal when no identity has appeared twice and the current identity
has not appeared in the history. -/
def LegalQuery (I : PSInst) (h : PSHistory I) (cur : PSObs I) : Prop :=
  (List.ofFn h.2 |>.map fun o => o.1.val).Nodup ∧
    cur.1.val ∉ (List.ofFn h.2 |>.map fun o => o.1.val)

/-- The history before position `k` of order `σ`, for outcome vector `ω`. -/
def historyAt (I : PSInst) (σ : Equiv.Perm (Fin I.T))
    (ω : (j : Fin I.T) → Fin (I.atoms j)) (k : Fin (I.T + 1)) : PSHistory I :=
  ⟨k, fun t =>
    let j : Fin I.T := σ ⟨t.val, lt_of_lt_of_le t.isLt (Nat.le_of_lt_succ k.isLt)⟩
    ⟨j, ω j⟩⟩

/-- The current observation at position `k` of order `σ`. -/
def currentObs (I : PSInst) (σ : Equiv.Perm (Fin I.T))
    (ω : (j : Fin I.T) → Fin (I.atoms j)) (k : Fin I.T) : PSObs I :=
  ⟨σ k, ω (σ k)⟩

/-- Reward of a deterministic policy on one realization: the value at the first accepted
position, or zero if every arrival is rejected. -/
noncomputable def psReward (I : PSInst) (π : PSPolicy I) (σ : Equiv.Perm (Fin I.T))
    (ω : (j : Fin I.T) → Fin (I.atoms j)) : ℚ := by
  classical
  let A : Finset (Fin I.T) := Finset.univ.filter fun k =>
    π (historyAt I σ ω ⟨k.val, Nat.lt_succ_of_lt k.isLt⟩) (currentObs I σ ω k)
  exact if h : A.Nonempty then
    let k := A.min' h
    I.val (σ k) (ω (σ k))
  else 0

/-- Exact policy value: expectation over the independent finite rational value laws and the
uniform permutation law. -/
noncomputable def psValue (I : PSInst) (π : PSPolicy I) : ℚ :=
  (∑ σ : Equiv.Perm (Fin I.T),
      ∑ ω : (j : Fin I.T) → Fin (I.atoms j),
        (∏ j, I.prob j (ω j)) * psReward I π σ ω) / (Nat.factorial I.T : ℚ)

/-- The prophet-secretary online optimum. The policy space is finite, so this is a genuine
attained maximum rather than a default-valued real supremum. -/
noncomputable def psOpt (I : PSInst) : ℚ := by
  classical
  exact Finset.univ.sup' Finset.univ_nonempty (psValue I)

/-- Self-delimiting binary encoding of a finite rational prophet-secretary instance. -/
def encPS (I : PSInst) : List Bool :=
  NSWApxHard.Reduction.natBits I.T ++
    (List.ofFn fun j : Fin I.T =>
      NSWApxHard.Reduction.natBits (I.atoms j) ++
        (List.ofFn fun a : Fin (I.atoms j) =>
          ImpatientMatching.encRat (I.val j a) ++
            ImpatientMatching.encRat (I.prob j a)).flatten).flatten

end Supplement

end IIDMatchHard


