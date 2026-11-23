-- Prove2me | Definitions.Def_ITPIRPreproc_MatchVec_IndexedVectorComputation
-- name    : ITPIRPreproc_MatchVec_IndexedVectorComputation
-- status  : Definition
-- author  : @Mr Robbins
-- created : 2026-11-23T02:37:28.882841+00:00
-- url     : https://prove2.me/theorems/cf9393ab-19cd-4a14-b3c0-7871adb84772
-- title:
--   Indexed matching-vector computation with linear workspace
-- statement:
--   For a family of $m=2^h$ pairs of matching vectors of dimension $d$, an indexed-vector computation is a deterministic word-RAM program that, on the self-delimiting encodings of $h$ and a row index $a$, halts with the three-bit-per-entry encodings of $u_a$ and $v_a$. Its work is at most $C_0dh^{c_0}$ and its working storage is at most $C_0d$.
--
--   This interface separates the paper’s per-entry construction from the whole-table construction. The workspace statement is essential because invoking an indexed computation repeatedly with an accumulating table is allowed, but allocating a fresh $O(md)$ buffer for every invocation would violate the paper’s linear table-storage bound.
-- source:
--   Dujmovic–Lai–Wichs, Nearly Optimal Information-Theoretic PIR with Client Preprocessing, STOC 2027 submission #572, Appendix A, printed pp.35–37 (PDF pp.37–39); interface for the final sentence “each vector computable from its row index in d poly(h) time.”

import Definitions.Def_ITPIRPreproc_MatchVec_MatchingVectors

namespace ITPIRPreproc.MatchVec

open WordRAM

/-- One indexed pair of matching vectors is computed with temporary storage linear in the
vector dimension. This is the per-row half of `MVComputable`, together with the storage bound
needed when the same program is invoked repeatedly to build a table. -/
def IndexedVectorComputable (dim : ℕ → ℕ)
    (u v : ∀ h : ℕ, Fin (2 ^ h) → Fin (dim h) → ZMod 6)
    (C₀ : ℝ) (c₀ : ℕ) (vecProg : Program) : Prop :=
  Deterministic vecProg ∧
  ∀ h : ℕ, 3 ≤ h → ∀ a : Fin (2 ^ h),
    Halts vecProg (encNat h ++ encNat a.val) zeroTape ∧
    output vecProg (encNat h ++ encNat a.val) zeroTape =
      encZ6Vec (u h a) ++ encZ6Vec (v h a) ∧
    (cost vecProg (encNat h ++ encNat a.val) zeroTape : ℝ) ≤
      C₀ * dim h * (h : ℝ) ^ c₀ ∧
    (workingBits vecProg (encNat h ++ encNat a.val) zeroTape : ℝ) ≤ C₀ * dim h

end ITPIRPreproc.MatchVec


