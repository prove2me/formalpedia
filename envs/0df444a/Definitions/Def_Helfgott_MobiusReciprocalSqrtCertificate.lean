-- Prove2me | Definitions.Def_Helfgott_MobiusReciprocalSqrtCertificate
-- name    : Helfgott_MobiusReciprocalSqrtCertificate
-- status  : Definition
-- author  : @raresbuhai
-- created : 2026-10-09T04:20:02.861355+00:00
-- url     : https://prove2.me/theorems/fee2adea-a295-4fe5-b186-7dd33f02466e
-- title:
--   Kernel-checkable square-root reciprocal Mobius certificate
-- statement:
--   Pure Boolean scan and balanced-tree definitions for an exact finite reciprocal Mobius square-root certificate. At scale Q the scan checks (abs(rounded prefix)+n)^2*(n+1)<=2*Q^2 for n>=2, and all start/end prefix transitions. There is no correctness assertion; separate proofs establish scan soundness and each numerical interval. Written by Codex.
-- source:
--   Original kernel-checkable certificate definitions reusing the published immutable reciprocal table data. Written by Codex.

import Definitions.Def_Helfgott_MobiusReciprocalCertificate
set_option autoImplicit false
namespace Helfgott

def mobiusReciprocalSqrtScan (g : ℕ → ℤ) (Q B : ℕ) : ℕ → ℕ → ℤ → Bool × ℤ
  | 0, _, s => (true, s)
  | fuel+1, n, s =>
      if n < B then
        let next := s+g n*(Q/n : ℕ)
        let own := if 2 ≤ n then decide ((next.natAbs+n)^2*(n+1) ≤ 2*Q^2) else true
        let rest := mobiusReciprocalSqrtScan g Q B fuel (n+1) next
        (own && rest.1, rest.2)
      else (true,s)

def mobiusReciprocalSqrtLeafCheck (g : ℕ → ℤ) (Q B offset : ℕ) (start finish : ℤ) : Bool :=
  let scan := mobiusReciprocalSqrtScan g Q B 32 offset start
  scan.1 && (scan.2 == finish)

def mobiusReciprocalSqrtTreeCheck (g : ℕ → ℤ) (Q B : ℕ) : ℕ → ℕ → MobiusReciprocalTree → Bool
  | d, offset, tree =>
      if B ≤ offset then mobiusReciprocalStart tree == mobiusReciprocalFinish tree else
      match d,tree with
      | 0,.leaf start finish _ _ => mobiusReciprocalSqrtLeafCheck g Q B offset start finish
      | d+1,.branch l r =>
          mobiusReciprocalSqrtTreeCheck g Q B d offset l &&
          mobiusReciprocalSqrtTreeCheck g Q B d (offset+32*2^d) r &&
          (mobiusReciprocalFinish l == mobiusReciprocalStart r)
      | _,_ => false
end Helfgott


