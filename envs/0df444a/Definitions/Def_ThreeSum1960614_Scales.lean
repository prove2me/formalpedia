-- Prove2me | Definitions.Def_ThreeSum1960614_Scales
-- name    : ThreeSum1960614_Scales
-- status  : Definition
-- author  : @Yuxuan Xu
-- created : 2026-10-14T07:24:22.16142+00:00
-- url     : https://prove2.me/theorems/d2377ac7-f0fd-4597-8c1c-96778b335178
-- title:
--   Executable rational block and band schedules for the quartic 3SUM parameters
-- statement:
--   For an input size $n$, let $m=\lfloor\log_2 n\rfloor$. The even microblock size is $s(m)=2\lfloor\lfloor m^{1/3}\rfloor/2\rfloor$. The number of blocks is $J(m)=20\lfloor e m/(20s(m))\rfloor$ with the exact rational $e=0.203889696$, and the total size is $\mu(m)=J(m)s(m)$. The band divisor is $2^{\lfloor-b\mu(m)\rfloor}$ with $b=-0.062656016$. All functions use natural-number integer arithmetic, including integer cube root and quotients. At $s(m)=0$, the totalized natural quotient returns zero, so $J(m)=\mu(m)=0$ and the divisor is one. The complete solver must supply its exceptional-size fallback. These functions specify the executable schedule; correctness and resource costs of the full 3SUM program are separate theorem obligations.
-- source:
--   User-supplied 3sum_certificate_1p960614_v3/3sum_certificate_v3/PROOF.md, Section 4.1, 14 October 2026; even microblock inherited from c0ldzy17/three-sum-lean@2b639655e07421b9ac743de9090459bab473a7c0, Submission/ThreeSum/Scales.lean.

import Definitions.Def_ThreeSum1960614_Analysis

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
Executable natural-number schedules from PROOF.md, Section 4.1.
The even microblock construction follows c0ldzy17/three-sum-lean,
Submission/ThreeSum/Scales.lean at commit
2b639655e07421b9ac743de9090459bab473a7c0 (Apache-2.0).
These definitions describe the changed schedule; their integration into
the complete Light/word-RAM solver is a separate obligation.
-/

namespace ThreeSum1960614.Schedule

def inputBits (n : ℕ) : ℕ := Nat.log2 n

def microSize (m : ℕ) : ℕ := 2 * (Nat.nthRoot 3 m / 2)

def blockCount (m : ℕ) : ℕ :=
  20 * (203889696 * m / (20000000000 * microSize m))

def totalSize (m : ℕ) : ℕ := blockCount m * microSize m

def bandExponent (m : ℕ) : ℕ := 62656016 * totalSize m / 1000000000

def bandDivisor (m : ℕ) : ℕ := 2 ^ bandExponent m

end ThreeSum1960614.Schedule


