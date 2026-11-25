-- Prove2me | Definitions.Def_DetDLP_D4GuardWeight
-- name    : DetDLP_D4GuardWeight
-- status  : Definition
-- author  : @Bingsheng
-- created : 2026-11-24T08:54:24.650587+00:00
-- url     : https://prove2.me/theorems/ad54c0e2-933b-4a31-b51e-70544c76bca5
-- title:
--   Dyadically padded branch weights with a depth-local uniform allowance
-- statement:
--   The branch weight uses a common per-site allowance. It lifts the proved quotient of each Hermite weight before multiplying by the missing dyadic power. The uniform allowance only uses the shift at the final depth.

import Definitions.Def_DetDLP_D4GuardTree
set_option autoImplicit false
namespace DetDLP.D4GuardTree
open Polynomial AppendixD4 ResidualScalarOracle
/-- Uniform allowance for all steps up to the indicated absolute depth. -/
def localAllowance (S D : ℕ) := 40*(S+1)*(D3Stopped.shift S D+1)*2^(D3Stopped.shift S D)
def totalGuard (S D : ℕ) := localAllowance S D*64^D
namespace Expansion
variable {S : ℕ} {f : ℤ[X]} {hf : f.Monic} {l : ℕ}
/-- The normalized branch coefficient with common per-node allowance A. The missing-node
allowance in an early leaf makes every expanded product have the same dyadic budget. -/
noncomputable def paddedWeight (A : ℕ) : {d k p : ℕ} → {z : B f l p} → (e : Expansion S f hf l d k p z) → e.Ranks → IntJet f l
  | _,_,_,_,.leaf (k:=k) _, _ => 2^(A*slots k)
  | _,_,_,_,.step (G:=G) (d:=d) s _ _ _ _ _ next, r =>
    let ν := r.1; let a := D3Stopped.shift S d; let u := D3Stopped.width S d
    2^(A-loss G.nE a u (AppendixD4.level ν.1.val)) * repr hf (AdjoinRoot.of _ (quotient s ν) : B f l _) * ∏ g, paddedWeight A (next ν g) (r.2 g)
end Expansion
end DetDLP.D4GuardTree


