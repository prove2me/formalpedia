-- Prove2me | Definitions.Def_AvoidPlast_Supplement_InNP
-- name    : AvoidPlast_Supplement_InNP
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T08:49:20.132208+00:00
-- url     : https://prove2.me/theorems/c86bc527-c81e-48e2-aa2f-6737a19f354b
-- title:
--   The class NP
-- statement:
--   $L\in\mathsf{NP}$ if $L\in\mathrm{NTIME}[n^k]$ for some $k$: a deterministic verifier reading $x$ and a witness $w$ with $|w|\le C(n^k+1)$ runs in time $C(n^k+1)$, and $x\in L$ iff some such $w$ is accepted.
-- source:
--   Li–Tell, Trading Time, Space, and Alternations: General Plasticity for Algorithms from Hardness of Range Avoidance, STOC 2027 submission (manuscript sha256 e1ff3a9e…), Theorem 6.1, p.31

import Mathlib
import Definitions.Def_AvoidPlast_IsNTimeVerifier
import Definitions.Def_AvoidPlast_Machine

namespace AvoidPlast.Supplement

open AvoidPlast

/-- The class NP (Li–Tell, *Trading Time, Space, and Alternations: General Plasticity for Algorithms from Hardness of Range Avoidance*, STOC 2027 submission manuscript (sha256 e1ff3a9e…d6728), Theorem 6.1, p.31): `L ∈ NTIME[n^k]` for some `k`, with the base
verifier notion `IsNTimeVerifier`. -/
def InNP (L : Set (List Bool)) : Prop :=
  ∃ (V : Machine 2) (k C : ℕ), IsNTimeVerifier V L (fun n => n ^ k) C

end AvoidPlast.Supplement


