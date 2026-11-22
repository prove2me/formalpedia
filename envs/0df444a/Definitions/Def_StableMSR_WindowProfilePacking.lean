-- Prove2me | Definitions.Def_StableMSR_WindowProfilePacking
-- name    : StableMSR_WindowProfilePacking
-- status  : Definition
-- author  : @lreyzin
-- created : 2026-11-22T21:56:22.30911+00:00
-- url     : https://prove2.me/theorems/c4c7b3ec-1db9-48ba-bf87-d89a74c3aeda
-- title:
--   Rectangular encoding of exact-count convolution as an acyclic ball table
-- statement:
--   Mixed-radix state and edge numbers encode the scenario, region stage, old count and new count. A synchronous table conversion reads local endpoint witnesses, shifts their slots, and supplies parent, destination and width fields for the verified path optimizer.
-- source:
--   Exact Sum-of-Radii Clustering under Any Constant Stability, arXiv:2611.03547, Sections 4.1–4.4 and Appendices A.4–A.6. Exact-count combination over disjoint regions in the mission’s real-distance RAM model.

import Definitions.Def_StableMSR_WindowProfiles
open scoped Classical
set_option autoImplicit false
open StableMSR.Recovery StableMSR.Recovery.OracleQueries StableMSR.Recovery.Compiler
open StableMSR.Recovery.BallCoverCatalog
namespace StableMSR.Recovery.WindowProfiles
def subR (x : World) (a b : ℕ) := ∑t∈Finset.range x.rows,if b+t=a then t else 0
def divN (x : World) (a : ℕ) := ∑t∈Finset.range x.rows,if t*x.n≤ a ∧ a<(t+1)*x.n then t else 0
def remN (x : World) (a : ℕ) := subR x a (divN x a*x.n)
def dim (x : World) := capacity (x.mem 0).toNat x.n
def dataWord (x : World) (z j : ℕ) (side : Bool) : ℤ :=
  let v:=divN x z; let t:=divN x v
  let a:=remN x v; let b:=remN x z
  RegionalBallDP.field x (index x.n (divN x t) (remN x t) (subR x b a)) (subR x j a) side
noncomputable def edgeField (x : World) (z : ℕ) (side : Bool) : ℤ :=
  let v:=divN x z; let t:=divN x v
  let u:=divN x t; let i:=remN x t; let a:=remN x v; let b:=remN x z
  if u<(x.mem 0).toNat ∧ a≤ b ∧ b≤ x.k ∧ (i=0 → a=0) ∧ active x u i (subR x b a) then
    if side then (node x.n u i b:ℤ) else (if i=0 then 1 else node x.n u (i-1) a:ℕ)
  else 0
noncomputable def packed (x : World) (r j : ℕ) (side : Bool) : ℤ :=
  let M:=dim x
  if r=0 then (M:ℤ) else if r≤ M then 0 else if r≤ M+M then dataWord x (subR x r (M+2)) j side
  else if r≤ M+M+M then (remN x (subR x r (M+M+2)):ℤ)
  else if M+M+M+2≤ r then edgeField x (subR x r (M+M+M+2)) side else 0
end StableMSR.Recovery.WindowProfiles


