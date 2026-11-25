-- Prove2me | Definitions.Def_DetDLP_D4BOuterInvariant
-- name    : DetDLP_D4BOuterInvariant
-- status  : Definition
-- author  : @Bingsheng
-- created : 2026-11-24T08:38:15.772661+00:00
-- url     : https://prove2.me/theorems/7857b073-3dbd-442f-b6e9-6308677798c2
-- title:
--   Typed states and bounded oracle interface for the outer cursor
-- statement:
--   Typed header, branch and digit states, coefficient-prefix sums, and the oracle reply and word-length obligations for a bounded run of the outer scalar cursor.
-- source:
--   Controller and run invariant for DetDLP.d4_outer_scalar_cursor_machine_v2 (dc44082d-fc56-402c-8efa-dc7eda4aebd8).

import Definitions.Def_DetDLP_D4BOuterStep
import Definitions.Def_DetDLP_D4Transcript
set_option autoImplicit false
namespace DetDLP.D4BOuter
open D4BEntry D4Plan D4Slice DetDLP_W1_Queries AppendixD4 ResidualScalarOracle Polynomial
open OAI.Algorithms.SubexponentialSAT OAI.Algorithms.SubexponentialSAT.Computation OAI.Algorithms.SubexponentialSAT.SqrtLogSpace
variable {C c : ℕ} {x : Input C c}
noncomputable section
abbrev qprec (P : Plan x) := P.guard + x.p
noncomputable def ctxWord (P : Plan x) := Encoding.encodeList id [input x,header P,
  (2^qprec P : ℕ).bits,(2^P.guard : ℕ).bits,List.replicate x.l true,
  List.replicate P.f.natDegree true,encodeNatListBin (fCoeffs P.f (qprec P)),
  residue P.f x.l (qprec P) P.hf 0]
noncomputable abbrev enc (P : Plan x) := residue P.f x.l (qprec P) P.hf
def vecWord {n J : ℕ} (a : Fin n → Fin J) := encodeNatListBin (List.ofFn fun v => (a v).val)
def digitsOf {n J : ℕ} (a : Fin n → Fin J) := List.ofFn fun i => (a i).val
abbrev Vect (P : Plan x) (u : Fin P.N) := Fin (P.R u).nV → Fin (J P u)
abbrev Res (P : Plan x) := B P.f x.l (qprec P)
def zvec (P : Plan x) (u : Fin P.N) : Vect P u := fun _ => ⟨0,Nat.succ_pos _⟩
def brState (P : Plan x) (u : Fin P.N) (s : Res P) := listWord [countWord 2,ctxWord P,enc P s,countWord u.val]
def dgState (P : Plan x) (u : Fin P.N) (a : Vect P u) (s t : Res P) :=
  listWord [countWord 3,ctxWord P,enc P s,countWord u.val,branch P u,vecWord a,enc P t]
def dgQuery (P : Plan x) (u : Fin P.N) (a : Vect P u) := encodeBTNInstance (digitDesc P u a) (P.R u) x.b
  (precision P.f x.l (P.R u) (h P u) (4*x.m*x.k)) (spacing P.f (P.R u)*x.l)
abbrev DigitsData (P : Plan x) := (u : Fin P.N) → Vect P u → Fin (spacing P.f (P.R u)*x.l) → ℕ
def dgAns (P : Plan x) (v : DigitsData P) (u : Fin P.N) (a : Vect P u) := encodeNatListBin (List.ofFn (v u a))
def summand (P : Plan x) (v : DigitsData P) (u : Fin P.N) (a : Vect P u) :=
  unpackTerm P.f x.l (qprec P) (P.R u) (h P u) a (v u a)
def prefixSum {R : Type} [AddCommMonoid R] {n : ℕ} (f : Fin n → R) (k : ℕ) :=
  ∑ i : Fin n, if i.val < k then f i else 0
def inside (P : Plan x) (v : DigitsData P) (u : Fin P.N) := prefixSum (fun i => summand P v u (finFunctionFinEquiv.symm i))
def outside (P : Plan x) := prefixSum (fun u => P.w u * BTNContract (P.R u) (P.V u))
def tagWord (tag : ℕ) (q : Bits) := if tag=0 then false::q else true::decide (tag=2)::q
structure Call (O : PrimitiveMachine) (o : Fin O.tapeCount) (τ σ : ℝ) (H : ℕ) (st : Bits) (tag : ℕ) (q y : Bits) : Prop where
  run : RunsWithin O o (tagWord tag q) y τ σ
  queryCap : (pair st (tagWord tag q)).length ≤ H
  pairCap : (pair st y).length ≤ H
abbrev TraceAt (L : ℕ) (O : PrimitiveMachine) (o : Fin O.tapeCount) (τ σ : ℝ) (H : ℕ) (out : Bits) (r : ℕ) (st ans : Bits) :=
  D4Transcript.run (step L) O o τ σ r st ans out H
structure BranchOracle (P : Plan x) (v : DigitsData P) (O : PrimitiveMachine) (o : Fin O.tapeCount) (τ σ : ℝ) (H B : ℕ) : Prop where
  exactValue : ∀ u, unpack P.f x.l (qprec P) (P.R u) (h P u) (J P u) (v u) = BTNContract (P.R u) (P.V u)
  count : ∀ u, J P u^(P.R u).nV ≤ B
  output : (answer x).length ≤ H
  br : ∀ u s, Call O o τ σ H (brState P u s) 1 (rankQuery x (u.val+1)) (branch P u)
  dg : ∀ u a s t, Call O o τ σ H (dgState P u a s t) 2 (dgQuery P u a) (dgAns P v u a)
def hdState (x : Input C c) (buf : Bits) := listWord [countWord 1,input x,buf]
def need (P : Plan x) := max (qprec P) x.l
end
end DetDLP.D4BOuter


