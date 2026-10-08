-- Prove2me | Definitions.Def_LRC_SharedRepair_Defs
-- name    : LRC_SharedRepair_Defs
-- status  : Definition
-- author  : @Whunt003
-- created : 2026-10-07T06:01:35.478988+00:00
-- url     : https://prove2.me/theorems/4b7429b3-171a-47bd-8241-56e723ddfa4c
-- title:
--   Primitive flanks, blocker fibres, and strict lonely times
-- statement:
--   Write $d(x)=|x-\operatorname{round}(x)|$ for distance to the nearest integer. For finite sets $R,W\subseteq\mathbb N$, let $S(n,R,W)=\{v\in\mathbb N:0<v<n,\ v\notin R\}\cup W$. A strict time means a real $t$ such that $d(vt)>1/n$ for every $v\in S(n,R,W)$. Write $U_r=\{0\le b<r:\gcd(r,b)=1\}$, $F_{n,r}=\{n-r\le b<n:\gcd(r,b)=1\}$, and $B(n,r,m,q,b)$ for the existence of an integer $D$ with $|nmD-q|\le mr$ and $r\mid Db-q$. An active fibre for $(n,r,m,q)$ consists of natural numbers $(d,h,U,V)$ with $d,V>0$, $h\ge2$, $r=dh$, $q=dU$, $\gcd(h,U)=\gcd(h,V)=1$, $|nmV-U|\le hm$, and, for every $b\in U_r$, $B(n,r,m,q,b)$ if and only if $h\mid Vb-U$.
--
--   The bundle also defines the failed residue set as the residues modulo $r$ of coprime $b\in[n-r,m(n-r))$, and eligible insertions as $q\in W\setminus\{mr\}$ with $m(n-r)\le q$. The bad-unit set filters $U_r$ by $B$; a primitive fibre filters $F_{n,r}$ by a reduced congruence $h\mid Vb-U$. A canonical Bezout numerator is $\operatorname{gcdA}(b,r)$.
--
--   For shifted two-speed intervals, a strict window requires $d(\alpha+pt),d(\beta+qt)>\delta$ at some $t\in[A,B]$. Writing $a=2\delta/p+2\delta/q$, the block bound is $\max\{a,(\lfloor qa\rfloor+2\delta)/q\}$. Real-clock candidate and blocker predicates replace $q$ by a real clock parameter $x$ only in the determinant window, retaining the congruence with $q$.
--
--   The finite small-fibre table uses the minimum multiplier $13$ when $(r,n)=(12,14)$ and $\lfloor n/(n-r)\rfloor+1$ otherwise, together with explicit representative and margin predicates and two stated small exceptions. These are definitions and a decidability instance, not assumed covering or escape theorems.
-- source:
--   Wade Hunter, lonely-runner research repository, https://github.com/huntrontrakkr/lonely-runner; local source snapshot 9b5f51aa235e321a3ec794c9bf60358933a8e6dc. Compiler-selected definition closure of LonelyRunner.UniqueSharedRepair.strict_of_unique_shared_multiple, from the 47 source modules recorded in the local source-hash manifest. AI-assisted formalization.

import Mathlib
import Mathlib.Data.ZMod.Units
import Mathlib.GroupTheory.Index
import Mathlib.RingTheory.Coprime.Lemmas
import Mathlib.RingTheory.Int.Basic

namespace LonelyRunner

/-- Distance from `x` to the nearest integer (`‖x‖` in the literature). -/
noncomputable def ndist (x : ℝ) : ℝ := |x - round x|













































end LonelyRunner

namespace LonelyRunner.BadCover





















end LonelyRunner.BadCover

namespace LonelyRunner.Farey



















end LonelyRunner.Farey

namespace LonelyRunner.CoprimeReplacements

open Farey BadCover





























end LonelyRunner.CoprimeReplacements

namespace LonelyRunner.SingleDeletion

open BadCover









end LonelyRunner.SingleDeletion

namespace LonelyRunner.BadCover











end LonelyRunner.BadCover

namespace LonelyRunner.MatchingArithmetic





end LonelyRunner.MatchingArithmetic

namespace LonelyRunner.LargeDeletionMatching

open BadCover SingleDeletion



















end LonelyRunner.LargeDeletionMatching

namespace LonelyRunner.SeparatedBands

open BadCover









end LonelyRunner.SeparatedBands

namespace LonelyRunner

open Finset



























end LonelyRunner

namespace LonelyRunner

















end LonelyRunner

namespace LonelyRunner.FailedWindow

open Farey BadCover









end LonelyRunner.FailedWindow

namespace LonelyRunner.SeparatedReplacements

open LargeDeletionMatching SeparatedBands























end LonelyRunner.SeparatedReplacements

namespace LonelyRunner.MixedReplacements

open LargeDeletionMatching SeparatedReplacements













end LonelyRunner.MixedReplacements

namespace LonelyRunner.SeparatedMulti

open SeparatedReplacements SeparatedBands SingleDeletion

def HasStrictTime (n : ℕ) (R W : Finset ℕ) : Prop :=
  ∃ t : ℝ, ∀ v : ℕ, ((0 < v ∧ v < n ∧ v ∉ R) ∨ v ∈ W) →
    (1:ℝ)/n < ndist ((v:ℝ)*t)





















end LonelyRunner.SeparatedMulti

namespace LonelyRunner.FailedFlank

open Farey BadCover LargeDeletionMatching









end LonelyRunner.FailedFlank

namespace LonelyRunner.FlankReduction

















end LonelyRunner.FlankReduction

namespace LonelyRunner.NearData

open LargeDeletionMatching SeparatedReplacements







end LonelyRunner.NearData

namespace LonelyRunner.FastestBoundary



















/-- Distinct unit residues of the failed GW window. -/
def failedResidues (n r m : ℕ) : Finset ℕ :=
  ((Finset.Ico (n-r) (m*(n-r))).filter (fun b => Nat.Coprime r b)).image (· % r)

/-- Other insertions large enough to block a failed boundary. -/
def eligible (n r m : ℕ) (W : Finset ℕ) : Finset ℕ :=
  (W.erase (m*r)).filter (fun q => m*(n-r) ≤ q)







end LonelyRunner.FastestBoundary

namespace LonelyRunner.CollectiveBoundary

def Candidate (n r m q D : ℤ) : Prop := |n*m*D-q| ≤ m*r

def Blocks (n r m q b : ℤ) : Prop :=
  ∃ D : ℤ, Candidate n r m q D ∧ r ∣ D*b-q



















end LonelyRunner.CollectiveBoundary

namespace LonelyRunner.SharedFastest

open FastestBoundary















end LonelyRunner.SharedFastest

namespace LonelyRunner.CollectiveUnits

/-- Canonical natural representatives of the units modulo `r`. -/
def units (r : ℕ) : Finset ℕ := (Finset.range r).filter (Nat.Coprime r)

















/-- One full period of primitive flank indices. -/
def primitiveFlanks (n r : ℕ) : Finset ℕ :=
  (Finset.Ico (n-r) n).filter (Nat.Coprime r)



















end LonelyRunner.CollectiveUnits

namespace LonelyRunner.CollectiveFibreNormalForm

structure ActiveFibre (n r m q : ℕ) where
  d : ℕ
  h : ℕ
  U : ℕ
  V : ℕ
  d_pos : 0 < d
  h_two : 2 ≤ h
  v_pos : 0 < V
  r_eq : r = d*h
  q_eq : q = d*U
  copU : Nat.Coprime h U
  copV : Nat.Coprime h V
  window : |(n:ℤ)*m*V-U| ≤ (h:ℤ)*m
  blocks_iff : ∀ b ∈ CollectiveUnits.units r,
    CollectiveBoundary.Blocks (n:ℤ) r m q b ↔ (h:ℤ) ∣ (V:ℤ)*b-U



end LonelyRunner.CollectiveFibreNormalForm

namespace LonelyRunner.CollectiveFibreCounting
open CollectiveUnits











end LonelyRunner.CollectiveFibreCounting

namespace LonelyRunner.TotientCapacity









end LonelyRunner.TotientCapacity

namespace LonelyRunner.SmallTotient









end LonelyRunner.SmallTotient

namespace LonelyRunner.CollectiveFibreClassification
open CollectiveBoundary CollectiveUnits

noncomputable def badUnits (n r m q : ℕ) : Finset ℕ :=
  by classical exact (units r).filter (fun b : ℕ => Blocks (n:ℤ) r m q b)



















end LonelyRunner.CollectiveFibreClassification

namespace LonelyRunner.TwoBlockerGeometry



















end LonelyRunner.TwoBlockerGeometry

namespace LonelyRunner.SharedMiddleArithmetic





















end LonelyRunner.SharedMiddleArithmetic

namespace LonelyRunner.ShiftedWindows



def StrictWindow (p q α β δ A B : ℝ) : Prop :=
  ∃ t ∈ Set.Icc A B, δ < ndist (α+p*t) ∧ δ < ndist (β+q*t)











end LonelyRunner.ShiftedWindows

namespace LonelyRunner.ShiftedBlocks









noncomputable def blockBound (p q δ : ℝ) : ℝ :=
  max (2*δ/p+2*δ/q) ((((⌊q*(2*δ/p+2*δ/q)⌋:ℤ):ℝ)+2*δ)/q)











end LonelyRunner.ShiftedBlocks

namespace LonelyRunner.WholeFlankWindows

open BadCover SeparatedMulti











end LonelyRunner.WholeFlankWindows

namespace LonelyRunner.CollectivePhase







end LonelyRunner.CollectivePhase

namespace LonelyRunner.CollectiveBoundaryForcing
open CollectiveBoundary CollectiveUnits







end LonelyRunner.CollectiveBoundaryForcing

namespace LonelyRunner.CollectiveSecondFastest

open BadCover





/-- A canonical Bezout numerator for a primitive representative. -/
def numerator (r b : ℕ) : ℤ := Nat.gcdA b r













end LonelyRunner.CollectiveSecondFastest

namespace LonelyRunner.SmallFibrePhase
open CollectiveFibreNormalForm CollectiveSecondFastest

















end LonelyRunner.SmallFibrePhase

namespace LonelyRunner.PrimitiveFibre
open CollectiveUnits CollectiveFibreNormalForm





def fibre (n r h V U : ℕ) : Finset ℕ :=
  (primitiveFlanks n r).filter (fun b => (h:ℤ) ∣ (V:ℤ)*b-U)











end LonelyRunner.PrimitiveFibre

namespace LonelyRunner.CanonicalTwoCover
open CollectiveUnits CollectiveBoundary CollectiveFibreClassification





end LonelyRunner.CanonicalTwoCover

namespace LonelyRunner.RealClockCapacity
open CollectiveBoundary CollectiveUnits CollectiveSecondFastest

def Candidate (n r m : ℤ) (x : ℝ) (D : ℤ) : Prop :=
  |(n:ℝ)*m*D-x| ≤ (m:ℝ)*r

def Blocks (n r m q b : ℤ) (x : ℝ) : Prop :=
  ∃ D : ℤ, Candidate n r m x D ∧ r ∣ D*b-q











noncomputable def badUnits (n r m q : ℕ) (x : ℝ) : Finset ℕ := by
  classical exact (units r).filter (fun b => Blocks (n:ℤ) r m q b x)









end LonelyRunner.RealClockCapacity

namespace LonelyRunner.TwoBlockerArithmetic
open CollectiveUnits























end LonelyRunner.TwoBlockerArithmetic

namespace LonelyRunner.TwoHalfPhase

open TwoBlockerArithmetic













end LonelyRunner.TwoHalfPhase

namespace LonelyRunner.SharedSlowestHalf
open CollectiveSecondFastest CollectiveUnits BadCover







end LonelyRunner.SharedSlowestHalf

namespace LonelyRunner.ComplementaryEscape
open CollectiveUnits CollectiveSecondFastest CollectiveFibreNormalForm









end LonelyRunner.ComplementaryEscape

namespace LonelyRunner.SmallFibreTable
open CollectiveUnits CollectiveFibreNormalForm

def minimumMultiplier (r n : ℕ) : ℕ :=
  if r=12 ∧ n=14 then 13 else n/(n-r)+1



def Entry (r n h C b : ℕ) : Prop :=
  n-r ≤ b ∧ b < n ∧ Nat.Coprime r b ∧ b%h=C ∧
  (b*(n+h) < minimumMultiplier r n*(n-r)*(n-h) ∨
    (r=12 ∧ n=19 ∧ h=6 ∧ C=5 ∧ b=11) ∨
    (r=12 ∧ n=20 ∧ h=6 ∧ C=1 ∧ b=13))

instance (r n h C b : ℕ) : Decidable (Entry r n h C b) := by unfold Entry; infer_instance

















end LonelyRunner.SmallFibreTable

namespace LonelyRunner.SharedSlowestSmall
open CollectiveSecondFastest





end LonelyRunner.SharedSlowestSmall

namespace LonelyRunner.SharedSlowest
open CollectiveUnits CollectiveSecondFastest CollectiveFibreNormalForm





end LonelyRunner.SharedSlowest

namespace LonelyRunner.UniqueSharedRepair







end LonelyRunner.UniqueSharedRepair


