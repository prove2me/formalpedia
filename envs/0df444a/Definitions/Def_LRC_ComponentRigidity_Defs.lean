-- Prove2me | Definitions.Def_LRC_ComponentRigidity_Defs
-- name    : LRC_ComponentRigidity_Defs
-- status  : Definition
-- author  : @Whunt003
-- created : 2026-10-07T18:53:53.778224+00:00
-- url     : https://prove2.me/theorems/e28d73da-9027-42d3-b4d1-b09e3e038b74
-- title:
--   Separated insertion cuts and small-component rigidity
-- statement:
--   Write $d(x)=|x-\operatorname{round}(x)|$ for distance to the nearest integer. For finite $R,W\subseteq\mathbb N$, put $S(n,R,W)=\{v\in\mathbb N:0<v<n,\ v\notin R\}\cup W$. A strict time is a real $t$ with $d(vt)>1/n$ for every $v\in S(n,R,W)$. Write $\operatorname{GW}(n,r,m)$ for the assertion that no natural number $b$ with $n-r\le b<m(n-r)$ is coprime to $r$. A separated cut $C\subseteq W$ satisfies $p+q<n\gcd(p,q)$ for every $p\in C$ and $q\in W\setminus C$. The insertion-component hypothesis means that $W$ admits a finite partition into blocks of size at most two, each a separated cut. Equivalently, the graph joining distinct $p,q$ when $n\gcd(p,q)\le p+q$ has components of size at most two. WeakAt requires every moving-speed distance at the specified time to be at least $1/n$. HasRepairs requires each deletion $r$ to have some $mr$ in the insertion set, with $m\ge2$ and GW satisfied, without assuming injectivity. Pairwise Separated requires the cut inequality for every pair of distinct insertions. The band indexed by $(p,j)\in\mathbb N\times\mathbb Z$ is $\{t:|pt-j|\le\delta\}$. The finite index set for $W,\delta,L,U$ contains $(p,j)$ with $p\in W$ and $\lfloor pL-\delta\rfloor\le j\le\lceil pU+\delta\rceil$. Smooth$(S,w)$ means every prime divisor of $w$ divides $S$. The two-deletion strict-time predicate uses $R=\{r,s\}$ and $W=\{p,q\}$. GW, distance, and the general strict-time predicate are imported from the earlier definition bundles. These are definitions, not assumed covering or matching results.
-- source:
--   Wade Hunter, AI-assisted lonely-runner research, https://github.com/huntrontrakkr/lonely-runner; local source snapshot e63781c7cf2101e453103bfd9b215b72d162d05d; compiler-selected definition closure. The snapshot identifies the local submitted source, not a publicly hosted commit.

import Mathlib
import Mathlib.NumberTheory.Bertrand
import Mathlib.NumberTheory.Primorial
import Definitions.Def_LRC_GW
import Definitions.Def_LRC_SharedRepair_Defs

namespace LonelyRunner















































end LonelyRunner

namespace LonelyRunner.BadCover





















end LonelyRunner.BadCover

namespace LonelyRunner.LaminarCover

open Set





end LonelyRunner.LaminarCover

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

/-- Strict loneliness for the baseline with two deletions and two insertions. -/
def HasStrictTime (n r s p q : ℕ) : Prop :=
  ∃ t : ℝ, ∀ v : ℕ,
    ((0 < v ∧ v < n ∧ v ≠ r ∧ v ≠ s) ∨ v=p ∨ v=q) →
    (1:ℝ)/n  <  ndist (t*v)

















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



def Separated (n : ℕ) (W : Finset ℕ) : Prop :=
  ∀ p ∈ W, ∀ q ∈ W, p ≠ q → p+q < n*Nat.gcd p q



















end LonelyRunner.SeparatedMulti

namespace LonelyRunner.InteractionComponents

open Set

def band (δ : ℝ) (i : ℕ × ℤ) : Set ℝ := {t | |(i.1 : ℝ)*t-i.2| ≤ δ}

def SeparatedCut (n : ℕ) (W C : Finset ℕ) : Prop :=
  ∀ p ∈ C, ∀ q ∈ W, q ∉ C → p+q < n*Nat.gcd p q







noncomputable def bandsOn (W : Finset ℕ) (δ L U : ℝ) : Finset (ℕ × ℤ) :=
  W.biUnion fun p =>
    (Finset.Icc ⌊(p:ℝ)*L-δ⌋ ⌈(p:ℝ)*U+δ⌉).image (fun j => (p,j))











end LonelyRunner.InteractionComponents

namespace LonelyRunner.GWArithmetic

open SeparatedReplacements







end LonelyRunner.GWArithmetic

namespace LonelyRunner.ContactPreservation











end LonelyRunner.ContactPreservation

namespace LonelyRunner.GWContactArithmetic

open SeparatedReplacements ContactPreservation



















end LonelyRunner.GWContactArithmetic

namespace LonelyRunner.ComponentRestoration

open SeparatedMulti InteractionComponents









end LonelyRunner.ComponentRestoration

namespace LonelyRunner.GWGrowth

open SeparatedReplacements GWArithmetic

























end LonelyRunner.GWGrowth

namespace LonelyRunner.OddSmooth

open SeparatedReplacements GWGrowth

/-- All prime divisors of w divide S. -/
def Smooth (S w : ℕ) : Prop := ∀ p : ℕ, Nat.Prime p → p ∣ w → p ∣ S













end LonelyRunner.OddSmooth

namespace LonelyRunner.SecondUnit

open SeparatedReplacements GWArithmetic OddSmooth











end LonelyRunner.SecondUnit

namespace LonelyRunner.ElementarySmooth

open SeparatedReplacements OddSmooth GWArithmetic GWGrowth SecondUnit

















end LonelyRunner.ElementarySmooth

namespace LonelyRunner.FailedFlank

open Farey BadCover LargeDeletionMatching









end LonelyRunner.FailedFlank

namespace LonelyRunner.FlankReduction

















end LonelyRunner.FlankReduction

namespace LonelyRunner.MixedNormalize

open SeparatedReplacements SecondUnit GWArithmetic



end LonelyRunner.MixedNormalize

namespace LonelyRunner.MixedArithmetic

open SeparatedReplacements GWArithmetic GWGrowth FlankReduction SecondUnit



end LonelyRunner.MixedArithmetic

namespace LonelyRunner.NearData

open LargeDeletionMatching SeparatedReplacements







end LonelyRunner.NearData

namespace LonelyRunner.MixedConverse

open LargeDeletionMatching SeparatedReplacements MixedReplacements
open GWArithmetic GWGrowth FlankReduction









end LonelyRunner.MixedConverse

namespace LonelyRunner.SmallComponentRigidity

open SeparatedMulti SeparatedReplacements InteractionComponents

def HasRepairs (n : ℕ) (D C : Finset ℕ) : Prop :=
  ∀ r ∈ D, ∃ p ∈ C, ∃ m : ℕ, 2 ≤ m ∧ p=m*r ∧ GW n r m















/-- A partition into separated sets of size at most two. Equivalently, the
arithmetic insertion graph has no connected component larger than two. -/
def PairComponents (n : ℕ) (W : Finset ℕ) : Prop :=
  ∃ B : Finset (Finset ℕ), B.biUnion id=W ∧
    (B : Set (Finset ℕ)).PairwiseDisjoint id ∧
    ∀ C ∈ B, C.card ≤ 2 ∧ SeparatedCut n W C





/-- A weak lonely time for the modified consecutive baseline. -/
def WeakAt (n : ℕ) (R W : Finset ℕ) (t : ℝ) : Prop :=
  ∀ v : ℕ, ((0 < v ∧ v < n ∧ v ∉ R) ∨ v ∈ W) →
    1/(n:ℝ) ≤ ndist ((v:ℝ)*t)













end LonelyRunner.SmallComponentRigidity


