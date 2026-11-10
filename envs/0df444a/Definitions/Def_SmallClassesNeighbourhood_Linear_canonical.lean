-- Prove2me | Definitions.Def_SmallClassesNeighbourhood_Linear_canonical
-- name    : SmallClassesNeighbourhood_Linear_canonical
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-09T16:35:47.911536+00:00
-- url     : https://prove2.me/theorems/14c1d5c3-cfc0-4414-b4cc-bc791f7beef8
-- title:
--   Canonical representatives, profiles, defects and witnesses
-- statement:
--   Set C=C_0^4 and n=|A|. The standing selection has a minimal bipartite pair A,B, |B|=Cn, and n>C^10. R is an inclusion-maximal subset of B whose A-neighbourhoods have pairwise symmetric differences larger than C^10. Equality of R-neighbourhoods partitions A. Q contains exactly one representative of each class. For u∈A, rep(u) is that unique representative; outside this domain its total fallback is u if no representative exists.
--
--   For any vertex v define
--
--   $$\Sigma(v)=\{u\in A:rep(u)\text{ is adjacent to }v\},\qquad P_v=N_Q(v),\qquad D_v=N_A(v)\triangle\Sigma(v).$$
--
--   Good selections require B_good ⊆ B∖R, |B_good| ≥ |B|/3, and |D_v| ≤ 4C^10 on B_good. The families of profiles and defects are actual finite images, so repetitions count once. For U⊆A, rep(U) is its image under rep; R_0⊆R is a witness if rep(U) is R_0-diverse. The defect graph has parts A and B_good and edges u∈D_v. All these are computed from F,R,Q. The selection structure packages only preceding source choices, and does not assume profile–defect injectivity or automorphism invariance.
-- source:
--   John Sylvester, Viktor Zamaraev, Maksim Zhukovskii, STOC 2027 submission #1126 (October 2026), §3 and §3.2.1, printed pp. 11 and 13–16 (PDF pp. 12 and 14–17)

import Definitions.Def_SmallClassesNeighbourhood_Linear_setSystems

noncomputable section

namespace SmallClassesNeighbourhood.Linear
variable {V : Type} [Fintype V] [DecidableEq V]

def MaximalSeparated (F : SimpleGraph V) (A B R : Finset V) (t : ℕ) : Prop :=
  R ⊆ B ∧ Separated t (traces F A R) ∧ Diverse F A R ∧
  ∀ R' : Finset V, R ⊆ R' → R' ⊆ B →
    Separated t (traces F A R') → Diverse F A R' → R' = R

def Representatives (F : SimpleGraph V) (A R Q : Finset V) : Prop :=
  Q ⊆ A ∧ ∀ u ∈ A, ∃! q : V, q ∈ Q ∧ trace F R q = trace F R u

/-- On A this is the unique member of Q with the same R-neighbourhood. -/
def rep (F : SimpleGraph V) (R Q : Finset V) (u : V) : V := by
  classical
  exact if h : ∃ q : V, q ∈ Q ∧ trace F R q = trace F R u then Classical.choose h else u

def repImage (F : SimpleGraph V) (R Q U : Finset V) : Finset V := by
  classical
  exact U.image (rep F R Q)

def sigmaSet (F : SimpleGraph V) (A R Q : Finset V) (v : V) : Finset V := by
  classical
  exact A.filter (fun u => F.Adj (rep F R Q u) v)

def profile (F : SimpleGraph V) (Q : Finset V) (v : V) : Finset V := trace F Q v

def defect (F : SimpleGraph V) (A R Q : Finset V) (v : V) : Finset V :=
  symmDiff (trace F A v) (sigmaSet F A R Q v)

def GoodSelection (C : ℕ) (F : SimpleGraph V) (A B R Q Bgood : Finset V) : Prop :=
  Representatives F A R Q ∧ Bgood ⊆ B \ R ∧
  (B.card : ℝ) / 3 ≤ (Bgood.card : ℝ) ∧
  ∀ v ∈ Bgood, (defect F A R Q v).card ≤ 4 * C ^ 10

/-- Exactly the standing choices fixed after Lemma 17, before either case. -/
structure CanonicalData (C0 : ℕ) (F : SimpleGraph V) where
  A : Finset V
  B : Finset V
  R : Finset V
  Q : Finset V
  Bgood : Finset V
  pair : MinimalPair (C0 ^ 4) F A B
  size_B : B.card = C0 ^ 4 * A.card
  large_A : (C0 ^ 4) ^ 10 < A.card
  maximal_R : MaximalSeparated F A B R ((C0 ^ 4) ^ 10)
  good : GoodSelection (C0 ^ 4) F A B R Q Bgood

namespace CanonicalData
variable {C0 : ℕ} {F : SimpleGraph V}

def P (s : CanonicalData C0 F) : V → Finset V := profile F s.Q

def D (s : CanonicalData C0 F) : V → Finset V := defect F s.A s.R s.Q

def representative (s : CanonicalData C0 F) : V → V := rep F s.R s.Q

def representativesOf (s : CanonicalData C0 F) (U : Finset V) : Finset V := repImage F s.R s.Q U

def defects (s : CanonicalData C0 F) : Finset (Finset V) := by
  classical
  exact s.Bgood.image s.D

def profiles (s : CanonicalData C0 F) : Finset (Finset V) := by
  classical
  exact s.Bgood.image s.P

def Witness (s : CanonicalData C0 F) (U R0 : Finset V) : Prop :=
  R0 ⊆ s.R ∧ Diverse F R0 (s.representativesOf U)

/-- Defect incidences as an actual simple undirected graph. -/
def defectGraph (s : CanonicalData C0 F) : SimpleGraph V where
  Adj u v := (u ∈ s.A ∧ v ∈ s.Bgood ∧ u ∈ s.D v) ∨
    (v ∈ s.A ∧ u ∈ s.Bgood ∧ v ∈ s.D u)
  symm := ⟨by intro u v; tauto⟩
  loopless := ⟨by
    intro u h
    have hd := s.pair.1.1
    have hb : u ∈ s.B := (Finset.mem_sdiff.mp (s.good.2.1 (by tauto))).1
    exact Finset.disjoint_left.mp hd (by tauto) hb⟩

end CanonicalData
end SmallClassesNeighbourhood.Linear


