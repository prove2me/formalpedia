-- Prove2me | Definitions.Def_MaxIsoVertexCuts_Shredders_VertexCuts
-- name    : MaxIsoVertexCuts_Shredders_VertexCuts
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-09T23:49:39.672196+00:00
-- url     : https://prove2.me/theorems/7b1bdcb7-fd3f-432a-aec4-a793b855e61d
-- title:
--   VertexCuts
-- statement:
--   A cut partitions V into L,S,R with no edge between the shores. An (X,Y)-cut requires nonempty disjoint terminal sets in the respective shores. Minimum cuts minimize separator weight over all such cuts; minimum shores and separators are their projections. A-reachability is reachability inside the induced shore. Maximal minimum cuts dominate all A-reachable minimum shores. Definitions 3.1, 3.2 and 4.1, printed pp.17,23 (PDF 19,25).
-- source:
--   Fischer and Yingchareonthawornchai, Maximal Isolating Vertex Cuts and Shredders: Structure and Applications, STOC 2027 submission, Sections 2–5; machine conventions specified in the mission.

import Mathlib
import Definitions.Def_MaxIsoVertexCuts_Shredders_NeighborhoodWeight

open Classical
open scoped BigOperators
noncomputable section

namespace MaxIsoVertexCuts.Shredders

structure Cut (n : ℕ) where
  L : VSet n
  S : VSet n
  R : VSet n
  deriving DecidableEq

def IsCut {n : ℕ} (G : SimpleGraph (Fin n)) (c : Cut n) : Prop :=
  Disjoint c.L c.S ∧ Disjoint c.L c.R ∧ Disjoint c.S c.R ∧
  c.L ∪ c.S ∪ c.R = Finset.univ ∧ ∀ u ∈ c.L, ∀ v ∈ c.R, ¬ G.Adj u v

def IsXYCut {n : ℕ} (G : SimpleGraph (Fin n)) (X Y : VSet n) (c : Cut n) : Prop :=
  X.Nonempty ∧ Y.Nonempty ∧ Disjoint X Y ∧ IsCut G c ∧ X ⊆ c.L ∧ Y ⊆ c.R

def IsMinCut {n : ℕ} (G : SimpleGraph (Fin n)) (w : Fin n → ℝ)
    (X Y : VSet n) (c : Cut n) : Prop :=
  IsXYCut G X Y c ∧ ∀ d, IsXYCut G X Y d → weight w c.S ≤ weight w d.S

def IsMinShore {n : ℕ} (G : SimpleGraph (Fin n)) (w : Fin n → ℝ)
    (X Y L : VSet n) : Prop := ∃ c, IsMinCut G w X Y c ∧ c.L = L

def IsMinSeparator {n : ℕ} (G : SimpleGraph (Fin n)) (w : Fin n → ℝ)
    (X Y S : VSet n) : Prop := ∃ c, IsMinCut G w X Y c ∧ c.S = S

def Independent {n : ℕ} (G : SimpleGraph (Fin n)) (T : VSet n) : Prop :=
  ∀ u ∈ T, ∀ v ∈ T, ¬ G.Adj u v

def ReachIn {n : ℕ} (G : SimpleGraph (Fin n)) (L : VSet n) (u v : Fin n) : Prop :=
  ∃ hu : u ∈ L, ∃ hv : v ∈ L,
    (G.induce (L : Set (Fin n))).Reachable ⟨u, hu⟩ ⟨v, hv⟩

def AReachable {n : ℕ} (G : SimpleGraph (Fin n)) (L A : VSet n) : Prop :=
  ∀ x ∈ L, ∃ a ∈ A, ReachIn G L x a

def IsMaxMinCut {n : ℕ} (G : SimpleGraph (Fin n)) (w : Fin n → ℝ)
    (T A : VSet n) (c : Cut n) : Prop :=
  IsMinCut G w A (T \ A) c ∧ AReachable G c.L A ∧
    ∀ d, IsMinCut G w A (T \ A) d → AReachable G d.L A → d.L ⊆ c.L

end MaxIsoVertexCuts.Shredders


