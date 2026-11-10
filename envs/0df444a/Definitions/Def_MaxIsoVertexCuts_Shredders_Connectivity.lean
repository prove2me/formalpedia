-- Prove2me | Definitions.Def_MaxIsoVertexCuts_Shredders_Connectivity
-- name    : MaxIsoVertexCuts_Shredders_Connectivity
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-09T23:50:25.61549+00:00
-- url     : https://prove2.me/theorems/987c5d6e-8f2c-4c1e-a1a5-4e3be4aac311
-- title:
--   Connectivity
-- statement:
--   The components of G−S use the published component predicate. A separator leaves at least two components; a shredder leaves at least three; a k-shredder has cardinality k. Vertex connectivity is the least separator cardinality, with κ(K_n)=n−1. Section 2, printed p.16 (PDF 18).
-- source:
--   Fischer and Yingchareonthawornchai, Maximal Isolating Vertex Cuts and Shredders: Structure and Applications, STOC 2027 submission, Sections 2–5; machine conventions specified in the mission.

import Mathlib
import Definitions.Def_MaxIsoVertexCuts_Shredders_VertexCuts

open Classical
open scoped BigOperators
noncomputable section

namespace MaxIsoVertexCuts.Shredders

noncomputable def components {n : ℕ} (G : SimpleGraph (Fin n)) (S : VSet n) : Finset (VSet n) :=
  Finset.univ.filter (HypRecov.IsCompOf G S)
noncomputable def steinerComponents {n : ℕ} (G : SimpleGraph (Fin n))
    (U S : VSet n) : Finset (VSet n) :=
  (components G S).filter fun C => (C ∩ U).Nonempty

def IsSeparator {n : ℕ} (G : SimpleGraph (Fin n)) (S : VSet n) : Prop :=
  2 ≤ (components G S).card

def IsShredder {n : ℕ} (G : SimpleGraph (Fin n)) (S : VSet n) : Prop :=
  3 ≤ (components G S).card

def IsKShredder {n : ℕ} (G : SimpleGraph (Fin n)) (k : ℕ) (S : VSet n) : Prop :=
  IsShredder G S ∧ S.card = k

noncomputable def kappa {n : ℕ} (G : SimpleGraph (Fin n)) : ℕ :=
  if h : ∃ k : ℕ, ∃ S, IsSeparator G S ∧ S.card = k then Nat.find h else n - 1

end MaxIsoVertexCuts.Shredders


