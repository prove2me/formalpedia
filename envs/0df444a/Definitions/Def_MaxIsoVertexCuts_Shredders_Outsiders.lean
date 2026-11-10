-- Prove2me | Definitions.Def_MaxIsoVertexCuts_Shredders_Outsiders
-- name    : MaxIsoVertexCuts_Shredders_Outsiders
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-09T23:51:26.177987+00:00
-- url     : https://prove2.me/theorems/b52a17b3-86cf-4ef8-bd1b-a96f9860b0ec
-- title:
--   Outsiders
-- statement:
--   Source-sink and Steiner connectivity are infima of positive separator weights in ENNReal, hence infinity when no separator exists. A-shredders are minimum (A,T−A)-separators with a component missing T; A-outsiders are vertices in such components for some such separator. Steiner shredders leave at least three components meeting U; source-sink and isolating variants also require the corresponding minimum-separator property. Definitions 3.6–3.7, 5.11, printed pp.19–20,31 (PDF 21–22,33).
-- source:
--   Fischer and Yingchareonthawornchai, Maximal Isolating Vertex Cuts and Shredders: Structure and Applications, STOC 2027 submission, Sections 2–5; machine conventions specified in the mission.

import Mathlib
import Definitions.Def_MaxIsoVertexCuts_Shredders_Connectivity

open Classical
open scoped BigOperators
noncomputable section

namespace MaxIsoVertexCuts.Shredders

def STSeparator {n : ℕ} (G : SimpleGraph (Fin n)) (s t : Fin n) (S : VSet n) : Prop :=
  s ≠ t ∧ s ∉ S ∧ t ∉ S ∧ ¬ ReachIn G (Finset.univ \ S) s t
noncomputable def stKappa {n : ℕ} (G : SimpleGraph (Fin n)) (w : Fin n → ℝ)
    (s t : Fin n) : ENNReal :=
  ⨅ S : {S : VSet n // STSeparator G s t S}, ENNReal.ofReal (weight w S.val)
noncomputable def steinerKappa {n : ℕ} (G : SimpleGraph (Fin n)) (w : Fin n → ℝ)
    (U : VSet n) : ENNReal :=
  ⨅ S : {S : VSet n // 2 ≤ (steinerComponents G U S).card}, ENNReal.ofReal (weight w S.val)

def AShredder {n : ℕ} (G : SimpleGraph (Fin n)) (w : Fin n → ℝ)
    (T A S : VSet n) : Prop :=
  IsMinSeparator G w A (T \ A) S ∧ ∃ C ∈ components G S, Disjoint C T
noncomputable def outsiders {n : ℕ} (G : SimpleGraph (Fin n)) (w : Fin n → ℝ)
    (T A : VSet n) : VSet n :=
  Finset.univ.filter fun x => ∃ S, AShredder G w T A S ∧
    x ∉ S ∧ ∀ t ∈ T, ¬ ReachIn G (Finset.univ \ S) x t

def STShredder {n : ℕ} (G : SimpleGraph (Fin n)) (w : Fin n → ℝ)
    (U : VSet n) (s t : Fin n) (S : VSet n) : Prop :=
  IsMinSeparator G w {s} {t} S ∧ 3 ≤ (steinerComponents G U S).card

def IsolatingSteinerShredder {n : ℕ} (G : SimpleGraph (Fin n)) (w : Fin n → ℝ)
    (U T : VSet n) (t : Fin n) (S : VSet n) : Prop :=
  AShredder G w T {t} S ∧ 3 ≤ (steinerComponents G U S).card

end MaxIsoVertexCuts.Shredders


