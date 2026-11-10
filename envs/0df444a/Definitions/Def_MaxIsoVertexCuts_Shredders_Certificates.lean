-- Prove2me | Definitions.Def_MaxIsoVertexCuts_Shredders_Certificates
-- name    : MaxIsoVertexCuts_Shredders_Certificates
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-09T23:52:21.041372+00:00
-- url     : https://prove2.me/theorems/3511c1cc-86e7-4d17-8c7c-74c9b1add1e7
-- title:
--   Certificates
-- statement:
--   A component certificate consists of distinct components and witnesses from distinct further components. Completeness certifies every component; L-completeness certifies all components inside L and one inside R. Steiner certificates only use components meeting U and witnesses in U. T-terminal completeness lists every component meeting U but missing T, with witnesses in T and listed components missing T. Size is |S|+|W|+Σ|C|. Definitions 5.1,5.12,5.15, printed pp.28,32 (PDF 30,34).
-- source:
--   Fischer and Yingchareonthawornchai, Maximal Isolating Vertex Cuts and Shredders: Structure and Applications, STOC 2027 submission, Sections 2–5; machine conventions specified in the mission.

import Mathlib
import Definitions.Def_MaxIsoVertexCuts_Shredders_Outsiders

open Classical
open scoped BigOperators
noncomputable section

namespace MaxIsoVertexCuts.Shredders

structure Certificate (n : ℕ) where
  C : Finset (VSet n)
  W : VSet n
  deriving DecidableEq

def Certifies {n : ℕ} (z : Certificate n) (D : VSet n) : Prop :=
  D ∈ z.C ∨ (D ∩ z.W).Nonempty

def ValidCertificate {n : ℕ} (G : SimpleGraph (Fin n)) (S : VSet n)
    (z : Certificate n) : Prop :=
  (∀ D ∈ z.C, HypRecov.IsCompOf G S D) ∧ Disjoint z.W S ∧
  (∀ D ∈ components G S, (D ∩ z.W).card ≤ 1) ∧
  ∀ D ∈ z.C, Disjoint D z.W

def Complete {n : ℕ} (G : SimpleGraph (Fin n)) (S : VSet n) (z : Certificate n) : Prop :=
  ValidCertificate G S z ∧ ∀ D ∈ components G S, Certifies z D

def LComplete {n : ℕ} (G : SimpleGraph (Fin n)) (c : Cut n) (z : Certificate n) : Prop :=
  ValidCertificate G c.S z ∧
  (∀ D, HypRecov.IsCompOf G (Finset.univ \ c.L) D → Certifies z D) ∧
  ∃ D, HypRecov.IsCompOf G (Finset.univ \ c.R) D ∧ Certifies z D

def ValidSteinerCertificate {n : ℕ} (G : SimpleGraph (Fin n))
    (U S : VSet n) (z : Certificate n) : Prop :=
  ValidCertificate G S z ∧ z.W ⊆ U ∧ ∀ D ∈ z.C, (D ∩ U).Nonempty

def SteinerComplete {n : ℕ} (G : SimpleGraph (Fin n))
    (U S : VSet n) (z : Certificate n) : Prop :=
  ValidSteinerCertificate G U S z ∧ ∀ D ∈ steinerComponents G U S, Certifies z D

def TerminalComplete {n : ℕ} (G : SimpleGraph (Fin n))
    (U T S : VSet n) (z : Certificate n) : Prop :=
  ValidSteinerCertificate G U S z ∧ z.W ⊆ T ∧
  (∀ D ∈ z.C, Disjoint D T) ∧
  ∀ D ∈ steinerComponents G U S, Disjoint D T → D ∈ z.C

def certificateSize {n : ℕ} (S : VSet n) (z : Certificate n) : ℕ :=
  S.card + z.W.card + ∑ D ∈ z.C, D.card

end MaxIsoVertexCuts.Shredders


