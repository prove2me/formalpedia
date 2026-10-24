-- Prove2me | Definitions.Def_PricingWithTips3DM_36f8af72b5600c8711e12fba
-- name    : PricingWithTips3DM_36f8af72b5600c8711e12fba
-- status  : Definition
-- author  : @qmaai2907271020
-- created : 2026-10-22T20:37:28.669981+00:00
-- url     : https://prove2.me/theorems/67345c99-d218-4e47-aa5c-9dd00bd47d58
-- title:
--   PricingWithTips 3DM dependency: Scratch_PricingWithTips_CLRS3CNF_Bridge
-- statement:
--   A private, kernel-checked dependency module used by the formal NP-hardness proof for three-dimensional matching and Theorems 4.1 and 4.2 of arXiv:2507.10872.
-- source:
--   https://arxiv.org/abs/2507.10872

import Definitions.Def_PricingWithTips3DM_301732ff58b1de24a54f1b1e
import Definitions.Def_PricingWithTips3DM_b27b057a2325e62412e51b11
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false

/-!
Semantic bridge from the CLRS raw 3-CNF language used by the all-alphabet
Cook--Levin theorem to the certified-reductions library's concrete SAT
representation.  The guard is essential: `ThreeCNFSat` rejects decoded
formulas wider than three literals, whereas `Concrete.SAT` alone does not.
-/

namespace PricingWithTips.CLRS3CNFBridge

open Hardness Hardness.Cert

def certLiteral : CLRS.Chapter34.Literal → LitTy.denote
  | .pos i => (i, true)
  | .neg i => (i, false)

def certCNF (f : CLRS.Chapter34.CNF) : SatTy.denote :=
  f.map (List.map certLiteral)

def guardedCertCNF (input : List CLRS.Chapter34.CNFSym) : SatTy.denote :=
  let f := CLRS.Chapter34.decodeCNF input
  if CLRS.Chapter34.isThreeCNFBool f then certCNF f else [[]]

theorem certLiteral_holds_iff (σ : ℕ → Bool)
    (l : CLRS.Chapter34.Literal) :
    (Hardness.Cert.litOf (certLiteral l)).Holds σ ↔
      CLRS.Chapter34.evalLit σ l := by
  cases l <;> simp [certLiteral, Hardness.Cert.litOf,
    Hardness.Literal.Holds, CLRS.Chapter34.evalLit]

theorem certClause_sat_iff (σ : ℕ → Bool)
    (c : CLRS.Chapter34.Clause) :
    Hardness.Clause.Sat σ
        ((List.map Hardness.Cert.litOf ∘ List.map certLiteral) c) ↔
      CLRS.Chapter34.evalClause σ c := by
  rw [show (List.map Hardness.Cert.litOf ∘ List.map certLiteral) c =
      c.map (Hardness.Cert.litOf ∘ certLiteral) by
    simp [Function.comp_def, List.map_map]]
  simp only [Hardness.Clause.Sat, CLRS.Chapter34.evalClause,
    List.mem_map, Function.comp_apply]
  constructor
  · rintro ⟨_, ⟨l, hl, rfl⟩, hh⟩
    exact ⟨l, hl, (certLiteral_holds_iff σ l).mp hh⟩
  · rintro ⟨l, hl, hh⟩
    exact ⟨Hardness.Cert.litOf (certLiteral l),
      ⟨l, hl, rfl⟩, (certLiteral_holds_iff σ l).mpr hh⟩

theorem certCNF_satisfiable_iff (f : CLRS.Chapter34.CNF) :
    (Hardness.Cert.decodeCNF (certCNF f)).Satisfiable ↔
      CLRS.Chapter34.CnfSatisfiable f := by
  constructor
  · rintro ⟨σ, hσ⟩
    refine ⟨σ, ?_⟩
    intro c hc
    have hmem : (List.map Hardness.Cert.litOf ∘ List.map certLiteral) c ∈
        Hardness.Cert.decodeCNF (certCNF f) := by
      exact List.mem_map_of_mem (List.mem_map_of_mem hc)
    exact (certClause_sat_iff σ c).mp
      (hσ ((List.map Hardness.Cert.litOf ∘ List.map certLiteral) c)
        hmem)
  · rintro ⟨σ, hσ⟩
    refine ⟨σ, ?_⟩
    intro c hc
    simp only [Hardness.Cert.decodeCNF, certCNF, List.map_map,
      Function.comp_apply] at hc ⊢
    obtain ⟨d, hd, rfl⟩ := List.mem_map.mp hc
    exact (certClause_sat_iff σ d).mpr (hσ d hd)

theorem threeCNFSat_iff_guardedCertSAT
    (input : List CLRS.Chapter34.CNFSym) :
    input ∈ CLRS.Chapter34.ThreeCNFSat ↔
      Hardness.Cert.Concrete.SAT (guardedCertCNF input) := by
  rw [show input ∈ CLRS.Chapter34.ThreeCNFSat ↔
      CLRS.Chapter34.IsThreeCNF (CLRS.Chapter34.decodeCNF input) ∧
        CLRS.Chapter34.CnfSatisfiable (CLRS.Chapter34.decodeCNF input) from Iff.rfl]
  rw [show Hardness.Cert.Concrete.SAT (guardedCertCNF input) ↔
      (Hardness.Cert.decodeCNF (guardedCertCNF input)).Satisfiable from Iff.rfl]
  by_cases h : CLRS.Chapter34.IsThreeCNF (CLRS.Chapter34.decodeCNF input)
  · have hb : CLRS.Chapter34.isThreeCNFBool
        (CLRS.Chapter34.decodeCNF input) = true :=
      (CLRS.Chapter34.isThreeCNFBool_eq_true _).2 h
    simp only [guardedCertCNF, hb, if_true, h, true_and]
    exact (certCNF_satisfiable_iff _).symm
  · have hb : CLRS.Chapter34.isThreeCNFBool
        (CLRS.Chapter34.decodeCNF input) = false := by
      cases he : CLRS.Chapter34.isThreeCNFBool
          (CLRS.Chapter34.decodeCNF input)
      · rfl
      · exact False.elim (h ((CLRS.Chapter34.isThreeCNFBool_eq_true _).1 he))
    simp only [guardedCertCNF, hb, h, false_and]
    constructor
    · intro hf
      exact False.elim hf
    · intro hs
      exact Hardness.CNF.not_satisfiable_of_nil_mem
        (φ := Hardness.Cert.decodeCNF ([[]] : SatTy.denote))
        (by simp [Hardness.Cert.decodeCNF]) hs

end PricingWithTips.CLRS3CNFBridge


