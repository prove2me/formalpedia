-- Prove2me | Definitions.Def_GeneralPieces_Defs
-- name    : GeneralPieces_Defs
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-04T22:28:17.923873+00:00
-- url     : https://prove2.me/theorems/099add04-1dcc-49c4-a3b5-5ed50773d872
-- title:
--   Defs
-- statement:
--   Definitions and structural lemmas for Defs, from Anthropic’s pinned ETH development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/Defs.lean

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ClauseBound_Gen_Defs
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Theorems.Thm_Groundwork_PolyT_length
import Theorems.Thm_Groundwork_PolyT_map
import Theorems.Thm_Groundwork_PolyT_sum
attribute [local fun_prop] Groundwork.PolyT.length
attribute [local fun_prop] Groundwork.PolyT.map
attribute [local fun_prop] Groundwork.PolyT.sum


set_option autoImplicit false
section
section
namespace GeneralPieces
open Finset Groundwork Groundwork.Prog PaddedDescent.F ClauseBound.Alg ClauseBound.Gen Levels.Gen
def StCaseII : Prop := ∀ (K g : ℕ) (c : Fin g → Fin g → ℕ) (P ζ : ℝ), 2 ≤ K → 2 ≤ g → K ∣ g → 0 < ζ → ζ ≤ 1 → 0 < P →
  (∀ a, ∑ b ∈ univ.erase a, (c a b : ℝ) ≤ P) → (∀ a b, a ≠ b → (c a b : ℝ) ≤ P / g) →
  (K : ℝ) * Real.log (2 * g * K) ≤ 2 * ζ ^ 2 * g →
  ∃ χ : Fin g → Fin K, (∀ γ, #{a | χ a = γ} = g / K) ∧
    ∀ γ γ', γ ≠ γ' → (∑ a with χ a = γ, ∑ b with χ b = γ', (c a b : ℝ)) <
      ((∑ a, ∑ b ∈ univ.erase a, (c a b : ℝ)) + 2 * ζ * g * P) / (K : ℝ) ^ 2
noncomputable def zetaOf (s : Step) : ℝ := 3 / (2 * (s.D : ℝ))
structure LevelOK2 (P : PiecesF) (s : Step) (lam : ℕ) : Prop where
  spec : P.Spec s.h lam
  two_le : 2 ≤ s.K
  two_le_p : 2 ≤ s.p
  D_ge : 2 ≤ s.D
  dvd : s.K ∣ s.p
  hoeffding : (s.K : ℝ) * Real.log (2 * s.p * s.K) ≤ 2 * zetaOf s ^ 2 * s.p
  square : s.thin = false → s.p = s.d
  a_pos : s.thin = true → 1 ≤ s.a
  ubar : ∀ y < nPat P s lam, (s.thin && colSide P s lam y) = false →
    totalG P s.p s.d (!s.thin && colSide P s lam y) s.h lam y ≤ ubarG P s lam
  ebar : ∀ y < nPat P s lam, (s.thin && colSide P s lam y) = true → totalG P s.p s.d true s.h lam y ≤ 2 * ebarG s lam
def StExpandG2 (P : PiecesF) : Prop := ∀ (pad : U) (s : Step) (lam B : ℕ) (I : PInst), LevelOK2 P s lam → WFe (s.p * s.d) lam B I → BudG P pad.length s lam →
  (P.d s.h lam : ℤ) ^ nRectG s.p s.d * zval (s.p * s.d) I = (expandG P pad s I).1 + ((expandG P pad s I).2.map (zval s.K)).sum ∧
  (∀ J ∈ (expandG P pad s I).2, WFe s.K (lamNextG P s lam) (bNextG P s lam B) J) ∧
  (expandG P pad s I).2.length ≤ nPat P s lam ∧
  (expandG P pad s I).1.natAbs ≤ 2 ^ (Nat.size (nPat P s lam) + Nof s lam + s.d ^ 2 * (s.p * B + s.p ^ 2 * P.bits s.h lam + 1))
def ChainG2 (P : PiecesF) (K₀ : ℕ) : ℕ → ℕ → List Step → Prop
  | Kup, _, [] => Kup = K₀
  | Kup, lam, s :: r => Kup = s.p * s.d ∧ LevelOK2 P s lam ∧ ChainG2 P K₀ s.K (lamNextG P s lam) r
def StSolveG2 (P : PiecesF) : Prop := ∀ (pad : U) (K₀ : ℕ) (sched : List Step) (Kup lam B : ℕ) (I : PInst),
  ChainG2 P K₀ Kup lam sched → FitsG P pad.length Kup lam B 1 1 sched → WFe Kup lam B I → solveG P pad K₀ sched I = zval Kup I
def StChain2 : Prop := ∀ (P : PiecesF) (ρ : ℝ) (c x₀ : ℕ), Par P ρ c → P.m = 1 → 18 ≤ x₀ → c + 5 ≤ 2 ^ x₀ →
  ∀ l lam, 1 ≤ lam → ChainG2 P (K x₀ 0) (K x₀ l) lam (sched P x₀ l)
def StRate2 : Prop := ∀ c : ℕ, ∃ C₀ : ℕ, ∀ (P : PiecesF) (ρ : ℝ) (x₀ : ℕ), 1 / 2 ≤ ρ → ρ < 1 → Par P ρ c → P.m = 1 → 18 ≤ x₀ → c + 5 ≤ 2 ^ x₀ →
  ∀ l lam B : ℕ, 1 ≤ lam → 1 ≤ B →
    (needG P (K x₀ l) lam B 1 1 (sched P x₀ l) : ℝ) ≤
      e ρ x₀ l * (K x₀ l : ℝ) ^ 2 * lam + C₀ * (K x₀ l : ℝ) ^ 2 * Real.logb 2 (K x₀ l * (lam + B))
def StSeq2 : Prop := ∀ (P : PiecesF) (ρ : ℝ) (c x₀ : ℕ), 1 / 2 ≤ ρ → ρ < 1 → Par P ρ c → P.m = 1 → 18 ≤ x₀ → c + 5 ≤ 2 ^ x₀ →
  ∃ C₀ : ℕ, ∃ Q : (solverOf P).Seq (e ρ x₀) C₀, ∀ l, Q.idx l = idx P x₀ l
end GeneralPieces


