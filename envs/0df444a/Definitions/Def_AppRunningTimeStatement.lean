-- Prove2me | Definitions.Def_AppRunningTimeStatement
-- name    : AppRunningTimeStatement
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-04T22:19:33.057423+00:00
-- url     : https://prove2.me/theorems/4374a26b-b3ad-408b-a27d-a12638651716
-- title:
--   App Running Time Statement
-- statement:
--   Definitions and structural lemmas for App Running Time Statement, from Anthropic’s pinned ETH development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/statements/AppRunningTimeStatement.lean

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ClauseBound_Gen_Defs
import Definitions.Def_ClauseBoundStatement
import Definitions.Def_FixedWidthVariableBoundStatement
import Definitions.Def_ThreeSatRateStatement
import Definitions.Def_LevelsStatement
import Definitions.Def_PiecesStatement
import Definitions.Def_AppHalfPiecesStatement
import Theorems.Thm_Groundwork_PolyT_length
import Theorems.Thm_Groundwork_PolyT_sum
attribute [local fun_prop] Groundwork.PolyT.length
attribute [local fun_prop] Groundwork.PolyT.sum


set_option autoImplicit false
section
section
namespace AppRunningTime
open Finset Groundwork Groundwork.Prog PaddedDescent.F ClauseBound.Alg ClauseBound.Gen Levels.Gen
abbrev ValQ : Type := U × (U × ℕ) × (List Bool × List Bool × List Bool × List Bool)
structure IsPieces (ρ : ℝ) (c : ℕ) (P : PiecesF) (A : (lam : ℕ) → ℕ → Pieces.Four lam) (val : ValQ → ℤ) : Prop where
  /-- ½ ≤ ρ < 1 real, c ≥ 1 an integer, d ≥ 1 -/
  rho_ge : 1 / 2 ≤ ρ
  rho_lt : ρ < 1
  c_pos : 1 ≤ c
  d_pos : ∀ lam, 1 ≤ lam → 1 ≤ P.d 0 lam
  /-- (a) Σ_{i ∈ 𝓘} A_i = d·[x = v][y = u] -/
  sum : ∀ lam, 1 ≤ lam → ∀ x y u v, ∑ i ∈ range (P.cnt 0 lam), A lam i x y u v = P.d 0 lam * Pieces.cross x y u v
  /-- (b) A_i factors through c^row_i bits as a function of (x,y) and (u,v) -/
  row : ∀ lam, 1 ≤ lam → ∀ pad : U, 2 ^ (c * lam) ≤ pad.length → ∀ i < P.cnt 0 lam, ∀ x y u v, A lam i x y u v =
    ∑ θ ∈ words (P.cap false 0 lam i), P.top ((pad, false), (0, i), (bitsOf x, bitsOf y, θ)) * P.bot ((pad, false), (0, i), (bitsOf u, bitsOf v, θ))
  /-- (b) and through c^col_i bits as a function of (x,u) and (y,v) -/
  col : ∀ lam, 1 ≤ lam → ∀ pad : U, 2 ^ (c * lam) ≤ pad.length → ∀ i < P.cnt 0 lam, ∀ x y u v, A lam i x y u v =
    ∑ θ ∈ words (P.cap true 0 lam i), P.top ((pad, true), (0, i), (bitsOf x, bitsOf u, θ)) * P.bot ((pad, true), (0, i), (bitsOf y, bitsOf v, θ))
  /-- (b) where c^row_i + c^col_i ≤ 4ρλ + c·log(2λ) -/
  caps : ∀ lam, 1 ≤ lam → ∀ i < P.cnt 0 lam, ((P.cap false 0 lam i + P.cap true 0 lam i : ℕ) : ℝ) ≤ 4 * ρ * lam + c * Real.logb 2 (2 * lam)
  /-- (c) |𝓘| ≤ (2λ)^c (so the elements of 𝓘 are below 2^{(2λ)^c} as well) -/
  card : ∀ lam, 1 ≤ lam → P.cnt 0 lam ≤ (2 * lam) ^ c
  /-- (c) d and all values of the A_i and of the functions of these factorizations are below
      2^{(2λ)^c} in absolute value -/
  size_d : ∀ lam, 1 ≤ lam → P.d 0 lam < 2 ^ (2 * lam) ^ c
  size_A : ∀ lam, 1 ≤ lam → ∀ i < P.cnt 0 lam, ∀ x y u v, |A lam i x y u v| < 2 ^ (2 * lam) ^ c
  size_f : ∀ lam, 1 ≤ lam → ∀ pad : U, 2 ^ (c * lam) ≤ pad.length → ∀ i < P.cnt 0 lam, ∀ tr (x y : Pieces.Bits lam) θ,
    |P.top ((pad, tr), (0, i), (bitsOf x, bitsOf y, θ))| < 2 ^ (2 * lam) ^ c ∧ |P.bot ((pad, tr), (0, i), (bitsOf x, bitsOf y, θ))| < 2 ^ (2 * lam) ^ c
  /-- (c) one algorithm computes each of them, and 𝓘, c^row_i, c^col_i, from λ, i and the arguments
      within 2^{cλ} operations. Here: |𝓘|, d, c^row_i, c^col_i are computed in time polynomial in λ;
      the two functions of a factorization and the value of A_i are polynomial-time in the length of
      pad and arguments, and right once the pad has 2^{cλ} units. -/
  time_cnt : Unary fun lam : U => P.cnt 0 lam.length
  time_d : PolyT fun lam : U => P.d 0 lam.length
  time_cap : Unary fun p : Bool × U × ℕ => P.cap p.1 0 p.2.1.length p.2.2
  time_top : PolyT P.top
  time_bot : PolyT P.bot
  time_val : PolyT val
  val_eq : ∀ lam, 1 ≤ lam → ∀ pad : U, 2 ^ (c * lam) ≤ pad.length → ∀ i < P.cnt 0 lam, ∀ x y u v,
    val (pad, (List.replicate lam (), i), (bitsOf x, bitsOf y, bitsOf u, bitsOf v)) = A lam i x y u v
def Exist (ρ : ℝ) (c : ℕ) : Prop := ∃ P A val, IsPieces ρ c P A val
def MayAssume : Prop := ∀ (ρ : ℝ) (c : ℕ) (P : PiecesF) A val, IsPieces ρ c P A val → ∃ P' : PiecesF, IsPieces ρ c P' A val ∧
  (∀ lam, P'.cnt 0 lam = P.cnt 0 lam ∧ P'.d 0 lam = P.d 0 lam) ∧ ∀ tr lam i, P'.cap tr 0 lam i ≤ 2 * lam
def Cases (K g : ℕ) (ζ : ℝ) (P : ℕ) (c : Fin g → Fin g → ℕ) : Prop :=
  (g = 3 * K ^ 8 ∧ ζ = 1 / (2 * K)) ∨ (K ∣ g ∧ (∀ a b, a ≠ b → (c a b : ℝ) ≤ (P : ℝ) / g) ∧ (K : ℝ) * Real.log (2 * g * K) ≤ 2 * ζ ^ 2 * g)
noncomputable def Lof (K g : ℕ) (ζ : ℝ) (P U : ℕ) : ℕ := ⌈((U : ℝ) + 2 * ζ * g * P) / (K : ℝ) ^ 2⌉₊
def B'of (K g P B : ℕ) : ℕ := (2 * g * P + K - 1) / K + g ^ 2 * B
def SomeGrouping : Prop := ∀ (K g : ℕ) (ζ : ℝ) (P : ℕ) (c : Fin g → Fin g → ℕ), 2 ≤ K → 2 ≤ g → 0 < ζ → ζ ≤ 1 → 1 ≤ P →
  (∀ a b, c a b = c b a) → (∀ a, ∑ b ∈ univ.erase a, c a b ≤ P) → Cases K g ζ P c →
  ∃ χ : Fin g → Fin K, (∀ γ, K * #{a | χ a = γ} ≤ 2 * g) ∧
    ∀ γ γ', γ ≠ γ' → ∑ a with χ a = γ, ∑ b with χ b = γ', c a b ≤ Lof K g ζ P (∑ a, ∑ b ∈ univ.erase a, c a b)
def GroupingSizes : Prop := ∀ (K g : ℕ) (ζ : ℝ) (P : ℕ) (c : Fin g → Fin g → ℕ), 2 ≤ K → 2 ≤ g → 0 < ζ → ζ ≤ 1 → 1 ≤ P →
  (∀ a, ∑ b ∈ univ.erase a, c a b ≤ P) → Cases K g ζ P c → K ≤ g ∧ Lof K g ζ P (∑ a, ∑ b ∈ univ.erase a, c a b) ≤ g * P + 1
noncomputable def alpha' (ρ : ℝ) : ℝ := Real.logb 2 (1 / ρ)
structure PartA (ρ : ℝ) (x₀ : ℕ) : Prop where
  /-- log K_ℓ = (3x₀+6)·2^ℓ − 6ℓ − 2x₀ − 6 -/
  logK : ∀ l : ℕ, Real.logb 2 (K x₀ l) = (3 * x₀ + 6) * 2 ^ l - 6 * l - 2 * x₀ - 6
  /-- so K_ℓ < K_{ℓ+1} ≤ K_ℓ^10 -/
  K_lt_le : ∀ l : ℕ, K x₀ l < K x₀ (l + 1) ∧ K x₀ (l + 1) ≤ K x₀ l ^ 10
  /-- ½ρ^ℓ ≤ e_ℓ ≤ 0.85·ρ^ℓ -/
  e_bounds : ∀ l : ℕ, 1 / 2 * ρ ^ l ≤ e ρ x₀ l ∧ e ρ x₀ l ≤ 0.85 * ρ ^ l
  /-- where ρ^ℓ ≤ ((3x₀+6)/log K_ℓ)^{α'} -/
  rho_pow : ∀ l : ℕ, ρ ^ l ≤ ((3 * x₀ + 6) / Real.logb 2 (K x₀ l)) ^ alpha' ρ
def PartB (ρ : ℝ) (x₀ C₀ : ℕ) : Prop := ∃ (run : U × U × PInst → ℤ) (need : ℕ → ℕ → ℕ → ℕ), PolyT run ∧
  (∀ (pad : U) (l lam B : ℕ) (I : PInst), 1 ≤ lam → 1 ≤ B → WFe (K x₀ l) lam B I → 2 ^ need l lam B ≤ pad.length →
    run (pad, List.replicate l (), I) = zval (K x₀ l) I) ∧
  ∀ l lam B : ℕ, 1 ≤ lam → 1 ≤ B →
    (need l lam B : ℝ) ≤ e ρ x₀ l * (K x₀ l : ℝ) ^ 2 * lam + C₀ * (K x₀ l : ℝ) ^ 2 * Real.logb 2 (K x₀ l * (lam + B))
structure ThmRunningTime : Prop where
  /-- (a) needs neither pieces nor 2^x₀ ≥ c + 5. -/
  a : ∀ (ρ : ℝ) (x₀ : ℕ), 1 / 2 ≤ ρ → ρ < 1 → 18 ≤ x₀ → PartA ρ x₀
  /-- (b); C₀ depends only on c. -/
  b : ∀ c : ℕ, ∃ C₀ : ℕ, ∀ (ρ : ℝ) (x₀ : ℕ), Exist ρ c → 18 ≤ x₀ → c + 5 ≤ 2 ^ x₀ → PartB ρ x₀ C₀
  /-- (c), first sentence: one machine counts the satisfying assignments of a k-CNF with m ≥ 1
  clauses in which every variable occurs within C·2^{C·km/(log₂(m+2))^{α'}} steps; machine and C do
  not depend on
  k, which is part of the input. The appendix takes any formula, numbers the variables that occur in
  a preparation and counts their assignments; here the input is promised to contain every one of its
  n
  variables, so there is no preparation. All steps are counted, so the polynomial in the length of
  the formula is absorbed. As a statement this only says that some machine exists: it does not name
  the algorithm. -/
  c_m : ∀ (ρ : ℝ) (c : ℕ), Exist ρ c → SatM.CountInRate (SatM.rPow (alpha' ρ))
  /-- (c), second sentence: for every fixed k and n variables, 2^{O(n·log log n/(log n)^{α'})}
  steps. The appendix asks in addition that a number between 0.85ρ^ℓ and ρ^ℓ can be computed from ℓ
  in time polynomial
  in K_ℓ; the proof in this development does not need that. Likewise: some machine exists; the
  statement does not name the algorithm. -/
  c_n : ∀ (ρ : ℝ) (c : ℕ), Exist ρ c → ∀ k : ℕ, 1 ≤ k → SatK.CountInRateN k (SatK.rN 1 (alpha' ρ))
  /-- (d): one machine decides 3-SAT on n variables within 2^{O(n/(log n)^{α'/10})} steps. Here this
  follows from the bound with the exponent 3/19 (`Sat3.inRateTM`), because α'/10 ≤ 1/10 < 3/19; the
  appendix's proof of (d), through the sparsification lemma with ε = (log n)^{−α'/10}, is not
  formalized. -/
  d : ∀ (ρ : ℝ) (c : ℕ), Exist ρ c → Sat3.InRateTM (alpha' ρ / 10)
def ThmHalfPieces : Prop := ∃ (c : ℕ) (P : PiecesF) (A : (lam : ℕ) → ℕ → Pieces.Four lam) (val : ValQ → ℤ), IsPieces (1 / Real.sqrt 2) c P A val ∧
  ∀ lam, 1 ≤ lam → ∃ mu : Pieces.Bits lam → AppHalfPieces.Ptn, AppHalfPieces.IsMu lam (AppHalfPieces.hOf lam) mu ∧
    P.cnt 0 lam = 4 * AppHalfPieces.hOf lam + 1 ∧ P.d 0 lam = (AppHalfPieces.hOf lam).factorial ∧
    ∀ i < P.cnt 0 lam, (∀ x y u v, (A lam i x y u v : ℚ) = AppHalfPieces.piece (AppHalfPieces.hOf lam) mu ((i : ℤ) - 2 * AppHalfPieces.hOf lam) x y u v) ∧
      P.cap false 0 lam i = Nat.clog 2 (AppHalfPieces.Rrow (AppHalfPieces.hOf lam) ((i : ℤ) - 2 * AppHalfPieces.hOf lam)) ∧
      P.cap true 0 lam i = Nat.clog 2 (AppHalfPieces.Rcol (AppHalfPieces.hOf lam) ((i : ℤ) - 2 * AppHalfPieces.hOf lam))
def BoundInM : Prop := SatM.TargetSqrt
end AppRunningTime


