-- Prove2me | Definitions.Def_PiecesCountedStatement
-- name    : PiecesCountedStatement
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-04T23:58:54.580999+00:00
-- url     : https://prove2.me/theorems/0098c22a-e7f0-41dd-b03c-a1207ca2be81
-- title:
--   Pieces Counted Statement
-- statement:
--   Definitions and structural lemmas for Pieces Counted Statement, from Anthropic’s pinned ETH development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/statements/PiecesCountedStatement.lean

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_QueryMachines_Kernel
import Definitions.Def_QueryMachines_CombDefs
import Definitions.Def_QueryMachines_CombRunsStatement
import Definitions.Def_QueryMachines_Comb
import Definitions.Def_PiecesFromEightSquaresStatement
import Theorems.Thm_Groundwork_PolyT_elim
import Theorems.Thm_Groundwork_PolyT_length
import Theorems.Thm_Groundwork_PolyT_sum
attribute [local fun_prop] Groundwork.PolyT.length
attribute [local fun_prop] Groundwork.PolyT.sum


set_option autoImplicit false
section
section
namespace PiecesCounted
open Finset Groundwork Groundwork.Prog
structure Data where
  fam : (lam : ℕ) → Pieces.Family lam
  fn : (lam : ℕ) → Bool → Bool → ℤ → Pieces.Bits lam × Pieces.Bits lam → List Bool → ℤ
def Data.cap (D : Data) (lam : ℕ) (tr : Bool) (i : ℤ) : ℕ := if tr then (D.fam lam).ccol i else (D.fam lam).crow i
structure Data.Is (D : Data) (ρ : ℝ) (c : ℕ) : Prop where
  /-- ½ ≤ ρ < 1 real, c ≥ 1 an integer, d ≥ 1 -/
  rho_ge : 1 / 2 ≤ ρ
  rho_lt : ρ < 1
  c_pos : 1 ≤ c
  d_pos : ∀ lam, 1 ≤ lam → 1 ≤ (D.fam lam).d
  /-- (a) Σ_{i ∈ 𝓘} A_i = d·[x = v][y = u] -/
  sum : ∀ lam, 1 ≤ lam → ∀ x y u v, ∑ i ∈ (D.fam lam).I, (D.fam lam).A i x y u v = (D.fam lam).d * Pieces.cross x y u v
  /-- (b) A_i factors through c^row_i bits as a function of (x, y) and (u, v) -/
  row : ∀ lam, 1 ≤ lam → ∀ i ∈ (D.fam lam).I, ∀ x y u v, (D.fam lam).A i x y u v = ∑ θ ∈ words (D.cap lam false i), D.fn lam false false i (x, y) θ * D.fn lam false true i (u, v) θ
  /-- (b) and through c^col_i bits as a function of (x, u) and (y, v) -/
  col : ∀ lam, 1 ≤ lam → ∀ i ∈ (D.fam lam).I, ∀ x y u v, (D.fam lam).A i x y u v = ∑ θ ∈ words (D.cap lam true i), D.fn lam true false i (x, u) θ * D.fn lam true true i (y, v) θ
  /-- (b) where c^row_i + c^col_i ≤ 4ρλ + c·log(2λ) -/
  caps : ∀ lam, 1 ≤ lam → ∀ i ∈ (D.fam lam).I, ((D.cap lam false i + D.cap lam true i : ℕ) : ℝ) ≤ 4 * ρ * lam + c * Real.logb 2 (2 * lam)
  /-- (c) |𝓘| ≤ (2λ)^c -/
  card : ∀ lam, 1 ≤ lam → #(D.fam lam).I ≤ (2 * lam) ^ c
  /-- (c) d, the elements of 𝓘 and all values of the A_i and of the functions of these
      factorizations are below 2^{(2λ)^c} in absolute value -/
  size_d : ∀ lam, 1 ≤ lam → (D.fam lam).d < 2 ^ (2 * lam) ^ c
  size_I : ∀ lam, 1 ≤ lam → ∀ i ∈ (D.fam lam).I, |i| < 2 ^ (2 * lam) ^ c
  size_A : ∀ lam, 1 ≤ lam → ∀ i ∈ (D.fam lam).I, ∀ x y u v, |(D.fam lam).A i x y u v| < 2 ^ (2 * lam) ^ c
  size_f : ∀ lam, 1 ≤ lam → ∀ i ∈ (D.fam lam).I, ∀ tr side z, ∀ θ ∈ words (D.cap lam tr i), |D.fn lam tr side i z θ| < 2 ^ (2 * lam) ^ c
abbrev Question : Type := Unit ⊕ (Unit ⊕ ((Bool × ℤ) ⊕ ((ℤ × (List Bool × List Bool × List Bool × List Bool)) ⊕ ((Bool × Bool) × ℤ × (List Bool × List Bool × List Bool)))))
abbrev Answer : Type := ℤ ⊕ List ℤ
def toBits (n : ℕ) (l : List Bool) : Pieces.Bits n := fun j => l.getD j.val false
def Data.answer (D : Data) (lam : ℕ) : Question → Option Answer
  | .inl _ => some (.inl (D.fam lam).d)
  | .inr (.inl _) => some (.inr (D.fam lam).I.sort)
  | .inr (.inr (.inl q)) => if q.2 ∈ (D.fam lam).I then some (.inl (D.cap lam q.1 q.2)) else none
  | .inr (.inr (.inr (.inl q))) =>
    if q.1 ∈ (D.fam lam).I ∧ q.2.1.length = lam ∧ q.2.2.1.length = lam ∧ q.2.2.2.1.length = lam ∧ q.2.2.2.2.length = lam then
      some (.inl ((D.fam lam).A q.1 (toBits lam q.2.1) (toBits lam q.2.2.1) (toBits lam q.2.2.2.1) (toBits lam q.2.2.2.2))) else none
  | .inr (.inr (.inr (.inr q))) =>
    if q.2.1 ∈ (D.fam lam).I ∧ q.2.2.1.length = lam ∧ q.2.2.2.1.length = lam ∧ q.2.2.2.2.length = D.cap lam q.1.1 q.2.1 then
      some (.inl (D.fn lam q.1.1 q.1.2 q.2.1 (toBits lam q.2.2.1, toBits lam q.2.2.2.1) q.2.2.2.2)) else none
def Data.oracle (D : Data) (g : List Unit × Question) : Option Answer := if 1 ≤ g.1.length then D.answer g.1.length g.2 else none
def steps (c lam : ℕ) : ℕ := 2 ^ (c * lam)
def price (c : ℕ) (g : List Unit × Question) : ℕ := steps c g.1.length + 2
def room (c lam : ℕ) : ℕ := (2 ^ (c * lam) + (2 * lam) ^ c + 8) * ((2 * lam) ^ c + 8)
def Computes (Alg : Stepped (List Unit × Question) Answer) (D : Data) (c : ℕ) : Prop :=
  ∀ (g : List Unit × Question) (a : Answer), D.oracle g = some a → Alg.Runs g (steps c g.1.length) (room c g.1.length) a
structure IsPieces (ρ : ℝ) (c : ℕ) (D : Data) (Alg : Stepped (List Unit × Question) Answer) : Prop where
  is : D.Is ρ c
  polyTimeSteps : Nonempty (IsPolyT Alg)
  computes : Computes Alg D c
def Exist (ρ : ℝ) (c : ℕ) : Prop := ∃ D Alg, IsPieces ρ c D Alg
def ToPure : Prop := ∀ (D : Data) (ρ : ℝ) (c : ℕ), D.Is ρ c → ∀ lam, 1 ≤ lam → (D.fam lam).Is ρ c
def GrowWithTheParameters : Prop := ∀ (ρ ρ' : ℝ) (c c' : ℕ) (D : Data) (Alg : Stepped (List Unit × Question) Answer), ρ ≤ ρ' → ρ' < 1 → c ≤ c' → IsPieces ρ c D Alg → IsPieces ρ' c' D Alg
def passOrRun {Q : Type} [HasSize Q] (Alg : Stepped (List Unit × Question) Answer) : QueryMachines.QueryMachine Q Answer (Unit × (Q ⊕ (List Unit × Question))) Answer :=
  QueryMachines.QueryMachine.branch (fun p : Unit × (Q ⊕ (List Unit × Question)) => p.2) (QueryMachines.QueryMachine.query id) (QueryMachines.QueryMachine.lift Alg)
def withAlgorithm {Q α β : Type} [HasSize Q] (M : QueryMachines.QueryMachine (Q ⊕ (List Unit × Question)) Answer α β) (Alg : Stepped (List Unit × Question) Answer) : QueryMachines.QueryMachine Q Answer α β :=
  QueryMachines.QueryMachine.mapIn (fun a : α => ((), a)) (M.subst (passOrRun Alg))
def OracleFromAlgorithm : Prop := ∀ (Q α β : Type) [HasSize Q] (M : QueryMachines.QueryMachine (Q ⊕ (List Unit × Question)) Answer α β) (Alg : Stepped (List Unit × Question) Answer) (D : Data) (c : ℕ),
  Computes Alg D c → ∀ (O : Q → Option Answer) (w : Q → ℕ) (a : α) (T S Λ SQ : ℕ) (b : β), (∀ x v, O x = some v → size x + size v ≤ SQ) →
    M.Within (Sum.elim O fun g => if g.1.length ≤ Λ then D.oracle g else none) (Sum.elim (fun x => w x + 2) (price c)) a T S b →
      (withAlgorithm M Alg).Within O w a T (S + room c Λ + SQ + 4) b
def ofPadded (P : ClauseBound.Alg.PiecesF) (A : (lam : ℕ) → ℕ → Pieces.Four lam) (c : ℕ) (shift : ℕ → ℤ) : Data where
  fam lam :=
    { d := P.d 0 lam
      I := (range (P.cnt 0 lam)).image fun i : ℕ => (i : ℤ) + shift lam
      A := fun i => A lam (i - shift lam).toNat
      crow := fun i => P.cap false 0 lam (i - shift lam).toNat
      ccol := fun i => P.cap true 0 lam (i - shift lam).toNat }
  fn lam tr side i z θ :=
    if side then P.bot ((List.replicate (2 ^ (c * lam)) (), tr), (0, (i - shift lam).toNat), (ClauseBound.Alg.bitsOf z.1, ClauseBound.Alg.bitsOf z.2, θ))
    else P.top ((List.replicate (2 ^ (c * lam)) (), tr), (0, (i - shift lam).toNat), (ClauseBound.Alg.bitsOf z.1, ClauseBound.Alg.bitsOf z.2, θ))
def FromPadded : Prop := ∀ (ρ : ℝ) (c : ℕ) (P : ClauseBound.Alg.PiecesF) (A : (lam : ℕ) → ℕ → Pieces.Four lam) (val : AppRunningTime.ValQ → ℤ) (shift : ℕ → ℤ), AppRunningTime.IsPieces ρ c P A val →
  PolyT (fun u : List Unit => shift u.length) → (∀ lam, 1 ≤ lam → |shift lam| + (2 * lam) ^ c < 2 ^ (2 * lam) ^ c) →
    ∃ (c' : ℕ) (Alg : Stepped (List Unit × Question) Answer), c ≤ c' ∧ IsPieces ρ c' (ofPadded P A c shift) Alg
def MayAssume : Prop := ∀ (ρ : ℝ) (c : ℕ) (D : Data) (Alg : Stepped (List Unit × Question) Answer), IsPieces ρ c D Alg →
  ∃ (D' : Data) (Alg' : Stepped (List Unit × Question) Answer), IsPieces ρ (c + 2) D' Alg' ∧
    ∀ lam, (D'.fam lam).d = (D.fam lam).d ∧ (D'.fam lam).I = (D.fam lam).I ∧ (D'.fam lam).A = (D.fam lam).A ∧ ∀ tr i, D'.cap lam tr i ≤ 2 * lam
def EightSquarePieces : Prop := (∃ (c₀ : ℕ) (Alg : Stepped (List Unit × Question) Answer), 8 ≤ c₀ ∧ ∀ c : ℕ, c₀ ≤ c → IsPieces (11 / 12) c (ofPadded Eight.eightF Eight.A 0 fun _ => 0) Alg) ∧
  ∀ lam, 1 ≤ lam → ((ofPadded Eight.eightF Eight.A 0 fun _ => 0).fam lam).I = Finset.Icc 0 (Eight.tOf lam : ℤ) ∧ ((ofPadded Eight.eightF Eight.A 0 fun _ => 0).fam lam).d = 2 ^ Eight.tOf lam ∧
    ∀ i : ℕ, i ≤ Eight.tOf lam → ((ofPadded Eight.eightF Eight.A 0 fun _ => 0).fam lam).A i = Eight.A lam i ∧
      (ofPadded Eight.eightF Eight.A 0 fun _ => 0).cap lam false i = Eight.crow lam i ∧ (ofPadded Eight.eightF Eight.A 0 fun _ => 0).cap lam true i = Eight.ccol lam i ∧
      ((Eight.crow lam i + Eight.ccol lam i : ℕ) : ℝ) ≤ 11 * lam / 3 + 8
def HalfPieces : Prop := ∃ (c : ℕ) (D : Data) (Alg : Stepped (List Unit × Question) Answer), IsPieces (1 / Real.sqrt 2) c D Alg ∧
  ∀ lam, 1 ≤ lam → ∃ mu : Pieces.Bits lam → AppHalfPieces.Ptn, AppHalfPieces.IsMu lam (AppHalfPieces.hOf lam) mu ∧
    (D.fam lam).I = Finset.Icc (-(2 * (AppHalfPieces.hOf lam : ℤ))) (2 * (AppHalfPieces.hOf lam : ℤ)) ∧ (D.fam lam).d = (AppHalfPieces.hOf lam).factorial ∧
    ∀ s ∈ (D.fam lam).I, (∀ x y u v, ((D.fam lam).A s x y u v : ℚ) = AppHalfPieces.piece (AppHalfPieces.hOf lam) mu s x y u v) ∧
      D.cap lam false s = Nat.clog 2 (AppHalfPieces.Rrow (AppHalfPieces.hOf lam) s) ∧ D.cap lam true s = Nat.clog 2 (AppHalfPieces.Rcol (AppHalfPieces.hOf lam) s)
def HalfPiecesExist : Prop := ∃ c : ℕ, Exist (1 / Real.sqrt 2) c
def HalfPiecesFrom : Prop := AppRunningTime.ThmHalfPieces → FromPadded → HalfPieces
end PiecesCounted


