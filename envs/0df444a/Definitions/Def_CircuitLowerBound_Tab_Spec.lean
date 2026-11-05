-- Prove2me | Definitions.Def_CircuitLowerBound_Tab_Spec
-- name    : CircuitLowerBound_Tab_Spec
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-04T17:53:42.247756+00:00
-- url     : https://prove2.me/theorems/6da2cf63-54ce-45c7-b6fc-343a93796ba5
-- title:
--   Spec
-- statement:
--   Definitions and structural lemmas for Spec, from Anthropic’s pinned ETH development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/CircuitLowerBound/Tab/Spec.lean

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_CircuitLowerBound_Interfaces
import Mathlib.SetTheory.Cardinal.NatCard
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Finset.Lattice.Fold
set_option autoImplicit false
section
section
namespace CircuitLowerBound.Tab
open ENP Turing
def ops {K : Type} {Γ : K → Type} {Λ σ : Type} : TM2.Stmt Γ Λ σ → ℕ
  | .push _ _ q => ops q + 1
  | .peek _ _ q => ops q + 1
  | .pop _ _ q => ops q + 1
  | .load _ q => ops q
  | .branch _ q₁ q₂ => max (ops q₁) (ops q₂)
  | .goto _ => 0
  | .halt => 0
def pref {α : Type} : List (Option α) → List α
  | [] => []
  | none :: _ => []
  | some a :: L => a :: pref L
instance (tm : FinTM2) : Fintype tm.Λ := tm.ΛFin
instance (tm : FinTM2) : Fintype tm.σ := tm.σFin
instance (tm : FinTM2) : Fintype tm.K := tm.kFin
variable (N : TM2ComputableAux Bool Bool)
def dep : ℕ := max 1 (Finset.univ.sup fun l : N.tm.Λ => ops (N.tm.m l))
def lamOf : ℕ := Nat.size (2 * dep N + 2)
abbrev Win : Type := ∀ k : N.tm.K, Fin (dep N) → Option (N.tm.Γ k)
abbrev Case : Type := Option N.tm.Λ × N.tm.σ × Win N
noncomputable def nc : ℕ := Nat.card (Case N)
noncomputable def ec [Finite (Case N)] : Case N ≃ Fin (nc N) := Finite.equivFin _
def nxt (γ : Case N) : N.tm.Cfg :=
  match γ.1 with
  | none => ⟨none, γ.2.1, fun k => pref (List.ofFn (γ.2.2 k))⟩
  | some l => TM2.stepAux (N.tm.m l) γ.2.1 fun k => pref (List.ofFn (γ.2.2 k))
inductive Atom
  | lab (l : Option N.tm.Λ)
  | var (v : N.tm.σ)
  | len (k : N.tm.K) (n : Fin (2 * dep N + 1))
  | cell (k : N.tm.K) (x : Option (N.tm.Γ k))
  | cs (γ : Case N)
  | pre (i : Fin (nc N + 1))
  | u
structure Spec [Finite (Case N)] (α : Atom N → ℕ → ℕ → Bool) (b Q P : ℕ) : Prop where
  /-- at every time before the last some case holds -/
  preTop : ∀ t < 2 ^ b, α (.pre (Fin.last _)) t 0 = true
  preBot : ∀ t < 2 ^ b, α (.pre 0) t 0 = false
  preStep : ∀ t < 2 ^ b, ∀ i : Fin (nc N), α (.pre i.succ) t 0 = false ∨ α (.pre i.castSucc) t 0 = true ∨ α (.cs ((ec N).symm i)) t 0 = true
  /-- the case that holds is that of the row -/
  csLab : ∀ t < 2 ^ b, ∀ γ : Case N, α (.cs γ) t 0 = true → α (.lab γ.1) t 0 = true
  csVar : ∀ t < 2 ^ b, ∀ γ : Case N, α (.cs γ) t 0 = true → α (.var γ.2.1) t 0 = true
  csCell : ∀ t < 2 ^ b, ∀ (γ : Case N) (k : N.tm.K) (j : Fin (dep N)), α (.cs γ) t 0 = true → α (.cell k (γ.2.2 k j)) t j = true
  /-- the case fixes label, state and the new tops of the next row -/
  nxLab : ∀ t < 2 ^ b, ∀ (γ : Case N) (x : Option N.tm.Λ), α (.cs γ) t 0 = true → (α (.lab x) (t + 1) 0 = true ↔ x = (nxt N γ).l)
  nxVar : ∀ t < 2 ^ b, ∀ (γ : Case N) (x : N.tm.σ), α (.cs γ) t 0 = true → (α (.var x) (t + 1) 0 = true ↔ x = (nxt N γ).var)
  nxLen : ∀ t < 2 ^ b, ∀ (γ : Case N) (k : N.tm.K) (n : Fin (2 * dep N + 1)), α (.cs γ) t 0 = true → (α (.len k n) t 0 = true ↔ (n : ℕ) = ((nxt N γ).stk k).length)
  nxCell : ∀ t < 2 ^ b, ∀ (γ : Case N) (k : N.tm.K) (x : Option (N.tm.Γ k)) (j : ℕ), j < ((nxt N γ).stk k).length → α (.cs γ) t 0 = true →
    (α (.cell k x) (t + 1) j = true ↔ x = ((nxt N γ).stk k)[j]?)
  /-- below the new top the stack is what lay below the old top -/
  copy : ∀ t < 2 ^ b, ∀ q < 2 ^ Q, ∀ (k : N.tm.K) (n : Fin (2 * dep N + 1)) (x : Option (N.tm.Γ k)), α (.len k n) t 0 = true →
    α (.cell k x) (t + 1) (q + n) = α (.cell k x) t (q + dep N)
  /-- the first row: the machine is started on 1^P 0 y -/
  iLab : ∀ x : Option N.tm.Λ, α (.lab x) 0 0 = true ↔ x = some N.tm.main
  iVar : ∀ x : N.tm.σ, α (.var x) 0 0 = true ↔ x = N.tm.initialState
  iCell : ∀ q < 2 ^ Q, ∀ k : N.tm.K, k ≠ N.tm.k₀ → ∀ x : Option (N.tm.Γ k), α (.cell k x) 0 q = true ↔ x = none
  iSome : ∀ q < 2 ^ Q, α (.cell N.tm.k₀ none) 0 q = true ∨ α (.cell N.tm.k₀ (some (N.inputAlphabet.symm false))) 0 q = true ∨ α (.cell N.tm.k₀ (some (N.inputAlphabet.symm true))) 0 q = true
  iMost : ∀ q < 2 ^ Q, ∀ x x' : Option (N.tm.Γ N.tm.k₀), x ≠ x' → α (.cell N.tm.k₀ x) 0 q = false ∨ α (.cell N.tm.k₀ x') 0 q = false
  iBlank : ∀ q < 2 ^ Q, α (.cell N.tm.k₀ none) 0 q = true → α (.cell N.tm.k₀ none) 0 (q + 1) = true
  uStep : ∀ q < 2 ^ Q, α .u 0 (q + 1) = true → α .u 0 q = true
  uP : α .u 0 P = true
  uP1 : α .u 0 (P + 1) = false
  uOne : ∀ q < 2 ^ Q, α .u 0 (q + 1) = true → α (.cell N.tm.k₀ (some (N.inputAlphabet.symm true))) 0 q = true
  cellP : α (.cell N.tm.k₀ (some (N.inputAlphabet.symm false))) 0 P = true
  /-- the last row: halted, with the output 1 -/
  fLab : α (.lab none) (2 ^ b) 0 = true
  fVar : α (.var N.tm.initialState) (2 ^ b) 0 = true
  fOut0 : α (.cell N.tm.k₁ (some (N.outputAlphabet.symm true))) (2 ^ b) 0 = true
  fOut1 : α (.cell N.tm.k₁ none) (2 ^ b) 1 = true
  fOther : ∀ k : N.tm.K, k ≠ N.tm.k₁ → α (.cell k none) (2 ^ b) 0 = true
end CircuitLowerBound.Tab
namespace CircuitLowerBound
open ENP Turing Tab
def lits (c : TCl) : List TLit := [c.1, c.2.1, c.2.2]
def GoodCode (e : MCode) : Prop := ∀ c ∈ tab e, ∀ l ∈ lits c, 1 ≤ l.1 ∧ l.1 < 2 ^ kb e ∧ l.2.2.2.1 ≤ 2 ^ lam e
def holdsT (α : ℕ → ℕ → ℕ → Bool) (b P t q : ℕ) (l : TLit) : Prop := α l.1 (tval b t l.2.1) (qval P q l.2.2.1 + l.2.2.2.1) = l.2.2.2.2
def SatT (X : List TCl) (b Q P : ℕ) : Prop := ∃ α : ℕ → ℕ → ℕ → Bool, ∀ c ∈ X, ∀ t < 2 ^ b, ∀ q < 2 ^ Q, ∃ l ∈ lits c, holdsT α b P t q l
def StPack : Prop := ∀ (e : MCode) (L P : ℕ), GoodCode e → Fits e L P → (Sat (tabF e L P) ↔ SatT (tab e) (bt e L) (bq e L) P)
def StSpec : Prop := ∀ (N : TM2ComputableAux Bool Bool) [Finite (Case N)] (b P : ℕ), 1 ≤ b → P + 2 ≤ 2 ^ b →
  ((∃ α, Spec N α b (b + lamOf N) P) ↔ Acc N P (2 ^ b))
def StSpecTab : Prop := ∀ (N : TM2ComputableAux Bool Bool) [Finite (Case N)], (∀ k, Finite (N.tm.Γ k)) →
  ∃ e : MCode, GoodCode e ∧ lam e = lamOf N ∧ ∀ b Q P : ℕ, SatT (tab e) b Q P ↔ ∃ α, Spec N α b Q P
end CircuitLowerBound


