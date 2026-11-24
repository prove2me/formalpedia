-- Prove2me | Definitions.Def_Development_AutomorphicSpectrum_Definitions_DivisibilityTowers_CompactGapsGE
-- name    : Development_AutomorphicSpectrum_Definitions_DivisibilityTowers_CompactGapsGE
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T01:38:14.783505+00:00
-- url     : https://prove2.me/theorems/3ca3c97a-a7f7-4d98-a172-7ae8f911869f
-- title:
--   Compact Gaps GE
-- statement:
--   Definitions and structural lemmas for Compact Gaps GE, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Definitions/DivisibilityTowers/CompactGapsGE.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MvPolynomial
namespace GlobalTheory.CompanionTheory.Ar.Top
abbrev RP (Ψ : Type) (N : ℕ) : Type := MvPolynomial (Ψ × Fin N) ℝ
abbrev RPA (Ψ : Type) (N : ℕ) : Type := MvPolynomial (Option (Ψ × Fin N)) ℝ
abbrev Wt (Ψ : Type) (N : ℕ) : Type := Ψ → Fin N → ℝ
def dimFl (Ψ : Type) [Fintype Ψ] (N : ℕ) : ℕ := Fintype.card Ψ * (N * (N - 1) / 2)
variable {Ψ : Type} [Fintype Ψ] {N : ℕ}
def permExp (σ : Ψ → Equiv.Perm (Fin N)) : (Ψ × Fin N) →₀ ℕ :=
  Finsupp.equivFunOnFinite.symm (fun x => N - 1 - ((σ x.1 x.2 : Fin N) : ℕ))
def degFl [DecidableEq Ψ] (F : RP Ψ N) : ℝ :=
  (-1) ^ dimFl Ψ N *
    ∑ σ : Ψ → Equiv.Perm (Fin N), (∏ τ, ((Equiv.Perm.sign (σ τ) : ℤ) : ℝ)) * F.coeff (permExp σ)
def linRoot (lam : Wt Ψ N) : RP Ψ N := -∑ x : Ψ × Fin N, C (lam x.1 x.2) * X x
def flagDeg [DecidableEq Ψ] (lam : Wt Ψ N) : ℝ := degFl (linRoot lam ^ dimFl Ψ N)
def toA (F : RP Ψ N) : RPA Ψ N := rename some F
def linA (lam : Wt Ψ N) (s : ℝ) : RPA Ψ N := toA (linRoot lam) + C s * X none
def pk (τ : Ψ) (k : ℕ) : RP Ψ N := ∑ i : Fin N, X (τ, i) ^ k
def pkLow (j : ℕ) (τ : Ψ) (k : ℕ) : RP Ψ N :=
  ∑ i ∈ Finset.univ.filter (fun i : Fin N => (i : ℕ) < j), X (τ, i) ^ k
def pLie (j : ℕ) (k : ℕ) : Ψ ⊕ Ψ → RP Ψ N
  | Sum.inl τ => pkLow j τ k
  | Sum.inr τ => ∑ i ∈ Finset.univ.filter (fun i : Fin N => j ≤ (i : ℕ)), (-X (τ, i)) ^ k
def Sh [DecidableEq Ψ] (j : ℕ) (τ : Ψ) (F : RP Ψ N) : ℝ :=
  degFl (∑ i ∈ Finset.univ.filter (fun i : Fin N => (i : ℕ) < j), pderiv (τ, i) F)
def Tot [DecidableEq Ψ] (τ : Ψ) (F : RP Ψ N) : ℝ := degFl (∑ i : Fin N, pderiv (τ, i) F)
def ent (lam : Wt Ψ N) (τ : Ψ) (i : ℕ) : ℝ := if h : i < N then lam τ ⟨i, h⟩ else 0
def gap (j : ℕ) (lam : Wt Ψ N) (τ : Ψ) : ℝ := ent lam τ (j - 1) - ent lam τ j
def Dominant (lam : Wt Ψ N) : Prop := ∀ τ (a b : Fin N), a ≤ b → lam τ b ≤ lam τ a
def RegDominant (lam : Wt Ψ N) : Prop := ∀ τ (a b : Fin N), a < b → lam τ b < lam τ a
def CompactGapsGE (j : ℕ) (c : ℝ) (lam : Wt Ψ N) : Prop :=
  ∀ τ (i : ℕ), i + 1 < N → i + 1 ≠ j → c ≤ ent lam τ i - ent lam τ (i + 1)
def IsRatWt (lam : Wt Ψ N) : Prop := ∀ τ i, ∃ q : ℚ, lam τ i = (q : ℝ)
def l1 (lam : Wt Ψ N) : ℝ := ∑ τ, ∑ i, |lam τ i|
def swapWt [DecidableEq Ψ] (τ : Ψ) (a b : Fin N) (lam : Wt Ψ N) : Wt Ψ N :=
  fun σ i => if σ = τ then lam σ (Equiv.swap a b i) else lam σ i
def rhoWt : Wt Ψ N := fun _ i => (N : ℝ) - 1 - (i : ℕ)
def NefThreshold (j : ℕ) (b : ℝ) (mu : Wt Ψ N) : Prop :=
  ∀ τ, 4 * (Fintype.card Ψ : ℝ) * ‖mu‖ ≤ (b - 2) * gap j mu τ
def InSmall (j : ℕ) (i : Fin N) : Prop := if j ≤ N - j then (i : ℕ) < j else j ≤ (i : ℕ)
def WeightHyp (j : ℕ) (u : Wt Ψ N) (g : ℝ) : Prop :=
  0 < g ∧ RegDominant u ∧ (∀ τ, g ≤ gap j u τ) ∧
    ∀ τ (a b : Fin N), InSmall j a → a ≠ b → g ≤ |u τ a - u τ b|
def bigB0 (u : Wt Ψ N) (g : ℝ) : ℝ := 4 * (Fintype.card Ψ : ℝ) * (N : ℝ) ^ 2 * (1 + ‖u‖ / g)
def spread (u : Wt Ψ N) : ℝ := ∑ τ, ((⨆ i, u τ i) - ⨅ i, u τ i)
def bigLam (B rd Lval : ℝ) : ℝ := Real.log (B * rd) + |Lval|
def deltaTerm [DecidableEq Ψ] (j p : ℕ) (τ : Ψ) (fr : ℕ → Ψ ⊕ Ψ) (k : ℕ) (Q : RP Ψ N) : ℝ :=
  Real.log p * k * ((∑' n : ℕ, ((p : ℝ) ^ k)⁻¹ ^ (n + 1) * degFl (pLie j (k - 1) (fr n) * Q)) -
    degFl (pkLow j τ (k - 1) * Q) / ((p : ℝ) - 1))
end GlobalTheory.CompanionTheory.Ar.Top


