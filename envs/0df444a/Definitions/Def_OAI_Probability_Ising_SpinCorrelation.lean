-- Prove2me | Definitions.Def_OAI_Probability_Ising_SpinCorrelation
-- name    : OAI_Probability_Ising_SpinCorrelation
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-14T21:58:18.669898+00:00
-- url     : https://prove2.me/theorems/dfa8a4c9-ca16-4912-8dfa-4405bf97324c
-- title:
--   Pin extensions, two-spin marginal tables and global spin reversal
-- statement:
--   Let $V=\{0,\dots,n-1\}$, let $F\subseteq V$ be a set of sites whose spins are fixed, and let $\tau\in\{-1,+1\}^V$ supply the fixed values. The file introduces the following.
--
--   1. **Pin extension.** For $\eta\in\{-1,+1\}^{V\setminus F}$, the configuration $\tau_F\oplus\eta\in\{-1,+1\}^V$ given by
--
--      $$(\tau_F\oplus\eta)_v=\begin{cases}\tau_v,& v\in F,\\ \eta_v,& v\notin F.\end{cases}$$
--
--   2. **Pin-extension bijection.** The map $\eta\mapsto\tau_F\oplus\eta$ is a bijection from $\{-1,+1\}^{V\setminus F}$ onto the set $\{\sigma\in\{-1,+1\}^V:\ \sigma_F=\tau_F\}$ of configurations obeying the pins; its inverse is restriction to $V\setminus F$.
--
--   3. **Pair table.** For a finite set $U$, a weight $W:\{-1,+1\}^U\to\mathbb{R}$ (not necessarily normalized) and sites $i,j\in U$, the two-spin table
--
--      $$T_{W,i,j}(s,t)=\sum_{\sigma:\ \sigma_i=s,\ \sigma_j=t}W(\sigma),\qquad s,t\in\{-1,+1\}.$$
--
--   4. **Global spin reversal.** The involution $\sigma\mapsto-\sigma$ of $\{-1,+1\}^U$, viewed as a permutation of configurations.
--
--   The pin extension makes precise that fixing the spins on $F$ eliminates those variables without deleting their interactions: a weight evaluated at $\tau_F\oplus\eta$ still contains every bond between $F$ and its complement. Pair tables reduce a many-spin weight to a two-spin table, to which the effective coupling of two-spin tables applies, and spin reversal shows that pair tables of flip-invariant (for instance zero-field) weights satisfy $T(s,t)=T(-s,-t)$.
--
--   **Formalization Note** The Lean names are `pinExtension F τ σ` (with the lemmas `pinExtension_agrees` and `pinExtension_apply`), the `Equiv` `pinExtensionEquiv F τ` onto the subtype `{σ // AgreesOn F σ τ}`, `pairTable W i j s t` (for a `Fintype` with decidable equality) and `spinFlipEquiv`. The file also contains private copies `dite_eq_left` and `dite_eq_right` of core rewriting lemmas.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Probability/Ising/SpinCorrelation.lean

-- Generated from openai/math@1581d4c lean/OAI/Probability/Ising/SpinCorrelation.lean by skeleton subtraction
-- (upload_full_project.md Phase 3): Definitions bundle for the BufferedIsing mission closure.
-- Kept: reachable definitions/instances and the theorems their bodies or the node statements cite.
-- Project imports rewritten to platform modules; otherwise byte-identical to the source.
import Mathlib
import Definitions.Def_BufferedIsing
import Definitions.Def_OAI_Probability_Ising_Basic
import Definitions.Def_OAI_Probability_Ising_Colorings
import Definitions.Def_OAI_Probability_Ising_EdwardsSokal
import Definitions.Def_OAI_Probability_Ising_TwoSpin

-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
private theorem dite_eq_left.{u} {c : Prop} {h : Decidable c} (hc : c) {α : Sort u} {t : c → α} {e : ¬c → α} : (dite c t e) = t hc := @dif_pos c h hc α t e
private theorem dite_eq_right.{u} {c : Prop} {h : Decidable c} (hc : ¬c) {α : Sort u} {t : c → α} {e : ¬c → α} : (dite c t e) = e hc := @dif_neg c h hc α t e

namespace OAI

open scoped BigOperators Classical

namespace BufferedIsing

/-- Extension by the actual common pins, in contrast to the deleted zero-field
comparison graph. -/
def pinExtension {n : ℕ} (F : Finset (Fin n)) (τ : Spins n)
    (σ : KeptVertex F → Bool) : Spins n :=
  fun v => if hv : v ∈ F then τ v else σ ⟨v, hv⟩

lemma pinExtension_agrees {n : ℕ} (F : Finset (Fin n)) (τ : Spins n)
    (σ : KeptVertex F → Bool) : AgreesOn F (pinExtension F τ σ) τ := by
  intro v hv
  simp only [pinExtension, dite_eq_left hv]

lemma pinExtension_apply {n : ℕ} (F : Finset (Fin n)) (τ : Spins n)
    (σ : KeptVertex F → Bool) (v : KeptVertex F) :
    pinExtension F τ σ v = σ v := by
  simp only [pinExtension, dite_eq_right v.property]

/-- Fixing sites is exactly elimination of their spin variables. This finite
bijection does not replace their interactions by deletion. -/
def pinExtensionEquiv {n : ℕ} (F : Finset (Fin n)) (τ : Spins n) :
    (KeptVertex F → Bool) ≃ {σ : Spins n // AgreesOn F σ τ} where
  toFun σ := ⟨pinExtension F τ σ, pinExtension_agrees F τ σ⟩
  invFun σ v := σ.val v
  left_inv σ := by ext v; exact pinExtension_apply F τ σ v
  right_inv σ := by
    apply Subtype.ext
    funext v
    by_cases hv : v ∈ F
    · simpa only [pinExtension, dite_eq_left hv] using (σ.property v hv).symm
    · simp only [pinExtension, dite_eq_right hv]

/-- A finite two-spin table extracted from a not necessarily normalized spin weight. -/
noncomputable def pairTable {V : Type*} [Fintype V] [DecidableEq V] (W : (V → Bool) → ℝ)
    (i j : V) (s t : Bool) : ℝ :=
  ∑ σ, if σ i = s ∧ σ j = t then W σ else 0

/-- Global spin reversal is a permutation of configurations. -/
def spinFlipEquiv (V : Type*) : (V → Bool) ≃ (V → Bool) where
  toFun σ v := !σ v
  invFun σ v := !σ v
  left_inv σ := by ext v; simp only [Bool.not_not]
  right_inv σ := by ext v; simp only [Bool.not_not]

end BufferedIsing

end OAI


