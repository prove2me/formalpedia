-- Prove2me | Definitions.Def_BirthdayEntropy_Soundness_Supplement_Agreement
-- name    : BirthdayEntropy_Soundness_Supplement_Agreement
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-15T21:18:23.038005+00:00
-- url     : https://prove2.me/theorems/ea12c3ff-0218-4603-a5e1-4fdc51c446fb
-- title:
--   Selected-family agreement and surviving-view laws
-- statement:
--   Let $H$ be a finite set of distinct Boolean labelled $\ell$-views on $n$ coordinates. Define $q_{\rm con}(H)$ by counting ordered pairs with at least one conflicting common bit, normalized by $|H|^2$. For a global Boolean assignment $g$, let $A_g(H)$ count all views whose restriction is selected. Define
--
--   $$f^*(H)=1-\frac{\max_g A_g(H)}{\binom n\ell}.$$
--
--   The maximum ranges over the nonempty finite set of all assignments. Define original-family coordinate incidences $z_i$, heavy coordinates by $z_i\ge(\ell/n)/8$, their strict complement $L$, any heavy-coordinate majority choice, the heavy-disagreement fraction $\varepsilon$, and the actual surviving subset $G$. The survivor law is uniform on $G$ and requires $G\ne\varnothing$; its view law is its pushforward. The ambient law is uniform on all views, with nonemptiness derived from $\ell\le n$. Conditional answer entropy is computed using the signed-set representation of each label, conditional on its view. All laws and entropies use the published finite-law library.
--
--   These definitions preserve missing views and multiple answers, and provide the computed quantities for Appendix A. SmallError is exactly regime (20), used only in A.2 and A.5. Outside the stated theorem domains, empty-family normalized counts are totalized to zero; no empty survivor probability law is constructed.
-- source:
--   Alexandru Popa, STOC 2027 submission #907 (October 2026), https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/907.pdf, §2 and Appendix A, PDF pp4,18–21 / printed pp3,17–20

import Mathlib
import Definitions.Def_BirthdayEntropy_Soundness_Graph
import Definitions.Def_BirthdayEntropy_Soundness_Counting

noncomputable section
open scoped Classical

namespace BirthdayEntropy.Soundness.Supplement
open OAI.ThorpCompatibility

/-- §2, PDF p4 / printed p3. Restrict a global assignment to one view. -/
def restriction {n ℓ : ℕ} (g : Fin n → Bool) (S : View n ℓ) : Vertex n ℓ :=
  ⟨S, fun i => g i.val⟩

/-- Existence of any differing bit; pairs are ordered and sampled with replacement. -/
def disagrees {n ℓ : ℕ} (v w : Vertex n ℓ) : Prop :=
  ∃ i : Fin n, (i, false) ∈ signed v ∧ (i, true) ∈ signed w ∨
    (i, true) ∈ signed v ∧ (i, false) ∈ signed w

def qcon {n ℓ : ℕ} (H : Finset (Vertex n ℓ)) : ℝ :=
  ((H ×ˢ H).filter (fun vw => disagrees vw.1 vw.2)).card / (H.card : ℝ)^2

/-- Count represented restrictions over all views, including missing views. -/
def agreementCount {n ℓ : ℕ} (H : Finset (Vertex n ℓ)) (g : Fin n → Bool) : ℕ :=
  (Finset.univ.filter (fun S : View n ℓ => restriction g S ∈ H)).card

/-- A maximum of a finite nonempty set of assignments, hence attained. -/
def bestAgreement {n ℓ : ℕ} (H : Finset (Vertex n ℓ)) : ℕ :=
  Finset.univ.sup' Finset.univ_nonempty (agreementCount H)

def fstar {n ℓ : ℕ} (H : Finset (Vertex n ℓ)) : ℝ :=
  1 - (bestAgreement H : ℝ) / Nat.choose n ℓ

/-- Original-H coordinate and bit incidences (Appendix A, PDF p18 / printed p17). -/
def incidence {n ℓ : ℕ} (H : Finset (Vertex n ℓ)) (i : Fin n) : ℝ :=
  (H.filter (fun v => i ∈ v.1.val)).card / (H.card : ℝ)

def bitCount {n ℓ : ℕ} (H : Finset (Vertex n ℓ)) (i : Fin n) (b : Bool) : ℕ :=
  (H.filter (fun v => (i,b) ∈ signed v)).card

def heavy {n ℓ : ℕ} (H : Finset (Vertex n ℓ)) : Finset (Fin n) :=
  Finset.univ.filter (fun i => ratio n ℓ / 8 ≤ incidence H i)

def low {n ℓ : ℕ} (H : Finset (Vertex n ℓ)) : Finset (Fin n) :=
  Finset.univ \ heavy H

/-- Every tie-breaking choice is allowed; values outside heavy coordinates are irrelevant. -/
def IsMajority {n ℓ : ℕ} (H : Finset (Vertex n ℓ)) (g : Fin n → Bool) : Prop :=
  ∀ i ∈ heavy H, bitCount H i (!(g i)) ≤ bitCount H i (g i)

def heavyErrorEvent {n ℓ : ℕ} (H : Finset (Vertex n ℓ))
    (g : Fin n → Bool) (v : Vertex n ℓ) : Prop :=
  ∃ i ∈ heavy H, (i, !(g i)) ∈ signed v

def heavyError {n ℓ : ℕ} (H : Finset (Vertex n ℓ)) (g : Fin n → Bool) : ℝ :=
  (H.filter (heavyErrorEvent H g)).card / (H.card : ℝ)

def survivors {n ℓ : ℕ} (H : Finset (Vertex n ℓ)) (g : Fin n → Bool) :
    Finset (Vertex n ℓ) :=
  H.filter (fun v => ¬ heavyErrorEvent H g v)

/-- Only the small-error lemmas use regime (20); not the agreement theorem. -/
def SmallError {n ℓ : ℕ} (H : Finset (Vertex n ℓ)) (g : Fin n → Bool) : Prop :=
  qcon H < ratio n ℓ / 32 ∧ heavyError H g ≤ 16 * qcon H / ratio n ℓ ∧
    16 * qcon H / ratio n ℓ < 1/2

def lowFraction {n ℓ : ℕ} (H : Finset (Vertex n ℓ)) : ℝ :=
  (low H).card / (n : ℝ)

/-- Uniform law on every possible view, with positivity derived from ell≤n. -/
def allViewLaw (n ℓ : ℕ) (hℓn : ℓ ≤ n) : Law (View n ℓ) := by
  have hc : 0 < Fintype.card (View n ℓ) := by
    rw [card_view]
    exact Nat.choose_pos hℓn
  letI : Nonempty (View n ℓ) := Fintype.card_pos_iff.mp hc
  exact Law.uniform

def lowIncidence {n ℓ : ℕ} (μ : Law (View n ℓ)) (L : Finset (Fin n)) : ℝ :=
  μ.mean (fun S => ((S.val ∩ L).card : ℝ)) / (ℓ : ℝ)

/-- This actual conditional law is defined only for a nonempty survivor set. -/
def survivorLaw {n ℓ : ℕ} (H : Finset (Vertex n ℓ)) (g : Fin n → Bool)
    (hG : (survivors H g).Nonempty) : Law (Vertex n ℓ) :=
  uniformOn (survivors H g) hG

def survivorViews {n ℓ : ℕ} (H : Finset (Vertex n ℓ)) (g : Fin n → Bool)
    (hG : (survivors H g).Nonempty) : Law (View n ℓ) :=
  (survivorLaw H g hG).map Sigma.fst

/-- The signed label is injective within each fixed view, so it encodes A|S exactly. -/
def answerEntropy {n ℓ : ℕ} (H : Finset (Vertex n ℓ)) (g : Fin n → Bool)
    (hG : (survivors H g).Nonempty) : ℝ :=
  (survivorLaw H g hG).condEntropy signed Sigma.fst

end BirthdayEntropy.Soundness.Supplement


