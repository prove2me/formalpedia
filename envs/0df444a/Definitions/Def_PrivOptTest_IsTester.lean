-- Prove2me | Definitions.Def_PrivOptTest_IsTester
-- name    : PrivOptTest_IsTester
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T16:58:23.479435+00:00
-- url     : https://prove2.me/theorems/839c107d-13be-4b1c-a28c-16d70ac98663
-- title:
--   The joint threshold loss $\mathrm{opt}_{\mathcal H}$ (3), the class $\mathcal H_{\mathrm{thr}}$ (6) and $\varepsilon$-private testers (Definition 1.2)
-- statement:
--   Alice's records are labelled $-1$ and Bob's $+1$. For a class $\mathcal H$ of $\{\pm1\}$-valued functions the **joint loss** (3) is
--   $$\mathrm{opt}_{\mathcal H}(S_A,S_B)=\min_{h\in\mathcal H}\Big(\sum_{x\in S_A}\mathbf 1\{h(x)\ne-1\}+\sum_{x\in S_B}\mathbf 1\{h(x)\ne+1\}\Big).$$
--   The class of **thresholds** (6) is $\mathcal H_{\mathrm{thr}}=\{h_\theta:\theta\in\mathbb R\}$ with $h_\theta(x)=1$ for $x\ge\theta$ and $h_\theta(x)=-1$ for $x<\theta$; on a finite domain $\mathcal X\subset\mathbb R$ it is used through its restriction to $\mathcal X$.
--
--   A protocol $\Pi$ on datasets in $\mathcal X^n$ with output in $\{\mathrm{Match},\mathrm{Far}\}$ is an **$\varepsilon$-private tester with resolution $t$ and failure probability $\beta$** for $\mathcal H$ if it is well formed and $\varepsilon$-differentially private on all inputs, $\Pr[\Pi(S_A,S_B)=\mathrm{Far}]\ge1-\beta$ whenever $\mathrm{opt}_{\mathcal H}(S_A,S_B)\ge t$, and $\Pr[\Pi(S_A,S_B)=\mathrm{Match}]\ge1-\beta$ whenever $\mathrm{opt}_{\mathcal H}(S_A,S_B)=0$. Definition 1.2 is the case $\beta=1/10$.
--
--   **Formalization Note** Datasets are sequences `Fin n → D`; a protocol on multisets is the special case that ignores the order. `true` stands for $+1$. `opt` is an infimum in $\mathbb N$, attained on every nonempty class. Definition 1.2's range $t\in[2n]$ is carried by the theorems.
-- source:
--   M. Haghifam, K. K. Patel, A. Blum, G. Fanti, J. Ziani, Should We Combine Our Data? Algorithms and Limits for Privately Assessing Data Sharing, arXiv:2611.03599 (manuscript sha256 4ac94dcf…), (3), p.3; (4), p.4; Definition 1.2, pp.3–4; (6), p.14

import Mathlib
import Definitions.Def_PrivLearn_Generic_Privacy
import Definitions.Def_PrivOptTest_Protocol

open MeasureTheory

namespace PrivOptTest

/-- The number of errors of `h` on the pooled data, inside (3), p.3 of arXiv:2611.03599 (manuscript
sha256 4ac94dcf…). Alice's records are labelled −1 and Bob's +1; `true` stands for +1 and `false` for −1. -/
def jointErrors {D : Type} {n : ℕ} (h : D → Bool) (SA SB : Fin n → D) : ℕ :=
  (Finset.univ.filter fun i => h (SA i) ≠ false).card +
    (Finset.univ.filter fun i => h (SB i) ≠ true).card

/-- **Joint loss in the disjoint-label setting, (3), p.3**:
`opt_H(S_A, S_B) = min_{h∈H} (Σ_{x∈S_A} 1{h(x) ≠ −1} + Σ_{x∈S_B} 1{h(x) ≠ +1})`.

**Formalization Note.** `sInf` on `ℕ` is attained on every nonempty `H`, and every class used here is
nonempty. On the empty class it would read 0. -/
noncomputable def opt {D : Type} {n : ℕ} (H : Set (D → Bool)) (SA SB : Fin n → D) : ℕ :=
  sInf ((fun h => jointErrors h SA SB) '' H)

/-- **Thresholds on the real line, (4), p.4 and (6), p.14**: `h_θ(x) = 1` for `x ≥ θ` and `h_θ(x) = −1`
for `x < θ`, with `θ ∈ ℝ`. A hypothesis is a function, not a cutoff. -/
def Hthr : Set (ℝ → Bool) :=
  {h | ∃ θ : ℝ, ∀ x, h x = decide (θ ≤ x)}

/-- The class `H_thr` restricted to a public domain `X ⊂ ℝ`. Only the values on the data enter `opt`. -/
def HthrOn (X : Finset ℝ) : Set (↥X → Bool) :=
  (fun h x => h (x : ℝ)) '' Hthr

/-- **ε-private tester with resolution `t` and failure probability `β`** (Definition 1.2, pp.3–4, with
0.9 replaced by `1 − β`; Definition 1.2 is `β = 1/10`). Fix a data space `D`, a class `H`, a dataset
size `n`. Then `Pr` is well-formed, is ε-private on all inputs, outputs `Far` with probability at least
`1 − β` when `opt_H ≥ t`, and `Match` with probability at least `1 − β` when `opt_H = 0`.

**Formalization Note.** A protocol on sequences `Fin n → D`. A multiset protocol is the special case
ignoring the order, so a lower bound over this class implies the multiset one. Definition 1.2's
`t ∈ [2n]` is a range for the parameter, carried by the theorems. -/
structure IsTester {D : Type} {n : ℕ} (Pr : Protocol (Fin n → D) Outcome) (H : Set (D → Bool))
    (ε : ℝ) (t : ℕ) (β : ℝ) : Prop where
  wellFormed : Pr.IsWellFormed
  privacy : Pr.IsPrivate ε
  soundness : ∀ SA SB : Fin n → D, t ≤ opt H SA SB →
    ENNReal.ofReal (1 - β) ≤ Pr.outputLaw SA SB {Sum.inl Outcome.far}
  completeness : ∀ SA SB : Fin n → D, opt H SA SB = 0 →
    ENNReal.ofReal (1 - β) ≤ Pr.outputLaw SA SB {Sum.inl Outcome.matched}

end PrivOptTest


