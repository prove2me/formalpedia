-- Prove2me | Definitions.Def_RealAPSP_Cover
-- name    : RealAPSP_Cover
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T20:57:07.400478+00:00
-- url     : https://prove2.me/theorems/0dc9939b-ae13-43ec-9701-57bcf2d66d69
-- title:
--   $|X|_{\pm\Delta}$, the approximate doubling condition, and subset sum covers
-- statement:
--   A set $Y\subseteq\mathbb R$ is a **$\Delta$-cover** of $X$ if every $x\in X$ has some $y\in Y$ with $x=y\pm\Delta$, and $|X|_{\pm\Delta}$ is the size of a minimum $\Delta$-cover. A set $X$ satisfies the **$\Delta$-approximate doubling condition** with constant $K$ if
--
--   $$|X+X|_{\pm\Delta}\le K\,|X|_{\pm\Delta}.$$
--
--   A pair $(\alpha,f)$ with $\alpha\in\mathbb R^d$ and $f:A\to\{0,1\}^d$ is a **$\Delta$-approximate subset sum cover** of $A$, of rank $d$, if $a=\alpha^{T}f(a)\pm\Delta$ for each $a\in A$.
--
--   These are the additive structure on which the hash to integers rests.
--
--   **Formalization Note** A set $A$ of size $m$ is an injective map from `Fin m`. Hash values are printed as a sign and a list of bits.
-- source:
--   Fischer, Polak, Schmidt, Real-to-Integer Reduction for All-Pairs Shortest Paths, arXiv:2611.04847 (held file sha256 a3dc0096…), §4.1, p.11 (PDF p.13); Definition 4.6, p.13 (PDF p.15)

import Mathlib
import Definitions.Def_RealAPSP_Machine

namespace RealAPSP

/-!
# Approximate covers, the approximate doubling condition, and subset sum covers

Fischer, Polak, Schmidt, arXiv:2611.04847 (held file sha256 a3dc0096…), §4.1, p.11 (PDF p.13): "For two sets X, C ⊆ R, we say
that C is a ∆-cover of X if X ⊆ ⋃_{c∈C} [c − ∆, c + ∆] … We denote by |X|_{±∆} the size of a minimum ∆-cover of X."
Definition 4.6, p.13 (PDF p.15): "Let A ⊆ R. A pair (α, f), where α ∈ R^d and f : A → {0, 1}^d, is called a ∆-approximate subset
sum cover of A if it satisfies a = αᵀf(a) ± ∆ for each a ∈ A. We call d the rank of the subset sum cover."

**Formalization Note.**
* For a finite `X` and `∆ ≥ 0`, `X` is a `∆`-cover of itself, so the infimum is over a nonempty set, and `|∅|_{±∆} = 0`.
* A set `A ⊆ ℝ` of size `m` is an injective `a : Fin m → ℝ`, and `f` is indexed by `Fin m`.
* Lemma 4.8's input and output layouts are given by `coverInts`, `coverReals` and `readSigned`.
-/

/-- `Y` is a `∆`-cover of `X`. -/
def IsCover (Δ : ℝ) (X Y : Finset ℝ) : Prop := ∀ x ∈ X, ∃ y ∈ Y, |x - y| ≤ Δ

/-- `|X|_{±∆}`, the size of a minimum `∆`-cover of `X`. -/
noncomputable def coverNumber (Δ : ℝ) (X : Finset ℝ) : ℕ :=
  sInf {c | ∃ Y : Finset ℝ, Y.card = c ∧ IsCover Δ X Y}

/-- The set of values of `a`. -/
noncomputable def valueSet {m : ℕ} (a : Fin m → ℝ) : Finset ℝ := Finset.univ.image a

open Pointwise in
/-- The `∆`-approximate doubling condition `|A + A|_{±∆} ≤ K·|A|_{±∆}`. -/
def HasDoubling (K Δ : ℝ) (X : Finset ℝ) : Prop :=
  (coverNumber Δ (X + X) : ℝ) ≤ K * coverNumber Δ X

/-- `(α, f)` is a `∆`-approximate subset sum cover of the set of values of `a`, of rank `d` (Definition 4.6). -/
def IsSubsetSumCover {m : ℕ} (Δ : ℝ) (a : Fin m → ℝ) (d : ℕ) (α : Fin d → ℝ) (f : Fin m → Fin d → Bool) : Prop :=
  ∀ i, |a i - ∑ l, α l * (if f i l then 1 else 0)| ≤ Δ

/-- Integer input cells for a subset sum cover: the bits `f i l`, row-major. -/
def coverInts {m d : ℕ} (f : Fin m → Fin d → Bool) : List ℤ :=
  (List.finRange m).flatMap fun i => (List.finRange d).map fun l => if f i l then 1 else 0

/-- Real input cells for a subset sum cover: the values of `a`, then `α`. -/
def coverReals {m d : ℕ} (a : Fin m → ℝ) (α : Fin d → ℝ) : List ℝ :=
  List.ofFn a ++ List.ofFn α

/-- The integer with sign cell `base` (`1` means negative) and bits at the `b` cells from `base + 1`,
least significant first. -/
noncomputable def readSigned (σ : State) (base b : ℕ) : ℤ :=
  (if σ.imem (outCell base) = 1 then -1 else 1) *
    ∑ l ∈ Finset.range b, (2 : ℤ) ^ l * (if σ.imem (outCell (base + 1 + l)) = 0 then 0 else 1)

end RealAPSP


