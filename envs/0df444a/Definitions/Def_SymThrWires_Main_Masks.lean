-- Prove2me | Definitions.Def_SymThrWires_Main_Masks
-- name    : SymThrWires_Main_Masks
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-11T00:15:46.249548+00:00
-- url     : https://prove2.me/theorems/b564e9ee-8240-4cd4-b941-7901626bb323
-- title:
--   Newton coefficients c_a, the threshold polynomial P_{τ,D}, and random label subsets
-- statement:
--   For nonnegative integers $\tau$ and $a$, the **Newton coefficient** of the cutoff $1[\,\cdot\le\tau]$ is
--   $$c_a=\sum_{i=0}^{\min(a,\tau)}(-1)^{a-i}\binom ai\in\mathbb Z ,$$
--   and for $D\ge 0$ and $G$ variables $y_1,\dots,y_G$ the **threshold polynomial** is $P_{\tau,D}(y)=\sum_{a=0}^D c_a\,e_a(y)$, with $e_a$ the elementary symmetric polynomial of degree $a$.
--
--   For a probability $p$ and an event $E$ about subsets $S$ of the labels $\{1,\dots,G\}$, the probability of $E$ when $S$ contains each label independently with probability $p$ is $\sum_{S\in E}p^{|S|}(1-p)^{G-|S|}$.
--
--   These carry Lemma 6.1 (integer threshold masks) and Lemma 6.3 (filter guarantees).
--
--   **Formalization Note.** `thresholdPoly τ D G` is an `MvPolynomial (Fin G) ℤ` built from `MvPolynomial.esymm`. `bernoulliSubsetProb G p E` is the explicit finite sum over `Finset (Fin G)`, so no measure theory is involved.
-- source:
--   Dev Nag, Near-Cubic Gate and Near-Quartic Wire Lower Bounds for SYM∘THR Circuits, STOC 2027 submission, Zenodo doi:10.5281/zenodo.23847026 (sha256 02f54f02…), p. 19, Lemma 6.1 (c_a, P_{τ,D}); p. 20, Lemma 6.3 (random label set S)

import Mathlib

/-!
# Newton coefficients of the integer threshold mask, and random label subsets

Dev Nag, *Near-Cubic Gate and Near-Quartic Wire Lower Bounds for SYM∘THR Circuits*, STOC 2027
submission, Zenodo doi:10.5281/zenodo.23847026, p. 19 (Lemma 6.1: `c_a`, `P_{τ,D}`) and p. 20
(Lemma 6.3: a random set of labels containing each label independently with probability `π0`).
-/

namespace SymThrWires.Main

/-- `c_a = Σ_{i=0}^{min(a,τ)} (−1)^{a−i} (a choose i)` (Lemma 6.1). -/
def newtonCoeff (τ a : ℕ) : ℤ :=
  ∑ i ∈ Finset.range (min a τ + 1), (-1) ^ (a - i) * (a.choose i : ℤ)

/-- `P_{τ,D}(y) = Σ_{a=0}^{D} c_a e_a(y)` in the variables `y_1, …, y_G`, where `e_a` is the
elementary symmetric polynomial of degree `a` (Lemma 6.1). -/
noncomputable def thresholdPoly (τ D G : ℕ) : MvPolynomial (Fin G) ℤ :=
  ∑ a ∈ Finset.range (D + 1), MvPolynomial.C (newtonCoeff τ a) * MvPolynomial.esymm (Fin G) ℤ a

open Classical in
/-- The probability, under the random set `S ⊆ Fin G` that contains each label independently with
probability `p`, of the event `E`: `Σ_{S : E S} p^{|S|} (1 − p)^{G − |S|}`. -/
noncomputable def bernoulliSubsetProb (G : ℕ) (p : ℝ) (E : Finset (Fin G) → Prop) : ℝ :=
  ∑ S : Finset (Fin G), if E S then p ^ S.card * (1 - p) ^ (G - S.card) else 0

end SymThrWires.Main


