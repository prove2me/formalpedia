-- Prove2me | Definitions.Def_BartlettNN_Sigmoid_Classification
-- name    : BartlettNN_Sigmoid_Classification
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-05T00:51:32.29679+00:00
-- url     : https://prove2.me/theorems/e266eaa7-c019-402b-8eb9-1dcd5b11f7e3
-- title:
--   The double-sample margin event of display (1)
-- statement:
--   Let $H$ be a class of real-valued functions on $X$, let $\gamma>0$ and $\varepsilon\in\mathbb R$, and let $z=((x_i,y_i))_{i=1}^m$ and $\tilde z=((\tilde x_i,\tilde y_i))_{i=1}^m$ be two labelled samples, with labels $y\in\{-1,1\}$ (Lean: `true` is $+1$, `false` is $-1$). With the clipping function $\pi_\gamma(a)=\max(-\gamma,\min(\gamma,a))$, the **double-sample event** of display (1) in the proof of Theorem 2 is the set of pairs $(z,\tilde z)$ for which some $h\in H$ satisfies
--
--   $$\frac1m\bigl|\{i:|\pi_\gamma(h(\tilde x_i))-\gamma\tilde y_i|\ge\gamma\}\bigr|\;\ge\;\frac1m\bigl|\{i:\pi_\gamma(h(x_i))\ne\gamma y_i\}\bigr|+\frac\varepsilon2.$$
--
--   The paper assumes throughout that every set it considers is measurable (p. 526); this set is named so that the restated Theorem 2 can carry that assumption for it explicitly.
--
--   **Formalization Note.** The pair is `(z, z̃)`: the first component is the training sample, the second the ghost sample. Sample indices are $0$-based. At $m=0$ both fractions are Lean's $0/0=0$; the theorem that uses the event assumes $m\ge1$.
-- source:
--   Bartlett, The Sample Complexity of Pattern Classification with Neural Networks, IEEE Trans. Inform. Theory 44 (1998), pp. 526–528, Section II and proof of Theorem 2, display (1); https://doi.org/10.1109/18.661502

import Mathlib
import Definitions.Def_BartlettNN_Margin_Classification
import Definitions.Def_BartlettNN_Margin_Squash

namespace BartlettNN.Sigmoid

/-- The double-sample event appearing in display (1) of the proof of Theorem 2. -/
noncomputable def doubleSampleEvent {X : Type*} (H : Set (X → ℝ))
    (γ ε : ℝ) (m : ℕ) :
    Set ((Fin m → X × Bool) × (Fin m → X × Bool)) :=
  {zz | ∃ h ∈ H,
    ((Finset.univ.filter fun i : Fin m =>
      γ ≤ |BartlettNN.Margin.squash γ (h (zz.2 i).1) - γ * BartlettNN.Margin.pm (zz.2 i).2|).card : ℝ) / m ≥
    ((Finset.univ.filter fun i : Fin m =>
      BartlettNN.Margin.squash γ (h (zz.1 i).1) ≠ γ * BartlettNN.Margin.pm (zz.1 i).2).card : ℝ) / m + ε / 2}

end BartlettNN.Sigmoid


