-- Prove2me | Definitions.Def_allikvere_stopping_set
-- name    : allikvere_stopping_set
-- status  : Definition
-- author  : @mysticflounder
-- created : 2026-09-10T10:52:34.576616+00:00
-- url     : https://prove2.me/theorems/268f50b0-d947-448f-b533-b2cb16002a09
-- title:
--   First-passage stopping set used in Allikvere Lemma 6.3
-- statement:
--   For $x\in\mathbb{R}$ with $x>1$, fix the Allikvere parameter $\alpha=1.001$ and set $$m_0=\left\lfloor\frac{\log x}{100000}\right\rfloor.$$ Define the Tao (5.10) range shell by $$R_x=\left[ e^{-(\log x)^{7/10}}\left(\frac{4}{3}\right)^{m_0}x,\ e^{(\log x)^{7/10}}\left(\frac{4}{3}\right)^{m_0}x\right].$$ The full stopping set is $$E'(x)=\left\{M\in\mathbb{N}: M\text{ is positive and odd},\ M\in R_x,\ x<\operatorname{Syracuse}^j(M)\ (j<m_0),\ 1\le\operatorname{Syracuse}^{m_0}(M)\le x\right\}.$$ For $W\subseteq\mathbb{R}$, `allikvereRealPreimage W` is $$\{M\in\mathbb{N}:(M: \mathbb{R})\in W\}.$$ The Lean definition remains total outside this exposition domain; this public description is restricted to $x>1$ so the logarithmic powers and floor convention have their intended interpretation. It is a definition-only interface and asserts no equidistribution or first-passage theorem.
-- source:
--   Jaan Allikvere, "Almost all Collatz orbits attain almost bounded values in natural density", Zenodo record 21499244, July 2026, version 2, author/title lines 32-33 and Allikvere Lemma 6.3 lines 1126-1208 in local allikvere-2026-07-natural-density-v2.tex; the range shell follows Tao (5.10), not Tao Corollary 6.3. https://zenodo.org/records/21499244

/-
Copyright (c) 2026 Adam McKenna. All rights reserved.
Released under GPL-3.0-or-later as described in the file LICENSE.
Authors: Adam McKenna.
-/

import Mathlib
import Definitions.Def_syracuseStep

set_option autoImplicit false

noncomputable section

def allikvereM0 (x : ℝ) : ℕ :=
  Nat.floor (Real.log x / 100000)

def allikvereRange5010 (x : ℝ) (m₀ M : ℕ) : Prop :=
  Real.exp (-(Real.rpow (Real.log x) (7 / 10 : ℝ))) *
      (4 / 3 : ℝ) ^ m₀ * x ≤ (M : ℝ) ∧
    (M : ℝ) ≤ Real.exp (Real.rpow (Real.log x) (7 / 10 : ℝ)) *
      (4 / 3 : ℝ) ^ m₀ * x

def allikvereFirstPassageAt (x : ℝ) (m₀ M : ℕ) : Prop :=
  (∀ j : ℕ, j < m₀ → x < ((syracuseStep^[j]) M : ℕ)) ∧
    1 ≤ ((syracuseStep^[m₀]) M : ℕ) ∧
    ((syracuseStep^[m₀]) M : ℕ) ≤ x

def allikvereEPrime (x : ℝ) : Set ℕ :=
  {M | Odd M ∧ 0 < M ∧
    allikvereRange5010 x (allikvereM0 x) M ∧
    allikvereFirstPassageAt x (allikvereM0 x) M}

def allikvereRealPreimage (W : Set ℝ) : Set ℕ :=
  {M | (M : ℝ) ∈ W}

end


