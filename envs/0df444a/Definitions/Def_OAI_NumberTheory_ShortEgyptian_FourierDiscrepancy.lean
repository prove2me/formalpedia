-- Prove2me | Definitions.Def_OAI_NumberTheory_ShortEgyptian_FourierDiscrepancy
-- name    : OAI_NumberTheory_ShortEgyptian_FourierDiscrepancy
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-15T21:21:28.184993+00:00
-- url     : https://prove2.me/theorems/b69c7977-837a-4cc8-9d19-63fcbe48fbed
-- title:
--   Character sums of sets and Fourier coefficients of weights on $\mathbb{Z}/q\mathbb{Z}$
-- statement:
--   Let $q\ge 1$ be an integer and let $\psi_q:\mathbb{Z}/q\mathbb{Z}\to\mathbb{C}$ be the standard additive character, $\psi_q(x)=\exp(2\pi i x/q)$, where $x$ is any integer representative of the residue class. The file defines:
--
--   1. **Character sum of a set.** For $A\subseteq\mathbb{Z}/q\mathbb{Z}$ and a frequency $k\in\mathbb{Z}/q\mathbb{Z}$,
--
--      $$S_A(k)=\sum_{a\in A}\psi_q(ka).$$
--
--   2. **Fourier coefficient of a weight.** For $\mu:\mathbb{Z}/q\mathbb{Z}\to\mathbb{R}$ and $k\in\mathbb{Z}/q\mathbb{Z}$,
--
--      $$\widehat{\mu}(k)=\sum_{x\in\mathbb{Z}/q\mathbb{Z}}\mu(x)\,\psi_q(-kx).$$
--
--   It also records that $|\psi_q(x)|=1$ for every $x$, that $S_A(0)=|A|$, and that $\widehat{\mu}(0)=1$ whenever $\sum_x\mu(x)=1$.
--
--   These are the Fourier-analytic quantities of the discrepancy argument. In the surrounding development they enter a convolution inequality: if $\mu\ge 0$ is a probability distribution on $\mathbb{Z}/q\mathbb{Z}$ and $A,B,I\subseteq\mathbb{Z}/q\mathbb{Z}$ satisfy $a+b\in I$ for all $a\in A$, $b\in B$, then
--
--   $$|A|\,|B|-\sum_{k\ne 0}|S_A(k)|\,|S_B(k)|\,|\widehat{\mu}(k)|\le q\,|B|\,\mu(I),$$
--
--   so a distribution whose nonzero Fourier coefficients are small must give substantial mass to $I$.
--
--   **Formalization Note** The Lean names are `charSum` and `probabilityFourier`, with the simp lemmas `stdAddChar_norm`, `charSum_zero` and `probabilityFourier_zero`. The character is Mathlib's `ZMod.stdAddChar`, and the instance `NeZero q` encodes $q\ge 1$.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/NumberTheory/ShortEgyptian/FourierDiscrepancy.lean

-- Generated from openai/math@1581d4c lean/OAI/NumberTheory/ShortEgyptian/FourierDiscrepancy.lean by skeleton subtraction
-- (upload_full_project.md Phase 3): Definitions bundle for the ShortEgyptianFractions mission closure.
-- Kept: reachable definitions/instances and the theorems their bodies or the node statements cite.
-- Project imports rewritten to platform modules; otherwise byte-identical to the source.
import Mathlib
import Definitions.Def_ShortEgyptianFractions
import Definitions.Def_OAI_NumberTheory_ShortEgyptian_Basic
import Definitions.Def_OAI_NumberTheory_ShortEgyptian_FirstDerivative
import Definitions.Def_OAI_NumberTheory_ShortEgyptian_ReciprocalDifferences
import Definitions.Def_OAI_NumberTheory_ShortEgyptian_IntervalDifferencing
import Definitions.Def_OAI_NumberTheory_ShortEgyptian_IteratedDifferencing
import Definitions.Def_OAI_NumberTheory_ShortEgyptian_ParameterBounds

namespace OAI

namespace ShortEgyptian

open scoped BigOperators
open Finset

noncomputable def charSum {q : ℕ} [NeZero q] (A : Finset (ZMod q)) (k : ZMod q) : ℂ :=
  ∑ a ∈ A, ZMod.stdAddChar (k * a)

noncomputable def probabilityFourier {q : ℕ} [NeZero q] (μ : ZMod q → ℝ) (k : ZMod q) : ℂ :=
  ∑ x : ZMod q, (μ x : ℂ) * ZMod.stdAddChar (-(k * x))

@[simp] theorem stdAddChar_norm {q : ℕ} [NeZero q] (x : ZMod q) :
    ‖ZMod.stdAddChar x‖ = 1 := by
  rw [ZMod.stdAddChar_apply]
  exact Circle.norm_coe _

@[simp] theorem charSum_zero {q : ℕ} [NeZero q] (A : Finset (ZMod q)) :
    charSum A 0 = A.card := by simp [charSum]

@[simp] theorem probabilityFourier_zero {q : ℕ} [NeZero q] (μ : ZMod q → ℝ)
    (hμ : ∑ x, μ x = 1) : probabilityFourier μ 0 = 1 := by
  simp only [probabilityFourier, zero_mul, neg_zero, AddChar.map_zero_eq_one, mul_one]
  exact_mod_cast hμ

end ShortEgyptian

end OAI


