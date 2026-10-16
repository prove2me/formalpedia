-- Prove2me | Definitions.Def_OAI_NumberTheory_ShortEgyptian_EmpiricalDiscrepancy
-- name    : OAI_NumberTheory_ShortEgyptian_EmpiricalDiscrepancy
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-15T21:25:27.568562+00:00
-- url     : https://prove2.me/theorems/f8ae5451-3c83-4506-9792-9d703f360cd1
-- title:
--   Empirical distribution and character averages of an indexed family of residues
-- statement:
--   Let $\alpha$ be a finite index set with $|\alpha|$ elements, let $q\ge 1$, and let $v=(v_i)_{i\in\alpha}$ be a family of residues $v_i\in\mathbb{Z}/q\mathbb{Z}$. Write $\psi_q(x)=\exp(2\pi i x/q)$ for the standard additive character of $\mathbb{Z}/q\mathbb{Z}$.
--
--   1. **Empirical mass.** For $x\in\mathbb{Z}/q\mathbb{Z}$,
--
--      $$\mu_v(x)=\sum_{i\in\alpha}\frac{\mathbf 1[v_i=x]}{|\alpha|}=\frac{\#\{i\in\alpha:\ v_i=x\}}{|\alpha|},$$
--
--      the proportion of indices whose residue equals $x$.
--
--   2. **Indexed character average.** For a frequency $k\in\mathbb{Z}/q\mathbb{Z}$,
--
--      $$A_v(k)=\frac{1}{|\alpha|}\sum_{i\in\alpha}\psi_q(k\,v_i).$$
--
--   When $\alpha$ is nonempty, $\mu_v$ is a probability distribution on $\mathbb{Z}/q\mathbb{Z}$, and its Fourier coefficient $\sum_x\mu_v(x)\psi_q(-kx)$ equals $A_v(-k)$. This translates distributional statements into counting statements about the family: in the surrounding development it is shown that if $\alpha$ is nonempty, $0<\delta\le 1/256$, $H\ge 1$ with $2H\delta^4\ge 1$, and $|A_v(l)|\le\delta^3$ for all integers $1\le l\le H$, then at least $\delta|\alpha|/2$ indices $i$ have the least nonnegative representative of $-v_i$ below $\delta q$.
--
--   **Formalization Note** The Lean names are `empiricalMass` and `indexedCharAverage`, with the character `ZMod.stdAddChar`. If the index type is empty, both quantities are 0 because Lean's division by zero gives 0.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/NumberTheory/ShortEgyptian/EmpiricalDiscrepancy.lean

-- Generated from openai/math@1581d4c lean/OAI/NumberTheory/ShortEgyptian/EmpiricalDiscrepancy.lean by skeleton subtraction
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
import Definitions.Def_OAI_NumberTheory_ShortEgyptian_FourierDiscrepancy
import Definitions.Def_OAI_NumberTheory_ShortEgyptian_WindowSpectrum
import Definitions.Def_OAI_NumberTheory_ShortEgyptian_WindowDiscrepancy

namespace OAI

universe uα

namespace ShortEgyptian

open scoped BigOperators
open Finset

noncomputable def empiricalMass {α : Type uα} [Fintype α] {q : ℕ} [NeZero q]
    (v : α → ZMod q) (x : ZMod q) : ℝ :=
  ∑ i, if v i = x then (1 : ℝ) / Fintype.card α else 0

noncomputable def indexedCharAverage {α : Type uα} [Fintype α] {q : ℕ} [NeZero q]
    (v : α → ZMod q) (k : ZMod q) : ℂ :=
  (∑ i, ZMod.stdAddChar (k * v i)) / Fintype.card α

end ShortEgyptian

end OAI


