-- Prove2me | Definitions.Def_BlockOrthoCSP_Decide_NumberField
-- name    : BlockOrthoCSP_Decide_NumberField
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-10T19:13:09.305205+00:00
-- url     : https://prove2.me/theorems/836ca7b0-2ea1-4d30-9dc0-cd1145c210e0
-- title:
--   The working field $K$ of (F.13), its roots of unity $\mu(K)$, the exponent $e_K$ and $L_q$
-- statement:
--   For a constraint language $\mathcal F$,
--   $$K = \mathbb Q\big(\{f(a), \overline{f(a)} : f \in \mathcal F,\ a \in D^{r_f}\}\big) \subseteq \mathbb C \qquad (F.13)$$
--   is a conjugation-stable number field. $\mu(K) = K^\times \cap \mu_\infty$ is its finite cyclic group of roots of unity, $e_K$ is the exponent of $\mu(K)$ (the least $e \ge 1$ with $\xi^e = 1$ for all $\xi \in \mu(K)$), and $L_q = \operatorname{lcm}(1,\dots,q)$.
-- source:
--   Liu, Meng, From Block Orthogonality to Decidability in Complex-Weighted Counting CSP, arXiv:2608.14845 (PDF sha256 ad21e5d7…), p. F-14, Eq. (F.13); p. F-6; p. F-34 (§F.8)

import Mathlib
import Definitions.Def_BlockOrthoCSP_Decide_Instance
import Definitions.Def_BlockOrthoCSP_Decide_Purification

set_option autoImplicit false

namespace BlockOrthoCSP.Decide

open ComplexConjugate

/-- The conjugation-stable number field `K = ℚ({f(a), conj f(a) : f ∈ F, a ∈ D^{r_f}})` of (F.13),
p. F-14, as a subfield of `ℂ`. -/
noncomputable def fieldK {q : ℕ} (F : Finset (CFn q)) : IntermediateField ℚ ℂ :=
  IntermediateField.adjoin ℚ {z : ℂ | ∃ f ∈ F, ∃ a : Fin f.1 → Fin q, z = f.2 a ∨ z = conj (f.2 a)}

/-- `µ(K) = K^× ∩ µ∞`, the roots of unity of `K` (p. F-6). -/
def muK {q : ℕ} (F : Finset (CFn q)) : Set ℂ :=
  {ξ | ξ ∈ fieldK F ∧ ξ ∈ muInf}

/-- `e_K`, the exponent of the finite group `µ(K)`: the least positive `e` with `ξ^e = 1` for
every `ξ ∈ µ(K)` (p. F-6, used in §F.8). -/
noncomputable def eK {q : ℕ} (F : Finset (CFn q)) : ℕ :=
  sInf {e : ℕ | 0 < e ∧ ∀ ξ ∈ muK F, ξ ^ e = 1}

/-- `L_q = lcm(1, …, q)` (§F.8). -/
def Lq (q : ℕ) : ℕ := (Finset.Icc 1 q).lcm id

end BlockOrthoCSP.Decide


