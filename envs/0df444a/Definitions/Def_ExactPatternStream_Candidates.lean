-- Prove2me | Definitions.Def_ExactPatternStream_Candidates
-- name    : ExactPatternStream_Candidates
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T11:05:14.958338+00:00
-- url     : https://prove2.me/theorems/9887a098-cc1b-4375-8eaf-fadc21375c33
-- title:
--   (17), (20), §8 — $A_i$, $M_i$, $W_i$, heavy levels, the implication (20)
-- statement:
--   $A_i=\{x\in[0\,.\,.\,|T_i|]:A^{(T)}_i[x]=1\}$. The candidate set is
--   $$M_i=\{x\in A_i:T_i[x\,.\,.\,x+m_i)=P_i[1\,.\,.\,m_i],\ e_i(x)\le|\overline T_i|,\ \overline T_i[(x+m_i)w_i\,.\,.\,e_i(x))=\mathrm{Res}_i\}.$$
--   The weight-eligible positions are $W_i=\{x\in[0\,.\,.\,|T_i|]:e_i(x)\le|\overline T_i|,\ \mathrm{wt}(\overline T_i[xw_i\,.\,.\,e_i(x)))\ge\tau\}$, and level $j$ is heavy if $\mathrm{wt}(V_j')\ge2\tau$. For $1\le r\le h$ and $x\in A_r$, (20) is the implication
--   $$T_r[x\,.\,.\,x+m_r)=P_r[1\,.\,.\,m_r]\implies\hat T_{r-1}[xg_{r-1}\,.\,.\,(x+m_r)g_{r-1})=\hat P_{r-1}[g_{r-1}\,.\,.\,|P_r|g_{r-1}).$$
--   They organize the descent from a reported occurrence at the top level to a true occurrence.
--
--   **Formalization Note** The equalities in $M_i$ and (20) are of labels. $\tau$ is a real parameter, set to $m/(4\mathcal L)$ where used.
-- source:
--   Gawrychowski, Janczewski, Jin, Nelson, An Improved Streaming Algorithm for Exact Pattern Matching (preprint, STOC 2027 submission, sha256 351218cb…), §8.1–§8.2, pp.22–23 (PDF 23–24), eqs. (17), (20)

import Mathlib
import Definitions.Def_ExactPatternStream_Strings
import Definitions.Def_ExactPatternStream_ParseTree
import Definitions.Def_ExactPatternStream_Build

namespace ExactPatternStream

/-! # Candidate sets, heavy levels, and the implication (20)

Gawrychowski, Janczewski, Jin, Nelson (preprint, sha256 351218cb…), §8.1–§8.2, pp.22–23 (PDF 23–24), eqs.
(17), (20).

**Formalization Note.** `τ = m/(4𝓛)` is a real number, a parameter here. `Ai` ranges over `[0 . . |T_i|]`
inclusive. Equalities of `T_i` with `P_i` in (17) and (20) are of **labels**, not of subtrees, which is
what makes them testable. `leq L x` is the antecedent of (20) and `paddedEq` its conclusion, read in the
level below. -/

namespace Level

variable (L : Level)

/-- `A_i = {x ∈ [0 . . |T_i|] : A^(T)_i[x] = 1}`. -/
def Ai : Set ℕ := {x | x ≤ L.T.length ∧ L.AT.getD x false = true}

/-- The candidate set `M_i` of (17). -/
def Mi : Set ℕ :=
  {x | x ∈ L.Ai ∧ slice (labels L.T) x (x + L.mi) = slice (labels L.P) 1 (L.mi + 1) ∧
    L.e x ≤ L.Tbar.length ∧
    slice L.Tbar ((x + L.mi) * L.w) (L.e x) = L.Res}

/-- The weight-eligible positions `W_i`, for a threshold `τ`, p.23. -/
def Wi (τ : ℝ) : Set ℕ :=
  {x | x ≤ L.T.length ∧ L.e x ≤ L.Tbar.length ∧
    τ ≤ (wt (slice L.Tbar (x * L.w) (L.e x)) : ℝ)}

/-- Level `j < h` is heavy when `wt(V'_j) ≥ 2τ`, p.23. -/
def IsHeavy (τ : ℝ) : Prop := 2 * τ ≤ (wt L.V' : ℝ)

/-- The antecedent of (20) at level `r`: `T_r[x . . x + m_r) = P_r[1 . . m_r]`. -/
def labelsAgree (x : ℕ) : Prop :=
  slice (labels L.T) x (x + L.mi) = slice (labels L.P) 1 (L.mi + 1)

end Level

/-- The implication (20) at `(r, x)`, with `Lr` level `r` and `Ld` level `r - 1`:
`T_r[x . . x + m_r) = P_r[1 . . m_r] ⟹ T̂_{r-1}[x g_{r-1} . . (x + m_r) g_{r-1}) = P̂_{r-1}[g_{r-1} . . |P_r| g_{r-1})`. -/
def Implication20 (Ld Lr : Level) (x : ℕ) : Prop :=
  Lr.labelsAgree x →
    slice Ld.hatT (x * Ld.g) ((x + Lr.mi) * Ld.g) = slice Ld.hatP Ld.g (Lr.P.length * Ld.g)

end ExactPatternStream


