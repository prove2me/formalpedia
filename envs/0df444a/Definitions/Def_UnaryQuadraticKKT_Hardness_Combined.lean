-- Prove2me | Definitions.Def_UnaryQuadraticKKT_Hardness_Combined
-- name    : UnaryQuadraticKKT_Hardness_Combined
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-09T15:45:28.729698+00:00
-- url     : https://prove2.me/theorems/2104ed52-c305-48d1-9181-dc765c8eb2e9
-- title:
--   Disjoint auxiliary blocks, the combined polynomial and its affine change of domain
-- statement:
--   For the actual dyadic terms of $\widetilde P$, let $m_r=k_r+2$ and index an auxiliary coordinate by $(r,j)$ with $1\le j\le m_r$. Original coordinates are shared by every occurrence of a factor. The combined function is
--   $$G(x,u)=\sum_{r=1}^R G_r(p_r(x),q_r(x),u_r),\qquad M_{\rm aux}=\sum_{r=1}^R m_r.$$
--   Its domain is $[0,1]^n\times\prod_r[-1,1]^{m_r}$. Define the affine map by leaving $x$ fixed and sending each auxiliary coordinate $v_{r,j}$ to $2v_{r,j}-1$, and define
--   $$H(x,v)=G(x,2v-1).$$
--   The constant produced by this substitution is retained in $H$. No minimization or KKT correspondence is assumed by these definitions. They connect the single chain to Proposition 4.6 and Equation (19), using the actual factor maps rather than unrelated real arguments.
--
--   **Formalization Note** The coordinate type is the disjoint sum of original coordinates and dependent auxiliary pairs. When $R=0$, the auxiliary type is empty, both sums are zero, and the original coordinates remain present.
-- source:
--   Argyrios Deligkas, Michail Fasoulakis, Stavros Ioannidis, STOC 2027 submission #1093 (October 2026), https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1093.pdf, Section 4.3, Equation (16), p.9, and Section 4.4, Equation (19), p.10. Canonical PDF SHA256 f4a6f774376cfc40e24acff39a11029782994f72d85350d10b69fc17030bd0a5

import Mathlib
import Definitions.Def_UnaryQuadraticKKT_Hardness_Normalization
import Definitions.Def_UnaryQuadraticKKT_Hardness_Chain

set_option autoImplicit false

namespace UnaryQuadraticKKT.Hardness
open Finset NetworkEquilibriumCLS.LinearNash

abbrev TermIndex {n : ℕ} (p : Quadratic n) := Fin (dyadicTerms p).length

def termAt {n : ℕ} (p : Quadratic n) (r : TermIndex p) : DyadicTerm n := (dyadicTerms p)[r]

/-- Dependent pair (r,j): every gadget has its own disjoint block. -/
abbrev Auxiliary {n : ℕ} (p : Quadratic n) :=
  (r : TermIndex p) × Fin ((termAt p r).exponent + 2)

abbrev CombinedIndex {n : ℕ} (p : Quadratic n) := Fin n ⊕ Auxiliary p

def auxiliaryCount {n : ℕ} (p : Quadratic n) : ℕ :=
  ∑ r : TermIndex p, ((termAt p r).exponent + 2)

/-- Eq. (16), with the original coordinates shared between all chains. -/
noncomputable def combinedValue {n : ℕ} (p : Quadratic n) (z : CombinedIndex p → ℝ) : ℝ :=
  ∑ r : TermIndex p,
    chainValue (termAt p r).exponent (termAt p r).sign
      (factorValue (termAt p r).left (fun i => z (.inl i)))
      (factorValue (termAt p r).right (fun i => z (.inl i)))
      (fun j => z (.inr ⟨r, j⟩))

def mixedLower {n : ℕ} (p : Quadratic n) : CombinedIndex p → ℝ
  | .inl _ => 0
  | .inr _ => -1

def affinePoint {n : ℕ} (p : Quadratic n) (z : CombinedIndex p → ℝ) : CombinedIndex p → ℝ
  | .inl i => z (.inl i)
  | .inr a => 2 * z (.inr a) - 1

/-- Eq. (19)'s H, including the constant created by the substitution. -/
noncomputable def affineValue {n : ℕ} (p : Quadratic n) (z : CombinedIndex p → ℝ) : ℝ :=
  combinedValue p (affinePoint p z)

end UnaryQuadraticKKT.Hardness


