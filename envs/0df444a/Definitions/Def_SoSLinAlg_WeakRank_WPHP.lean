-- Prove2me | Definitions.Def_SoSLinAlg_WeakRank_WPHP
-- name    : SoSLinAlg_WeakRank_WPHP
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-10T22:29:52.982279+00:00
-- url     : https://prove2.me/theorems/d27008fb-a75c-455a-b31f-065b1add4af2
-- title:
--   Tight Frame and Weak Pigeonhole polynomial systems
-- statement:
--   Let $X$ be a single $n\times r$ matrix of real indeterminates. The Tight Frame system is the family
--   $$\operatorname{TFrame}_r^n:\quad \sum_{j=1}^r X_{ij}X_{kj}-\delta_{ik}=0\quad (1\le i,k\le n).$$
--   The Weak Pigeonhole system is the union of three indexed families:
--   $$\operatorname{WPHP}_r^n:\quad X_{ij}^2-X_{ij}=0,\quad X_{ij}X_{kj}=0\ (i<k),\quad \sum_{j=1}^r X_{ij}-1=0.$$
--   Here Boolean equations range over all entries, collision equations over $1\le j\le r$ and $1\le i<k\le n$, and row equations over $1\le i\le n$. The symbol $\delta_{ik}$ is one if $i=k$ and zero otherwise.
--
--   These systems share the one-matrix polynomial ring, distinct from the two-matrix ring of WRank. The definition uses tagged indices for the three WPHP families and retains the strict order on collision pairs. Positivity conditions $n>r\ge1$ are imposed by Proposition 1.10, not built into the equation families.
-- source:
--   Dmitriy Kunisky, Xifan Yu, The sum-of-squares complexity of linear-algebraic principles, STOC 2027 submission #1181 (October 2026), https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1181.pdf, Definitions 1.5 and 1.8, PDF p.5 (printed p.3)

import Mathlib

noncomputable section

namespace SoSLinAlg.WeakRank

/-- One matrix of variables for Definitions 1.5 and 1.8, PDF p.5. -/
abbrev SingleVar (n r : ℕ) := Fin n × Fin r
abbrev SinglePoly (n r : ℕ) := MvPolynomial (SingleVar n r) ℝ

def singleX {n r : ℕ} (i : Fin n) (j : Fin r) : SinglePoly n r :=
  MvPolynomial.X (i, j)

/-- Definition 1.5: XXᵀ - I = 0. -/
def TFrame (n r : ℕ) : (Fin n × Fin n) → SinglePoly n r :=
  fun ik => (∑ j : Fin r, singleX ik.1 j * singleX ik.2 j) -
    MvPolynomial.C ((1 : Matrix (Fin n) (Fin n) ℝ) ik.1 ik.2)

/-- The Boolean, collision, and row-sum equations of Definition 1.8.
Collision indices retain the source's strict i < k. -/
abbrev WPHPIndex (n r : ℕ) :=
  (Fin n × Fin r) ⊕ ((Fin r × {ik : Fin n × Fin n // ik.1 < ik.2}) ⊕ Fin n)

/-- Definition 1.8, PDF p.5 (printed p.3). -/
def WPHP (n r : ℕ) : WPHPIndex n r → SinglePoly n r
  | Sum.inl ij => singleX ij.1 ij.2 ^ 2 - singleX ij.1 ij.2
  | Sum.inr (Sum.inl ji) => singleX ji.2.val.1 ji.1 * singleX ji.2.val.2 ji.1
  | Sum.inr (Sum.inr i) => (∑ j : Fin r, singleX i j) - 1

end SoSLinAlg.WeakRank
end


