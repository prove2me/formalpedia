-- Prove2me | Definitions.Def_OAI_NumberTheory_ShortEgyptian_ResidueSystem
-- name    : OAI_NumberTheory_ShortEgyptian_ResidueSystem
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-15T22:57:37.070038+00:00
-- url     : https://prove2.me/theorems/32908028-02bd-4b3a-a561-5341c4d88110
-- title:
--   Residue systems: one modulus whose divisors give small residues at every level
-- statement:
--   This file defines the central combinatorial object of a residue-descent proof that fractions $a/b$ have Egyptian fraction expansions with $O(\log\log b)$ terms.
--
--   Notation, for a real scale $S$ and $C\in\mathbb{N}$: $\log$ is the natural logarithm; $\lfloor\cdot\rfloor_+$, $\lceil\cdot\rceil_+$ are floor and ceiling truncated at $0$; $D_M=204204$ and $D_X=204206$; $m=m(S)=\lfloor S/\log S\rfloor_+$; $\rho=\rho(S)=e^{-m/10000}$; $X_j=X_j(S)=\exp(D_XS-mj/10000)=e^{D_XS}\rho^j$ are the levels; $J=J(S)=\lceil (D_XS-m)/(m/10000)\rceil_+$ is the depth; $L_j=L_j(S,C)$ equals $C$ if $e^S<X_j$ and $1$ otherwise; and $\beta=\beta(S)=\lceil 100000\log S/\log 2\rceil_+$. For natural numbers $v,u$ let
--
--   $$r(v,u)=u\Big\lceil\frac vu\Big\rceil-v ,$$
--
--   which for $u>0$ is the least non-negative residue of $-v$ modulo $u$.
--
--   A *residue system* for $(S,C)$ consists of
--
--   - a natural number $M$ with $e^S<M\le e^{D_MS}$ and $2^{\beta}\mid M$;
--   - for every level $j\in\mathbb{N}$, a family $\big(t_j(i)\big)_{i\in\{0,1\}^m}$ of positive divisors of $M$, indexed by the Boolean vectors of length $m$;
--   - for every $j\in\mathbb{N}$, a finite set $\mathrm{Bad}_j\subseteq\mathbb{N}$,
--
--   subject to the following three conditions.
--
--   1. **Few exceptions.** For every $j<J$, $|\mathrm{Bad}_j|\le X_j\,e^{-m/1000}$.
--   2. **Many good divisors.** For every $j<J$ and every integer $u$ with $\lfloor \rho X_j\rfloor_+<u\le\lfloor X_j\rfloor_+$ and $u\notin\mathrm{Bad}_j$,
--
--      $$\#\{\,i\in\{0,1\}^m:\ r\big(L_j\,t_j(i),\,u\big)\le X_{j+1}\,\}\ \ge\ \frac{\rho\,2^m}{2}.$$
--
--   3. **Terminal divisors.** For every natural number $u$ with $S^{100000}<u\le e^{m}$ there is a positive divisor $t$ of $M$ with $r(t,u)\le u^{9999/10000}$.
--
--   By the identity $\frac{u}{ML_j}=\frac{1}{(M/t)z}+\frac{h}{ML_jz}$ with $z=\lceil L_jt/u\rceil$ and $h=r(L_jt,u)$, a good divisor $t=t_j(i)$ trades the numerator $u\in(X_{j+1},X_j]$ for one unit fraction and a numerator $h\le X_{j+1}$ one level lower; condition 1 says that only few numerators lack such divisors, and condition 3, together with $2^\beta\mid M$, handles the final stage below $e^m$. Residue systems exist for all sufficiently large $S$ and all $C$ with $e^{D_CS}\le C\le e^{2D_CS}$, where $D_C=4D_X$; they are built from products of primes of size about $S^{100}$.
--
--   **Formalization Note** `ResidueSystem S C` is a structure carrying data (fields `M`, `t`, `bad`) together with the properties above (`M_lower`, `M_upper`, `binary_dvd`, `t_pos`, `t_dvd`, `bad_card`, `good_residues`, `terminal`). The family `t` is defined for every level $j$, with index type `Fin (scaleM S) → Bool`; the window in condition 2 is `scaleInterval (level S j) (scaleRho S)`, and $r(v,u)$ is `residue v u (quotient v u)` with truncated natural subtraction. All inequalities between sizes are stated after casting to the reals, and $u^{9999/10000}$ is a real power.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/NumberTheory/ShortEgyptian/ResidueSystem.lean

-- Generated from openai/math@1581d4c lean/OAI/NumberTheory/ShortEgyptian/ResidueSystem.lean by skeleton subtraction
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
import Definitions.Def_OAI_NumberTheory_ShortEgyptian_EmpiricalDiscrepancy
import Definitions.Def_OAI_NumberTheory_ShortEgyptian_DivisorWeights
import Definitions.Def_OAI_NumberTheory_ShortEgyptian_TruncatedDivisors
import Definitions.Def_OAI_NumberTheory_ShortEgyptian_SmoothBounds
import Definitions.Def_OAI_NumberTheory_ShortEgyptian_DivisorMoments
import Definitions.Def_OAI_NumberTheory_ShortEgyptian_PrimeLists
import Definitions.Def_OAI_NumberTheory_ShortEgyptian_PrimeProducts
import Definitions.Def_OAI_NumberTheory_ShortEgyptian_HammingDistance
import Definitions.Def_OAI_NumberTheory_ShortEgyptian_SamplePartitions
import Definitions.Def_OAI_NumberTheory_ShortEgyptian_ProductCorrelations
import Definitions.Def_OAI_NumberTheory_ShortEgyptian_ListSelection
import Definitions.Def_OAI_NumberTheory_ShortEgyptian_LevelSelection
import Definitions.Def_OAI_NumberTheory_ShortEgyptian_ListConstruction
import Definitions.Def_OAI_NumberTheory_ShortEgyptian_ScaleGeometry
import Definitions.Def_OAI_NumberTheory_ShortEgyptian_ScaleBounds

-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

universe uA

namespace ShortEgyptian

attribute [local instance] scaleFinDecidableEq

open scoped BigOperators
open Finset Classical

structure ResidueSystem (S : ℝ) (C : ℕ) where
  M : ℕ
  M_lower : Real.exp S < (M:ℝ)
  M_upper : (M:ℝ) ≤ Real.exp ((dimM:ℝ)*S)
  binary_dvd : 2^binaryExponent S ∣ M
  t : ℕ → (Fin (scaleM S) → Bool) → ℕ
  t_pos : ∀ j i, 0 < t j i
  t_dvd : ∀ j i, t j i ∣ M
  bad : ℕ → Finset ℕ
  bad_card : ∀ j, j < depth S → (bad j).card ≤ level S j*Real.exp (-(1/1000:ℝ)*scaleM S)
  good_residues : ∀ j, j < depth S → ∀ u ∈ scaleInterval (level S j) (scaleRho S), u ∉ bad j →
    scaleRho S*Fintype.card (Fin (scaleM S) → Bool)/2 ≤
      ((univ.filter fun i => (residue (levelMultiplier S C j*t j i) u
        (quotient (levelMultiplier S C j*t j i) u):ℝ) ≤ level S (j+1)).card:ℝ)
  terminal : ∀ u : ℕ, S^100000 < (u:ℝ) → (u:ℝ) ≤ Real.exp (scaleM S:ℝ) →
    ∃ t : ℕ, 0 < t ∧ t ∣ M ∧
      (residue t u (quotient t u):ℝ) ≤ (u:ℝ)^((9999/10000:ℝ))

end ShortEgyptian

end OAI


