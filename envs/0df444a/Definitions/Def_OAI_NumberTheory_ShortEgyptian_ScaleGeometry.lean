-- Prove2me | Definitions.Def_OAI_NumberTheory_ShortEgyptian_ScaleGeometry
-- name    : OAI_NumberTheory_ShortEgyptian_ScaleGeometry
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-15T22:52:26.744514+00:00
-- url     : https://prove2.me/theorems/09aac45f-ab3b-4041-b826-7bdb398a80ae
-- title:
--   Dimension constants and the geometric ladder of levels at scale $S$
-- statement:
--   This file fixes the numerical constants and the scale-dependent parameters of a multiplicative descent used to prove that every fraction $a/b$ with $1\le a<b$ has an Egyptian fraction expansion with $O(\log\log b)$ terms; the scale parameter is a real number $S$ (in the application $b=e^S$). Throughout, $\log$ is the natural logarithm and $\lfloor\cdot\rfloor_+$, $\lceil\cdot\rceil_+$ denote floor and ceiling truncated at $0$.
--
--   1. **Dimension constants.**
--
--      $$D_M=(2\cdot1000+2)(100+2)=204204,\qquad D_X=D_M+2=204206,\qquad D_C=4D_X=816824 .$$
--
--   2. **Block length.** $m(S)=\lfloor S/\log S\rfloor_+$.
--
--   3. **Ratio.** $\rho(S)=\exp\big(-m(S)/10000\big)$.
--
--   4. **Levels.** For $j\in\mathbb{N}$,
--
--      $$X_j(S)=\exp\Big(D_XS-\frac{m(S)\,j}{10000}\Big)=e^{D_XS}\rho(S)^j .$$
--
--   5. **Depth.**
--
--      $$J(S)=\Big\lceil\frac{D_XS-m(S)}{m(S)/10000}\Big\rceil_+ ,$$
--
--      so that, when $m(S)>0$, one has $j<J(S)$ exactly when $X_j(S)>e^{m(S)}$.
--
--   6. **Level multiplier.** For $C,j\in\mathbb{N}$, $L_j(S,C)=C$ if $e^S<X_j(S)$, and $L_j(S,C)=1$ otherwise.
--
--   7. **Binary exponent.** $\beta(S)=\lceil 100000\log S/\log 2\rceil_+$, so that $2^{\beta(S)}\ge S^{100000}$ for $S>0$.
--
--   The descent starts with numerators up to $X_0(S)=e^{D_XS}$ and, level by level, replaces a numerator of size at most $X_j$ by one of size at most $X_{j+1}=\rho X_j$, until the level falls to $e^{m(S)}$ after $J(S)=O(\log S)$ steps. The constant $D_M$ bounds the common modulus ($M\le e^{D_MS}$), $D_C$ fixes the window $[e^{D_CS},e^{2D_CS}]$ for the denominator $C$ produced by greedy preparation, and the multiplier $L_j$ keeps the factor $C$ in the denominator only at the high levels $X_j>e^S$. The power $2^{\beta(S)}$ divides the modulus and handles the smallest numerators by binary expansion.
--
--   **Formalization Note** The Lean names are `dimM`, `dimX`, `dimC` (irreducible natural-number constants), `scaleM`, `scaleRho`, `level`, `depth`, `levelMultiplier` and `binaryExponent`; $\log$ is `Real.log` and the truncated floor and ceiling are `Nat.floor` and `Nat.ceil`. Since division by zero gives $0$ in Lean, `depth S = 0` whenever $m(S)=0$; these degenerate values play no role for the large $S$ used in the proof.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/NumberTheory/ShortEgyptian/ScaleGeometry.lean

-- Generated from openai/math@1581d4c lean/OAI/NumberTheory/ShortEgyptian/ScaleGeometry.lean by skeleton subtraction
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

-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

namespace ShortEgyptian

open scoped BigOperators
open Finset Classical Filter Topology

@[irreducible] def dimM : ℕ := (2*1000+2)*(100+2)
@[irreducible] def dimX : ℕ := dimM+2
@[irreducible] def dimC : ℕ := 4*dimX
noncomputable def scaleM (S : ℝ) : ℕ := ⌊S/Real.log S⌋₊
noncomputable def scaleRho (S : ℝ) : ℝ := Real.exp (-(1/10000:ℝ)*scaleM S)
noncomputable def level (S : ℝ) (j : ℕ) : ℝ :=
  Real.exp ((dimX:ℝ)*S-(1/10000:ℝ)*scaleM S*j)
noncomputable def depth (S : ℝ) : ℕ :=
  ⌈((dimX:ℝ)*S-scaleM S)/((1/10000:ℝ)*scaleM S)⌉₊
noncomputable def levelMultiplier (S : ℝ) (C j : ℕ) : ℕ :=
  if Real.exp S < level S j then C else 1
noncomputable def binaryExponent (S : ℝ) : ℕ := ⌈100000*Real.log S/Real.log 2⌉₊

end ShortEgyptian

end OAI


