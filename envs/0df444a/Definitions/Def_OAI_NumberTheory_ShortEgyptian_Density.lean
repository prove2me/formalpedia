-- Prove2me | Definitions.Def_OAI_NumberTheory_ShortEgyptian_Density
-- name    : OAI_NumberTheory_ShortEgyptian_Density
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-15T23:07:29.336368+00:00
-- url     : https://prove2.me/theorems/d524e53a-0a71-49a7-8f96-2d4378ed7348
-- title:
--   Dense sets of numerators with short unit-fraction representations over a modulus
-- statement:
--   Notation: $\log$ is the natural logarithm, $\lfloor\cdot\rfloor_+$ is the floor truncated at $0$, $D_M=204204$ and $D_X=204206$. A *unit-fraction representation* of a rational number $x$ is a finite list of natural numbers $n_1,\dots,n_r$, each at least $2$ (repetitions allowed), with $\sum_i 1/n_i=x$; its length is $r$.
--
--   1. **Density constant.**
--
--      $$c_{\mathrm{dens}}=c_{\mathrm{term}}+3\cdot D_X\cdot 10000,\qquad c_{\mathrm{term}}=\frac{100000}{\log 2}+\frac{1}{\log(10000/9999)}+3 .$$
--
--   2. **Dense data.** Let $S\in\mathbb{R}$ and $C\in\mathbb{N}$, and put $U=\{1,2,\dots,\lfloor e^{D_XS}\rfloor_+\}$. A *dense datum* for $(S,C)$ consists of a natural number $M$ and a finite set $G\subseteq\mathbb{N}$ such that
--      - $e^{S}<M\le e^{D_MS}$;
--      - $G\subseteq U$;
--      - $|U\setminus G|\le e^{D_XS}/8$;
--      - for every $u\in G$, the fraction $u/(MC)$ has a unit-fraction representation of length at most $c_{\mathrm{dens}}\log S$.
--
--   A dense datum says that all but at most an eighth of the numerators up to $e^{D_XS}$ are good over the common denominator $MC$. This is enough to treat every remainder $A/C$ with $0<A\le e^S$: a suitable multiple $gAM$ lies in $[e^{D_XS}/2,e^{D_XS}]$ and, the bad set being small, is a sum of two elements of $G$, which gives a unit-fraction representation of $A/C$ of length at most $2c_{\mathrm{dens}}\log S$. Dense data exist for all sufficiently large $S$ and all $C$ with $e^{D_CS}\le C\le e^{2D_CS}$, where $D_C=4D_X$; the constant $c_{\mathrm{dens}}$ accounts for the terminal length plus one unit fraction per level of the descent.
--
--   **Formalization Note** The constant is `densityConstant`, and `DenseData S C` is a structure carrying data (fields `M` and `G`, the latter a `Finset`) together with the properties `M_lower`, `M_upper`, `G_subset`, `bad_card` and `expansion`. Representations are expressed with `IsUnitSum`, the fraction $u/(MC)$ is computed in $\mathbb{Q}$ (so it is $0$ if $MC=0$), and the length bound is an inequality between real numbers.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/NumberTheory/ShortEgyptian/Density.lean

-- Generated from openai/math@1581d4c lean/OAI/NumberTheory/ShortEgyptian/Density.lean by skeleton subtraction
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
import Definitions.Def_OAI_NumberTheory_ShortEgyptian_ResidueSystem
import Definitions.Def_OAI_NumberTheory_ShortEgyptian_TerminalScale
import Definitions.Def_OAI_NumberTheory_ShortEgyptian_DescentSets
import Definitions.Def_OAI_NumberTheory_ShortEgyptian_MomentRecurrence

-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

namespace ShortEgyptian

attribute [local instance] scaleFinDecidableEq

open scoped BigOperators
open Finset Classical Filter Topology

noncomputable def densityConstant : ℝ := terminalConstant+3*(dimX:ℝ)*10000

structure DenseData (S : ℝ) (C : ℕ) where
  M : ℕ
  G : Finset ℕ
  M_lower : Real.exp S < (M:ℝ)
  M_upper : (M:ℝ) ≤ Real.exp ((dimM:ℝ)*S)
  G_subset : G ⊆ Icc 1 ⌊Real.exp ((dimX:ℝ)*S)⌋₊
  bad_card : ((Icc 1 ⌊Real.exp ((dimX:ℝ)*S)⌋₊ \ G).card:ℝ) ≤ Real.exp ((dimX:ℝ)*S)/8
  expansion : ∀ u ∈ G, ∃ ns, IsUnitSum ((u:ℚ)/(M*C)) ns ∧ (ns.length:ℝ) ≤ densityConstant*Real.log S

end ShortEgyptian

end OAI


