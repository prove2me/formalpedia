-- Prove2me | Definitions.Def_MIPRE_Foundations_Linearity
-- name    : MIPRE_Foundations_Linearity
-- status  : Definition
-- author  : @thomasvidick
-- created : 2026-10-17T01:41:13.76999+00:00
-- url     : https://prove2.me/theorems/c61c4105-735c-46ca-b1a7-75b4256e20f3
-- title:
--   Definitions of Linearity: Approximate linearity gives exact linearity Blueprint `thm:linearity`, the quantum linearity test
-- statement:
--   The definitions of the module `MIPRE.Foundations.Linearity` of the MIP\* = RE formalization (commit `70cbf1c` of vidick/MIPRE-formalization). Approximate linearity gives exact linearity. Blueprint `thm:linearity`, the quantum linearity test. A family of observables `{O^u}_{u in F_q^n}` that is *approximately* linear --- `O^u O^{u'}` close to `O^{u + u'}` on average, in the state-dependent distance --- is close on average to a family that is *exactly* linear, after adjoining an ancilla register to one player. The paper imports this from Natarajan--Vidick; it is proved here. The route is the one the blueprint's proof text names, and every step of it is already in this repository: * **Parseval.** The Fourier transform `A_e = |V|^{-1}…
--
--   **Definitions** (2): `MIPRE.extVecA` (**The one-sided extension of a state**: an ancilla register in the fixed state `|a₀⟩`, adjoined to the **first** party only.); `MIPRE.fourierOf` (**The Fourier transform** of a family of operators indexed by `V = F_q^n`, against the characters of the trace form.).
--
--   **Formalization Note** The bundle is the module `MIPRE.Foundations.Linearity` (`MIPRE/Foundations/Linearity.lean`) with every declaration not listed removed, imports rewritten to the bundles of the module's import closure; the declarations keep their names, statements and bodies; the source module is split over 16 imported bundle(s).
-- source:
--   https://github.com/vidick/MIPRE-formalization/blob/70cbf1c52e3d5e1dff1162fdf952c9a9f4bd99ed/MIPRE/Foundations/Linearity.lean; blueprint thm:linearity

/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Foundations/Linearity.lean (definition bundle: declarations the uploaded statements rest on);
   produced mechanically by prove2me/tools/gen.py, never edited by hand. -/
import Mathlib.Algebra.MvPolynomial.CommRing
import Mathlib.Algebra.MvPolynomial.Degrees
import Mathlib.Algebra.MvPolynomial.SchwartzZippel
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Analysis.CStarAlgebra.CStarMatrix
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.Analysis.SpecialFunctions.Complex.Circle
import Mathlib.Data.ENat.Lattice
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Data.Real.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.FieldTheory.Finite.GaloisField
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.RingTheory.Trace.Basic
import Mathlib.Tactic.IntervalCases
import Definitions.Def_MIPRE_Foundations_Games
import Definitions.Def_MIPRE_Foundations_Distances
import Definitions.Def_MIPRE_Foundations_LowDegree_Encoding
import Definitions.Def_MIPRE_Foundations_Closeness
import Definitions.Def_MIPRE_Foundations_OpBound
import Definitions.Def_MIPRE_Foundations_OpBound_B
import Definitions.Def_MIPRE_Foundations_StateDistance
import Definitions.Def_MIPRE_Foundations_StateDistance_B
import Definitions.Def_MIPRE_Foundations_Sign
import Definitions.Def_MIPRE_Foundations_PVM
import Definitions.Def_MIPRE_Foundations_PVM_B
import Definitions.Def_MIPRE_Foundations_Dilation
import Definitions.Def_MIPRE_Foundations_LowDegree_SchwartzZippel
import Definitions.Def_MIPRE_Foundations_LowDegree_Anticomm
import Definitions.Def_MIPRE_Foundations_Weyl
import Definitions.Def_MIPRE_Foundations_Parseval
import Theorems.Thm_MIPRE_aOp_sum
import Theorems.Thm_MIPRE_ancillaEmbed_isometry

/-!
# Approximate linearity gives exact linearity

Blueprint `thm:linearity`, the quantum linearity test. A family of observables
`{O^u}_{u in F_q^n}` that is *approximately* linear --- `O^u O^{u'}` close to `O^{u + u'}` on
average, in the state-dependent distance --- is close on average to a family that is *exactly*
linear, after adjoining an ancilla register to one player.

The paper imports this from Natarajan--Vidick; it is proved here. The route is the one the
blueprint's proof text names, and every step of it is already in this repository:

* **Parseval.** The Fourier transform `A_e = |V|^{-1} sum_a (-1)^{<a,e>} O^a` of the family
  against the characters of the trace form has `sum_e A_e^2 = |V|^{-1} sum_a (O^a)^2 = Id`
  whenever each `O^a` is an involution. So `{A_e^2}` is a POVM --- **exactly**, with no
  appeal to the approximate linearity, which is the one surprise of the argument.
* **Naimark.** `exists_projective_dilation` dilates that POVM to a projective measurement
  `{P_e}` on `d x V`, compressed back by the isometry that pads with the ancilla state `|0>`.
* **Inversion.** `L^u = sum_e (-1)^{<u,e>} P_e` is then exactly linear --- `L^u L^{u'} =
  L^{u+u'}` and `L^0 = Id` --- because the `P_e` are mutually orthogonal projections, and its
  compression is `sum_e (-1)^{<u,e>} A_e^2`, which the same character sum identifies with
  `|V|^{-1} sum_a O^a O^{a+u}`.
* **The estimate.** That average is where the hypothesis enters, and it enters once:
  `|V|^{-2} sum_{a,b} <psi| O^a O^b O^{a+b} |psi>` is the hypothesis written out, so the
  closeness of `L^u` to `O^u` on the extended state carries the *same* `delta`, with no square
  root and no loss in the exponent.

The one thing to watch is which distance the hypothesis is in. It is the state-dependent one of
`def:state-distance` --- not the Hilbert--Schmidt distance of `thm:gowers-hatami` --- so this is
not Gowers--Hatami with a different normalization; the exact-POVM step above replaces the
approximate-representation machinery entirely.
-/

noncomputable section

namespace MIPRE

open Finset Matrix MIPRE.Weyl
open scoped Kronecker ComplexOrder MatrixOrder

set_option linter.unusedSectionVars false

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] [Algebra (ZMod 2) F]
variable {n : Type*} [Fintype n] [DecidableEq n]
variable {d : Type*} [Fintype d] [DecidableEq d]

/-! ## The Fourier transform of a family of operators -/

/-- **The Fourier transform** of a family of operators indexed by `V = F_q^n`, against the
characters of the trace form. This is `MIPRE.Weyl.proj` with the index group decoupled from the
space the operators act on, and with no group law assumed. -/
def fourierOf (O : (n → F) → Matrix d d ℂ) (e : n → F) : Matrix d d ℂ :=
  (Fintype.card (n → F) : ℂ)⁻¹ • ∑ a : n → F, sgn (trDot a e) • O a

/-! ## The exactly linear family -/

/-! ## Adjoining an ancilla to one party -/

variable {dA dB : Type*} [Fintype dA] [DecidableEq dA] [Fintype dB] [DecidableEq dB]

/-- **The one-sided extension of a state**: an ancilla register in the fixed state `|a₀⟩`,
adjoined to the **first** party only. `expVec` splits an ancilla *pair* between the two parties;
this is the asymmetric extension `thm:linearity` needs, the exactly linear observables living on
the first party's enlarged space and the second party untouched. -/
def extVecA {A : Type*} [Fintype A] [DecidableEq A] (ψ : dA × dB → ℂ) (a₀ : A) :
    (dA × A) × dB → ℂ :=
  ((ancillaEmbed dA a₀) ⊗ₖ (1 : Matrix dB dB ℂ)) *ᵥ ψ

section Ext

variable {A : Type*} [Fintype A] [DecidableEq A]

end Ext

/-! ## The distance between two unitaries, as a quadratic form -/

/-! ## The theorem -/

section Main

variable {X : Type*} [Fintype X]

end Main

end MIPRE

end


