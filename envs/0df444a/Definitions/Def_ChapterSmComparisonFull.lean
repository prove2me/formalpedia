-- Prove2me | Definitions.Def_ChapterSmComparisonFull
-- name    : ChapterSmComparisonFull
-- status  : Definition
-- author  : @leonardopedro
-- created : 2026-11-04T15:11:44.891201+00:00
-- url     : https://prove2.me/theorems/6a765611-e049-418b-8916-2e8fac83baef
-- title:
--   Chapter SmComparisonFull
-- statement:
--   Formal definitions for the timepiece Lean 4 formalization (source chapter `BookProof/ChapterSmComparisonFull.lean`): generated def bundle for ChapterSmComparisonFull. See BookProof/ChapterSmComparisonFull.lean for full context.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterSmComparisonFull.lean

import Theorems.Thm_BookProof_ScalaronEsa_ccDomain_dense

import Theorems.Thm_BookProof_ScalaronEsa_smoothPotential_essentiallySelfAdjoint

import Theorems.Thm_BookProof_ScalaronEsa_smoothPotential_symmetric

import Definitions.Def_ChapterSmComparison
import Definitions.Def_ChapterScalaronCoreEsa
import Definitions.Def_ChapterSirkTrotterKato
import Definitions.Def_ChapterEsaClosureCore
import Definitions.Def_ChapterFarisLavine
import Definitions.Def_ChapterStoneBridge
import Definitions.Def_ChapterTensorSumChain
import Mathlib


/-!
# The derivative coordinates of `N₀`, and the full comparison chain of the Standard Model

`BookProof.ChapterSmComparison` proves essential self-adjointness of the *dynamical* part of
the Standard-Model comparison operator `N₀` of `CONSOLIDATED_PLAN.md` §D6b-SM.2 — the `40`
momentum-carrying coordinates, each contributing `π² + q⁴` (gluon, weak, Higgs) or `π² + q²`
(hypercharge) — and records as an honest boundary that

> the derivative-coordinate summands of `N₀` (multiplication operators with no conjugate
> momentum) are outside `sm_N_dyn_esa`, so “`N` is ESA on `C_c^∞`” is not claimed in full.

This module removes that boundary.  The point is that a derivative-coordinate summand
`Σ_j (Φ_{,j})²` is multiplication by the smooth real function `q ↦ q²`, and multiplication by
a smooth real function — with **no** growth, boundedness or semiboundedness hypothesis — is
essentially self-adjoint on the compactly supported smooth core
(`BookProof.ScalaronEsa.smoothPotential_essentiallySelfAdjoint`).  So a derivative coordinate
is an `EsaOp` in exactly the sense the tensor-sum chain consumes, and the chain can be
extended from `40` to `160` factors.

## What is proved

* `derivEsaOp` — one derivative coordinate: multiplication by `q²` on `L²(ℝ)`, essentially
  self-adjoint on the compactly supported smooth core;
* `deriv_coordinate_esa` — that statement on its own;
* `smFullChain`, **`sm_N_full_esa`** — the tensor sum of **all** `160` summands of `N₀`
  (`37` quartic + `3` quadratic dynamical factors and `120` derivative factors) is
  essentially self-adjoint on the algebraic tensor product of the `160` cores;
* `sm_N_full_stone_flow` — the unitary group it generates;
* `smFullChain_length` — the recount: `160` factors, one for each of the `163` collective
  coordinates of `BookProof.SmOneParticle.SmCoord` except the three spatial ones, which carry
  no summand of `N₀`.

As in `ChapterSmComparison`, the accounting identity of `bookGfTerm_eq_zero_of_Afield0`
(Cadabra PART F) applies: on `A₀ = 0` the BRST gauge-fixing term vanishes, so the full `N`
of record is `N₀ + c₀ I` with **no** additional gauge-fixing/ghost summand beyond the `160`
factors counted here.

## Honest boundary

As for `sm_N_dyn_esa`, the chain realizes the uncoupled sum on the tensor product of the
`160` one-dimensional spaces, which is the framework of `BookProof.ChapterTensorSumChain`;
this is a statement about `N₀`, not about the Standard-Model Hamiltonian `h`, and it does not
by itself give the Faris–Lavine hypotheses of §D6b-SM.3 for the bosonic sector (nor are they
needed there: the bosonic inner operator is a positive sum of squares, so the instrument is
Friedrichs).

Everything is `sorry`-free and `axiom`-free.
-/

namespace BookProof.SmComparisonFull

open BookProof.FarisLavine BookProof.TensorSumChain
open BookProof.SmComparison BookProof.ScalaronEsa
open BookProof.StoneBridge BookProof.ChapterStoneResolvent BookProof.EsaClosure
open MeasureTheory

noncomputable section

/-- **A derivative coordinate of `N₀`**: multiplication by `q²`, essentially self-adjoint on
the compactly supported smooth core of `L²(ℝ)`.  Unlike the dynamical factors it carries no
conjugate momentum — it is a pure multiplication operator — and its essential
self-adjointness comes from the smooth-potential theorem, not from a Schrödinger argument. -/
def derivEsaOp : EsaOp where
  space := ⟨Lp ℂ 2 (volume : Measure ℝ)⟩
  complete := inferInstanceAs (CompleteSpace (Lp ℂ 2 (volume : Measure ℝ)))
  dom := ccDomain ℝ
  op := opCc (fun x : ℝ => x ^ 2) contDiff_pow2
  dense := ccDomain_dense
  sym := smoothPotential_symmetric _ _
  esa := smoothPotential_essentiallySelfAdjoint _ _



/-- The list of factors of the full comparison chain: `36` further quartic factors (the
gluon, weak and Higgs coordinates beyond the first), the `3` quadratic hypercharge factors,
and the `120` derivative coordinates. -/
def smFullFactors : List EsaOp :=
  List.replicate 36 quarticEsaOp ++ List.replicate 3 quadraticEsaOp
    ++ List.replicate 120 derivEsaOp



/-- **The full comparison chain of `N₀`**: the `40` dynamical confining factors together with
the `120` derivative factors. -/
def smFullChain : EsaOp := chain quarticEsaOp smFullFactors





end

end BookProof.SmComparisonFull


