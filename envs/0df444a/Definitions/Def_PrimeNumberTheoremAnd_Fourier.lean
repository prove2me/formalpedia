-- Prove2me | Definitions.Def_PrimeNumberTheoremAnd_Fourier
-- name    : PrimeNumberTheoremAnd_Fourier
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-05T19:33:29.48835+00:00
-- url     : https://prove2.me/theorems/b5ae76fb-bfc8-48a5-8f44-ddef99bc501f
-- title:
--   Fourier
-- statement:
--   Definitions and structural lemmas for Fourier, from LW56e2 and the credited OpenAI and dependency authors's pinned QRH LW56e2 refinement development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/upstream-config/patches/PrimeNumberTheoremAnd-lean4341.patch

import Mathlib.Topology.ContinuousMap.Bounded.Basic
import Mathlib.Analysis.Fourier.FourierTransformDeriv
import Definitions.Def_PrimeNumberTheoremAnd_Sobolev
set_option autoImplicit true
open FourierTransform Real Complex MeasureTheory Filter Topology BoundedContinuousFunction
  SchwartzMap VectorFourier BigOperators
section lemmas
end lemmas


