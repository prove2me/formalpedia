-- Prove2me | Definitions.Def_DerivativeChainPrivate_dyadic_kernel
-- name    : DerivativeChainPrivate_dyadic_kernel
-- status  : Definition
-- author  : @labuka
-- created : 2026-10-18T10:45:51.748765+00:00
-- url     : https://prove2.me/theorems/32bd6029-0332-4a72-a938-9dbbd4465f58
-- title:
--   Paired natural-number arithmetic for dyadic critical-root certificates
-- statement:
--   Pure paired reciprocal-sum arithmetic and Boolean endpoint-sign checks. The soundness and full polynomial theorem are separate obligations. No global derivative-chain bound is asserted by these definitions.
-- source:
--   https://github.com/Amal-David/derivative-chain-prize/blob/a308e02e7640561ffded6c668be6865bf5418a7c/dyadic_formal/Source/KernelCheck.lean

import Mathlib.Data.Nat.Basic
set_option autoImplicit false
namespace DerivativeChainPrivate.DyadicKernel

def pairedSums (numerator square : ℕ) (parentSquares : List ℕ) : ℕ × ℕ :=
  parentSquares.foldl (fun p r =>
    if r < square then (p.1+numerator/(square-r),p.2)
    else (p.1,p.2+numerator/(r-square))) (0,0)

def endpoint (degree w : ℕ) (parentSquares : List ℕ) (positive : Bool) : Bool :=
  let p := pairedSums (2^85*w) (w*w) parentSquares
  let pos := p.1 + if degree % 2 = 1 then 2^84/w else 0
  if positive then decide (p.2+degree < pos) else decide (pos+degree < p.2)

def signs (degree : ℕ) (parentSquares : List ℕ) (points : List (ℕ × Bool)) : Bool :=
  points.all (fun p => endpoint degree p.1 parentSquares p.2)

end DerivativeChainPrivate.DyadicKernel


