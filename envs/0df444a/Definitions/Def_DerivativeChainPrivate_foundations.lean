-- Prove2me | Definitions.Def_DerivativeChainPrivate_foundations
-- name    : DerivativeChainPrivate_foundations
-- status  : Definition
-- author  : @labuka
-- created : 2026-10-17T18:37:01.841566+00:00
-- url     : https://prove2.me/theorems/68b95d66-17eb-4790-99fc-9c955976c17a
-- title:
--   Multiplicity-aware derivative-chain foundations
-- statement:
--   A root list forms the monic product polynomial; row m is its derivative of order n-m. A complete chain chooses an actual root of every degree-one through degree-n row and sums adjacent Euclidean distances. RealCoefficients and nonrealCount retain the original private mission conventions and count multiplicities. Target statements use positive n and rows 1 through n. These definitions assert no bound.
-- source:
--   Derivative-zero chains: public formalization reference, R01, DerivativeChainPrivate_foundations. https://gist.github.com/Amal-David/d6612109c98595b12561cd638c60edf5/3883c57ddc7bf9d4c0e898c3d6bfd2ca0d7f9c95#file-notes-md

import Mathlib
open scoped BigOperators
set_option autoImplicit false
namespace DerivativeChainPrivate

noncomputable def fromRoots {n : ℕ} (a : Fin n → ℂ) : Polynomial ℂ :=
  ∏ i, (Polynomial.X - Polynomial.C (a i))

noncomputable def row {n : ℕ} (a : Fin n → ℂ) (m : ℕ) : Polynomial ℂ :=
  (Polynomial.derivative^[n - m]) (fromRoots a)

noncomputable def IsChain {n : ℕ} (a z : Fin n → ℂ) : Prop :=
  ∀ i, (row a (i.val + 1)).eval (z i) = 0

noncomputable def chainCost {n : ℕ} (z : Fin n → ℂ) : ℝ :=
  ∑ i : Fin (n - 1),
    ‖z ⟨i.val + 1, by omega⟩ - z ⟨i.val, by omega⟩‖

noncomputable def RealCoefficients {n : ℕ} (a : Fin n → ℂ) : Prop :=
  ∀ k : ℕ, ((fromRoots a).coeff k).im = 0

noncomputable def nonrealCount {n : ℕ} (a : Fin n → ℂ) : ℕ := by
  classical
  exact (Finset.univ.filter (fun i => (a i).im ≠ 0)).card


end DerivativeChainPrivate


