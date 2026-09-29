-- Prove2me | Definitions.Def_mme_CW_2376_profile_address
-- name    : mme_CW_2376_profile_address
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-08-24T17:02:01.770962+00:00
-- url     : https://prove2.me/theorems/7e2f83ae-cfef-4acb-98b4-373e71790cd7
-- title:
--   Exact joint-profile addresses for the CW 2.376 extraction
-- statement:
--   At scale $m$, an exact Coppersmith--Winograd profile address is a triple of five-grade words of common length $3{,}000{,}000m$. At each coordinate the three grades form one joint type. The fifteen supported joint types are divided into four cyclic orbits with respective multiplicities
--
--   $$
--   699m,\qquad 37{,}518m,\qquad 307{,}638m,\qquad 616{,}627m.
--   $$
--
--   These totals satisfy
--
--   $$
--   3(699m)+6(37{,}518m)+3(307{,}638m)+3(616{,}627m)=3{,}000{,}000m.
--   $$
--
--   The definition also records when a finite family of exact-profile addresses is mode-disjoint: two distinct addresses must have different grade words in each of the three modes. This is the precise combinatorial interface between the Salem--Spencer pruning step and the tensor direct-sum assembly.
-- source:
--   D. Coppersmith and S. Winograd, Matrix Multiplication via Arithmetic Progressions, Journal of Symbolic Computation 9 (1990), tensor-square types (11), optimized joint counts (13), and numerical profile on journal pp. 265--269; https://www.sciencedirect.com/science/article/pii/S0747717108800132

import Mathlib.Data.Fin.VecNotation
import Definitions.Def_mme_CW_2376_profile_data
import Definitions.Def_mme_CW_square_five_grade_certificate

namespace MME

def cw2376ProfileLength (m : ℕ) : ℕ := 3000000 * m

def CW2376ProfileAddress (m : ℕ) : Type :=
  Fin 3 → Fin (cw2376ProfileLength m) → Fin 5

def cw2376AddressType {m : ℕ} (a : CW2376ProfileAddress m)
    (j : Fin (cw2376ProfileLength m)) : Fin 3 → Fin 5 :=
  fun i => a i j

def cw2376ScalarTypes : Finset (Fin 3 → Fin 5) :=
  {cwSquareBlockType 0 0 4,
    cwSquareBlockType 0 4 0,
    cwSquareBlockType 4 0 0}

def cw2376RectTypes : Finset (Fin 3 → Fin 5) :=
  {cwSquareBlockType 0 1 3,
    cwSquareBlockType 0 3 1,
    cwSquareBlockType 1 0 3,
    cwSquareBlockType 3 0 1,
    cwSquareBlockType 1 3 0,
    cwSquareBlockType 3 1 0}

def cw2376CentralTypes : Finset (Fin 3 → Fin 5) :=
  {cwSquareBlockType 0 2 2,
    cwSquareBlockType 2 0 2,
    cwSquareBlockType 2 2 0}

def cw2376CoupledTypes : Finset (Fin 3 → Fin 5) :=
  {cwSquareBlockType 1 1 2,
    cwSquareBlockType 2 1 1,
    cwSquareBlockType 1 2 1}

def cw2376ProfileMultiplicity (m : ℕ) (σ : Fin 3 → Fin 5) : ℕ :=
  if σ ∈ cw2376ScalarTypes then 699 * m
  else if σ ∈ cw2376RectTypes then 37518 * m
  else if σ ∈ cw2376CentralTypes then 307638 * m
  else if σ ∈ cw2376CoupledTypes then 616627 * m
  else 0

def CW2376ExactProfileAddress (m : ℕ) : Type :=
  {a : CW2376ProfileAddress m //
    ∀ σ : Fin 3 → Fin 5,
      (Finset.univ.filter
        (fun j => cw2376AddressType a j = σ)).card =
      cw2376ProfileMultiplicity m σ}

def CW2376ModeDisjoint {m : ℕ}
    (F : Finset (CW2376ExactProfileAddress m)) : Prop :=
  ∀ x : F, ∀ y : F, x ≠ y →
    ∀ i : Fin 3, x.1.1 i ≠ y.1.1 i

end MME


