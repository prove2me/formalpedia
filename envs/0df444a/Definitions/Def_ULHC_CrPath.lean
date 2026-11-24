-- Prove2me | Definitions.Def_ULHC_CrPath
-- name    : ULHC_CrPath
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-24T02:53:28.913442+00:00
-- url     : https://prove2.me/theorems/0d7535c6-8f9d-4dac-9b18-d101e1b9aabe
-- title:
--   Cr Path
-- statement:
--   Definitions and structural lemmas for Cr Path, from zzyzek/SolidGridGraphHamiltonianCycle2D-Lean contributors (see pinned CC0-1.0 LICENSE and source headers)'s pinned Umans-Lenhart Hamiltonian-cycle algorithm for solid grid graphs development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/zzyzek/SolidGridGraphHamiltonianCycle2D-Lean/blob/ff168b1a209d760cb25b5b85c7f7059ee34bff97/ULHC/CrPath.lean

import Definitions.Def_ULHC_Cr2
import Theorems.Thm_ULHC_APair_flip

set_option autoImplicit true
namespace ULHC
open Finset Classical
def SideOff (b c : StripSpec) : Prop :=
  ∀ j < c.n, ∀ i, i + 1 < b.n → ∀ e ∈ cellE (cellJ c.c c.s j), e ∉ cellE (cellJ b.c b.s i)
def CR2 (V : Finset Pt) (G : Finset Edge) (b c : StripSpec) : Prop :=
  2 ≤ b.n ∧ b.n % 2 = 0 ∧ 1 ≤ c.n ∧ StripPat (flip G (endCell b)) c.c c.s c.n ∧
    (∀ j < c.n, IsCell V (cellJ c.c c.s j)) ∧ SideOff b c ∧
    (∀ j < c.n, cellJ c.c c.s j ≠ endCell b) ∧
    (c.n % 2 = 0 → ∀ e ∈ cellE (endCell c), e ∉ cellE (endCell b)) ∧
    ¬ IsMid b.c b.s (b.n - 2) (back1 c.c c.s) ∧ ¬ IsMid b.c b.s (b.n - 2) (front1 c.c c.s) ∧
    Conn G (back1 c.c c.s) (front1 c.c c.s) ∧
    ¬ Conn (flip G (endCell b)) (back1 c.c c.s) (front1 c.c c.s)
def CRChain (V : Finset Pt) (G : Finset Edge) : StripSpec → List StripSpec → Prop
  | σ, [] => σ.n % 2 = 1
  | σ, τ :: L => σ.n % 2 = 0 ∧ CR2 V G σ τ ∧ CRChain V G τ L
def CRPath (V : Finset Pt) (G : Finset Edge) (σ : StripSpec) (L : List StripSpec) : Prop :=
  ValidStrip V G σ ∧ CRChain V G σ L
def wt (σ : StripSpec) (L : List StripSpec) : ℕ := σ.n + (L.map StripSpec.n).sum
section progress
def EndOK (V : Finset Pt) (G : Finset Edge) (σ : StripSpec) : Prop :=
  σ.n % 2 = 0 → IsCell V (endCell σ) ∧ lat1 (endCell σ) σ.s ∈ G ∧ lat2 (endCell σ) σ.s ∈ G ∧
    back (endCell σ) σ.s ∉ G ∧ front (endCell σ) σ.s ∉ G
end progress
end ULHC


