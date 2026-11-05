-- Prove2me | Definitions.Def_ClauseBound_ParityChecks_ProgDefs
-- name    : ClauseBound_ParityChecks_ProgDefs
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-04T23:00:57.68329+00:00
-- url     : https://prove2.me/theorems/5fa99908-b474-4e33-94c3-466f2028335b
-- title:
--   Prog Defs
-- statement:
--   Definitions and structural lemmas for Prog Defs, from Anthropic’s pinned ETH development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/ParityChecks/ProgDefs.lean

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ClauseBound_ParityChecks_NetDefs
import Definitions.Def_ClauseBound_ParityChecks_RunDefs
import Definitions.Def_ClauseBound_ParityChecks_Params
import Definitions.Def_ClauseBound_Alg_TopNet
import Theorems.Thm_Groundwork_PolyT_length
attribute [local fun_prop] Groundwork.PolyT.length


set_option autoImplicit false
section
section
namespace ClauseBound.ParityChecks
open Groundwork Groundwork.Prog PaddedDescent.F PaddedDescent.F.Mark ClauseBound.Alg ClauseBound.TopN ClauseBound.TopN.EvalW
def rep (n : ℕ) : U := List.replicate n ()
def parQ (n Δ m : ℕ) : Par := if m ≤ nbOf n Δ then { parOf n Δ m with r := 0 } else parOf n Δ m
def capM (q : Par) : ℕ := q.β - 1 + q.r
def blkOL (Δ : ℕ) : ℕ := 2 * Δ + 16 * Δ * LD Δ + 1
def bitOL (Δ : ℕ) : ℕ := Nat.clog 2 (blkOL Δ)
def colMax (n Δ : ℕ) : ℕ := Nat.clog 2 (16 * Δ * n) + 18 * LD Δ + 2
def rowMax (n Δ : ℕ) : ℕ := Nat.clog 2 (96 * n) + 3 * Δ * LD Δ + 2
def occOL (n Δ : ℕ) : ℕ := max (Δ * (2 + colMax n Δ)) (rowMax n Δ)
def parM (n Δ : ℕ) (q : Par) : U × U × U × U := (rep (n + q.r), rep (capM q), rep (bitOL Δ), rep (blkOL Δ))
def UbOL (k K n Δ : ℕ) : ℕ := Ub (k + 1) (3 * K ^ 8) (7 * n) (11 * n) (bitOL Δ) 3
def PbOL (K n Δ : ℕ) : ℕ := Pb (3 * K ^ 8) (7 * n) (bitOL Δ) (occOL n Δ)
section
variable {Idx : Type} [Enc Idx] (S : Solver Idx) (k : ℕ) (pad : U) (i : Idx) (n Δ : ℕ) (q : Par)
def evW (ws : List ℤ) (lo hi : List ℕ) (Ls : List Fml) : ℤ :=
  evalV (k + 1) pad (rep (3 * S.K i ^ 8))
    (fun c => GW c.2.1.length ws lo hi (tl c.1.1.length c.2.1 c.2.2) * valS S pad i (UbOL k (S.K i) n Δ) (PbOL (S.K i) n Δ) markF c)
    (parM n Δ q) Ls
def orcA (ψ : Fml) (Ls : List Chk) : ℤ :=
  evW S k pad i n Δ q [1, -2] [q.nb + 1, 0] [q.nb + 1, capM q] [ψ, incL n ψ (Ls.take Ls.length) Ls.length] / 2 ^ q.r
def orcB (ψ : Fml) (Ls : List Chk) (cur : Chk) (e j : ℕ) : ℤ :=
  evW S k pad i n Δ q [1, -2, 1] [q.nb + 1, 0, j] [q.nb + 1, capM q, j] [ψ, incL n ψ (Ls ++ [cur]) Ls.length, ψ.drop e] / 2 ^ q.r
def runToF (ψ : Fml) (Ls : List Chk) (e : ℕ) : Chk :=
  (List.range e).foldl (fun cur x => cap pad [] (q.decide1 (orcA S k pad i n Δ q ψ) (orcB S k pad i n Δ q ψ) Ls cur x)) (cap pad [] [])
def runF (ψ : Fml) : List Chk :=
  (List.range q.r).foldl (fun Ls _ => cap pad [] (Ls ++ [runToF S k pad i n Δ q ψ Ls q.m])) (cap pad [] [])
def countOL (ψ : Fml) : ℕ :=
  ((evW S k pad i n Δ q [-1, -2] [0, 0] [q.nb, capM q] [ψ, incL n ψ ((runF S k pad i n Δ q ψ).take q.r) q.r] / 2 ^ q.r) % 2 ^ (n + 1)).toNat
end
def StEvW : Prop := ∀ (Idx : Type) [Enc Idx] (S : Solver Idx) (ok : Idx → Prop), S.Correct ok → ∀ (k : ℕ) (pad : U) (i : Idx) (n Δ : ℕ) (q : Par)
  (ws : List ℤ) (lo hi : List ℕ) (Ls : List Fml), ok i → 2 ≤ S.K i → q.r ≤ 6 * n → capM q ≤ 11 * n → Ls.length ≤ 3 → WfL (k + 1) (n + q.r) Ls → (∀ v, (occ Ls.flatten v).length ≤ occOL n Δ) →
  Ls.flatten.length ≤ blkOL Δ * (n + q.r + 1) → (∀ l < Ls.length, hi.getD l 0 ≤ capM q) →
  nProf (3 * S.K i ^ 8) (cls Ls).length Ls.length ≤ pad.length → 2 ^ needNet S i (UbOL k (S.K i) n Δ) (PbOL (S.K i) n Δ) 0 ≤ pad.length →
  evW S k pad i n Δ q ws lo hi Ls = truncW (n + q.r) ws lo hi Ls
def StShape : Prop := ∀ (k n Δ : ℕ) (q : Par) (ψ : Fml) (Lam : List Chk) (j e : ℕ), ψ.length = q.m → 2 ≤ q.nb → q.m ≤ Δ * n → q.r ≤ 6 * n → n < 2 * (q.nb * LD Δ) →
  WfL k n [ψ] → (∀ v, (occ ψ v).length ≤ Δ) → j ≤ q.r → (∀ L ∈ Lam, L.Nodup ∧ ∀ x ∈ L, x < q.m) → Tent q (lam q.m Lam) →
  WfL (k + 1) (n + q.r) [ψ, incL n ψ Lam j, ψ.drop e] ∧ (∀ v, (occ [ψ, incL n ψ Lam j, ψ.drop e].flatten v).length ≤ occOL n Δ) ∧
    [ψ, incL n ψ Lam j, ψ.drop e].flatten.length ≤ blkOL Δ * (n + q.r + 1)
structure FitsOL {Idx : Type} [Enc Idx] (S : Solver Idx) (k : ℕ) (i : Idx) (n Δ : ℕ) (F : ℕ) : Prop where
  net : 2 ^ needNet S i (UbOL k (S.K i) n Δ) (PbOL (S.K i) n Δ) 0 ≤ F
  prof : nProf (3 * S.K i ^ 8) (blkOL Δ * (7 * n + 1)) 3 ≤ F
  lists : 8 * (6 * n + 1) * (Δ * n + 1) * (Nat.size (Δ * n) + 2) + 8 ≤ F
def StCountOL : Prop := ∀ (Idx : Type) [Enc Idx] (S : Solver Idx) (ok : Idx → Prop), S.Correct ok → ∀ (k : ℕ) (pad : U) (i : Idx) (n Δ : ℕ) (ψ : Fml) (ε : ℚ),
  ok i → 2 ≤ S.K i → WfL k n [ψ] → (∀ v, (occ ψ v).length ≤ Δ) → ψ.length ≤ Δ * n → 2 ≤ nbOf n Δ → n < 2 * (nbOf n Δ * LD Δ) →
  (nbOf n Δ < ψ.length → Hyp (parOf n Δ ψ.length) (2 ^ n) ε ∧ (parOf n Δ ψ.length).r ≤ 6 * n ∧ (parOf n Δ ψ.length).β ≤ 5 * n ∧
    (parOf n Δ ψ.length).i₀ ≤ capM (parOf n Δ ψ.length)) → FitsOL S k i n Δ pad.length →
  countOL S k pad i n Δ (parQ n Δ ψ.length) ψ = nSat n ψ
def StCertCountOL : Prop := ∀ (Idx : Type) [Enc Idx] (S : Solver Idx), S.Poly → ∀ k : ℕ,
  PolyT fun x : U × Idx × (U × U) × Fml => countOL S k x.1 x.2.1 x.2.2.1.1.length x.2.2.1.2.length (parQ x.2.2.1.1.length x.2.2.1.2.length x.2.2.2.length) x.2.2.2
end ClauseBound.ParityChecks


