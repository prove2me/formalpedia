-- Prove2me | Definitions.Def_ClauseBound_ParityChecks_Run
-- name    : ClauseBound_ParityChecks_Run
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-04T15:19:11.488503+00:00
-- url     : https://prove2.me/theorems/b04a98ec-488e-40ce-bb61-a82a4d181705
-- title:
--   Run
-- statement:
--   Definitions and structural lemmas for Run, from Anthropic’s pinned ETH development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/ParityChecks/Run.lean

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ClauseBound_ParityChecks_Num
import Definitions.Def_ClauseBound_ParityChecks_Congr
set_option autoImplicit false
section
section
@[expose] section
namespace ClauseBound.ParityChecks
open Finset _root_.ParityChecks
variable {X : Type} [Fintype X] (q : Par) (V : X → Finset (Fin q.m)) (orcA : List Chk → ℤ) (orcB : List Chk → Chk → ℕ → ℕ → ℤ)
@[expose] def OrcOK : Prop := ∀ (Ls : List Chk) (cur : Chk) (e : ℕ), Ls.length < q.r → (∀ L ∈ Ls, ChkOK q.m L) → ChkOK e cur → e ≤ q.m →
  Tent q (lam q.m (Ls ++ [cur])) →
    orcA Ls ≡ Aint V q.nb Ls.length (lam q.m (Ls ++ [cur])) [ZMOD 2 ^ q.β] ∧
    ∀ i ≤ q.i₀, orcB Ls cur e i ≡ Bint V q.nb i Ls.length (lam q.m (Ls ++ [cur])) (Dset q.m e) [ZMOD 2 ^ q.β]
namespace Run
variable {q}
structure Bd (q : Par) (Λ : ℕ → Finset (Fin q.m)) : Prop where
  inc : ((∑ j' ∈ range q.r, #(Λ j') : ℕ) : ℚ) < 8 * pr q.nb * q.m * q.r
  row : ∀ j' < q.r, (2 : ℚ) ^ #(Λ j') < 8 * q.r * (1 + pr q.nb) ^ q.m
  col : ∀ x : Fin q.m, (2 : ℚ) ^ #{j' ∈ range q.r | x ∈ Λ j'} < 8 * q.m * (1 + pr q.nb) ^ q.r
section Pot
variable (q)
def UU (Ls : List Chk) (cur : Chk) (e : ℕ) : ℚ := Ups V q.nb q.r Ls.length (lam q.m (Ls ++ [cur])) (Dset q.m e)
def tUU (Ls : List Chk) (cur : Chk) (e : ℕ) : ℚ :=
  tUpar V q.nb q.r q.i₀ Ls.length (lam q.m (Ls ++ [cur])) (Dset q.m e) + Uinc q.nb q.r Ls.length (lam q.m (Ls ++ [cur])) (Dset q.m e)
    + Urow q.nb q.r Ls.length (lam q.m (Ls ++ [cur])) (Dset q.m e) + Ucol q.nb q.r Ls.length (lam q.m (Ls ++ [cur])) (Dset q.m e)
def NN (X : Type) [Fintype X] (q : Par) : ℚ := ((Fintype.card X * q.m.choose (q.nb + 1) : ℕ) : ℚ)
end Pot
variable {V} {orcA orcB} {ε : ℚ}
structure Inv (q : Par) (V : X → Finset (Fin q.m)) (ε : ℚ) (Ls : List Chk) (cur : Chk) (e : ℕ) : Prop where
  lt : Ls.length < q.r
  done : ∀ L ∈ Ls, ChkOK q.m L
  okc : ChkOK e cur
  le : e ≤ q.m
  pot : UU q V Ls cur e ≤ 1 / 2 + ((Ls.length * q.m + e : ℕ) : ℚ) * (ε * NN X q)
end Run
open Run
end ClauseBound.ParityChecks


