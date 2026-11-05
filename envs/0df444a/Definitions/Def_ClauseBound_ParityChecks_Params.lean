-- Prove2me | Definitions.Def_ClauseBound_ParityChecks_Params
-- name    : ClauseBound_ParityChecks_Params
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-04T15:17:13.528751+00:00
-- url     : https://prove2.me/theorems/205c22f2-9b93-4b5a-b796-efafe907d8b2
-- title:
--   Params
-- statement:
--   Definitions and structural lemmas for Params, from Anthropic’s pinned ETH development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/ParityChecks/Params.lean

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ClauseBound_ParityChecks_RunDefs
import Definitions.Def_ClauseBound_Rec_Few
set_option autoImplicit false
section
section
@[expose] section
namespace ClauseBound.ParityChecks
open Finset _root_.ParityChecks
@[expose] def LD (Δ : ℕ) : ℕ := Nat.clog 2 (2 * Δ)
@[expose] def nbOf (n Δ : ℕ) : ℕ := n / LD Δ
@[expose] def beta0 (m nb : ℕ) : ℕ := Nat.clog 2 (m.choose (nb + 1))
@[expose] def rOf (n β₀ : ℕ) : ℕ := (59 * (n + β₀ + 3) + 39) / 40
@[expose] def i0Of (n : ℕ) : ℕ := (20 * n + Nat.log 2 n - 1) / Nat.log 2 n
@[expose] def beta1 (m i₀ : ℕ) : ℕ := (range (i₀ + 1)).sup fun i => Nat.clog 2 (m.choose i)
@[expose] def parOf (n Δ m : ℕ) : Par where
  m := m
  nb := nbOf n Δ
  r := rOf n (beta0 m (nbOf n Δ))
  i₀ := i0Of n
  β := n + beta0 m (nbOf n Δ) + beta1 m (i0Of n) + 2
namespace Params
end Params
open Params
namespace Params
end Params
namespace Params
structure Big (c n Δ m ℓ t : ℕ) : Prop where
  hℓ : ℓ = Nat.log 2 n
  ht : t = Nat.clog 2 (ℓ + 1)
  hℓ1 : 1 ≤ ℓ
  hA : 84 * (c + 1) * t ≤ ℓ
  hΔ2 : 2 ≤ Δ
  hΔ : Δ ≤ (ℓ + 1) ^ c
  hnb : nbOf n Δ < m
  hm : m ≤ Δ * n
namespace Big
variable {c n Δ m ℓ t : ℕ} (b : Big c n Δ m ℓ t)
include b
end Big
end Params
namespace Params
namespace Big
variable {c n Δ m ℓ t : ℕ} (b : Big c n Δ m ℓ t)
include b
end Big
end Params
end ClauseBound.ParityChecks


