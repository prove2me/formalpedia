-- Prove2me | Definitions.Def_PaddedDescent_F_CertNet
-- name    : PaddedDescent_F_CertNet
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-04T22:08:17.053185+00:00
-- url     : https://prove2.me/theorems/0c7beac2-d011-470a-aff7-c29ab8da75ed
-- title:
--   Cert Net
-- statement:
--   Definitions and structural lemmas for Cert Net, from Anthropic’s pinned ETH development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/PaddedDescent/F/CertNet.lean

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_PaddedDescent_F_Interfaces
import Definitions.Def_PaddedDescent_F_FuelCert
set_option autoImplicit false
section
section
namespace PaddedDescent.F.CertNet
open Groundwork Groundwork.Prog Groundwork.Prog.NetE PaddedDescent.F
variable {α β γ ε : Type} [Enc α] [Enc β] [Enc γ] [Enc ε]
variable {C : Type} [Enc C] {Np : PNet C}
structure KeepsU (Np : PNet C) : Prop where
  n : Unary fun p : C × ℕ => Np.n p.1 p.2
  cap : Unary fun p : C × ℕ × ℕ => Np.cap p.1 p.2.1 p.2.2
section
variable (h : KeepsU Np)
include h
end
section
variable (h : KeepsU Np)
include h
end
end PaddedDescent.F.CertNet
namespace PaddedDescent.F
open Groundwork
end PaddedDescent.F


