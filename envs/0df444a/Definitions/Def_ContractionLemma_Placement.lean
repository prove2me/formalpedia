-- Prove2me | Definitions.Def_ContractionLemma_Placement
-- name    : ContractionLemma_Placement
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T20:57:11.607213+00:00
-- url     : https://prove2.me/theorems/2531275b-4bf0-4ca1-a706-9c17f5012cd0
-- title:
--   Packets, slots, the shift curve $W(T)$ and the shift $\sigma_t$
-- statement:
--   A **placement** puts the edges into packets of $L=2^a$ slots numbered $0,\dots,L-1$, with at most one edge per slot of a packet; slots may be empty. The **shift curve** is the wiring with entries
--
--   $$
--   W_{xy}(T)=K_{y-x}(T)
--   $$
--
--   when the row bit at slot $x$ and the column bit at slot $y$ lie in the same packet, and $0$ between packets. The **shift** $\sigma_t$ is the $0/1$ matrix wiring the row bit in slot $x$ of each packet to the column bit in slot $x+t$ of the same packet.
--
--   **Formalization Note** Rows and columns are indexed by the edges. A slot without an edge has no bit, so it has no row or column in these matrices.
-- source:
--   Gajulapalli, The Contraction Lemma Beyond ETH (manuscript, sha256 049caea1…), App. A.4.1, pp.57–58

import Mathlib
import Definitions.Def_ContractionLemma_kernel

set_option autoImplicit false

namespace ContractionLemma

open Polynomial

/-- **A placement of the edges into packets of `L = 2^a` slots** — Gajulapalli, *The
Contraction Lemma Beyond ETH* (manuscript, sha256 049caea1…), App. A.4.1, p.57.

There are `np` packets; edge `e` sits in packet `packet e` at slot `slot e ∈ {0, …, L − 1}`,
and two edges never share a slot of the same packet (`inj`). Slots may be empty. -/
structure Placement (E : Type*) (a : ℕ) where
  /-- number of packets -/
  np : ℕ
  /-- the packet of each edge -/
  packet : E → Fin np
  /-- the slot of each edge -/
  slot : E → Fin (2 ^ a)
  /-- at most one edge per slot of a packet -/
  inj : ∀ e f, packet e = packet f → slot e = slot f → e = f

namespace Placement

variable {E : Type*} {a : ℕ}

/-- **The shift curve `W(T)`** (p.58): inside a packet `W_{xy}(T) = K_{y−x}(T)` (row bit at
slot `x`, column bit at slot `y`), and `W` is `0` between packets. Rows and columns are indexed
by the edges. -/
noncomputable def wiring (pl : Placement E a) : Matrix E E ℚ[X] := fun e f =>
  if pl.packet e = pl.packet f then kernel a ((pl.slot f : ℤ) - (pl.slot e : ℤ)) else 0

/-- **The shift `σ_t`** (p.58): the `0/1` matrix wiring the row bit in slot `x` of each packet
to the column bit in slot `x + t` of the same packet. -/
def shiftMat (pl : Placement E a) (t : ℤ) : Matrix E E ℚ := fun e f =>
  if pl.packet e = pl.packet f ∧ (pl.slot f : ℤ) = (pl.slot e : ℤ) + t then 1 else 0

end Placement

end ContractionLemma


