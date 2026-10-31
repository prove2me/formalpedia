-- Prove2me | Definitions.Def_SlottingFees_Regions
-- name    : SlottingFees_Regions
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T18:51:27.090369+00:00
-- url     : https://prove2.me/theorems/5b028c58-42a3-42e3-9ec7-3f6dd473ed7f
-- title:
--   Regions $\Omega^k_A$, $\bar\Omega_A$, $\Phi_\uparrow$ (corrected), $\Phi_\downarrow$, $\Phi_0$
-- statement:
--   The parameter regions of Propositions 3–5. Write $r=v_1/(v_1+v_2)$.
--
--   1. **Proposition 3 (reconstructed).** Let $L(\omega)=\max\{3v_1/16,\,v_2/4\}$ if $r\ge1/2$ and $L(\omega)=\max\{v_1/4,\,3v_2/16\}$ otherwise. Then
--   $$
--   \Omega^+_{\{1,2\}}=\{\omega\in\Omega:\ K<v_{12}+2S^{|2|}-L(\omega)\},
--   $$
--   and on $\Omega\setminus\Omega^+_{\{1,2\}}$: $\Omega^0_{\{1\}}$ where $r\in[1/2,4/7]$, $\Omega^+_{\{1\}}$ where $r\in(4/7,1]$, $\Omega^0_{\{2\}}$ where $r\in[3/7,1/2)$, $\Omega^+_{\{2\}}$ where $r\in[0,3/7)$.
--   2. **Proposition 4.** $\bar\Omega_{\{1\}}=\{\omega\in\Omega: v_1\ge v_2,\ K\ge v_{12}-\max\{v_1/16,v_2/4\}\}$, $\bar\Omega_{\{2\}}=\{\omega\in\Omega: v_1<v_2,\ K\ge v_{12}-\max\{v_1/4,v_2/16\}\}$, $\bar\Omega_{\{1,2\}}=\Omega\setminus(\bar\Omega_{\{1\}}\cup\bar\Omega_{\{2\}})$.
--   3. **Proposition 5.**
--   $$
--   \Phi_\uparrow=\{\omega\in\Omega: v_1\ge v_2,\ v_{12}-\max\{\tfrac{v_1}{16},\tfrac{v_2}{4}\}\le K<v_{12}+2S^{|2|}-\max\{\tfrac{3v_1}{16},\tfrac{v_2}{4}\}\}\cup\{\omega\in\Omega: v_1<v_2,\ v_{12}-\max\{\tfrac{v_1}{4},\tfrac{v_2}{16}\}\le K<v_{12}+2S^{|2|}-\max\{\tfrac{v_1}{4},\tfrac{3v_2}{16}\}\},
--   $$
--   $$
--   \Phi_\downarrow=\{\omega\in\Omega: v_1\ge v_2,\ v_{12}+2S^{|2|}-\tfrac{3v_1}{16}\le K<v_{12}-\max\{\tfrac{v_1}{16},\tfrac{v_2}{4}\}\}\cup\{\omega\in\Omega: v_1<v_2,\ v_{12}+2S^{|2|}-\tfrac{3v_2}{16}\le K<v_{12}-\max\{\tfrac{v_1}{4},\tfrac{v_2}{16}\}\},
--   $$
--   and $\Phi_0=\Omega\setminus(\Phi_\downarrow\cup\Phi_\uparrow)$.
--
--   **Formalization Note** The sets $\Omega^k_A$ are defined in the paper's online supplement, which the source artifact does not contain; item 1 is reconstructed from Propositions 1–2 and agrees with every printed clause of Propositions 3 and 5 and with Corollary 2. The paper prints $\max\{v_1/16,v_2/4\}$ in the lower bound of the second set of $\Phi_\uparrow$; that statement is false (at $(1.1,1,0.13,0,0)\in\Omega$ the benchmark carries both products), and the bound is corrected to its mirror $\max\{v_1/4,v_2/16\}$, as in $\bar\Omega_{\{2\}}$. Part (c) prints $\Omega\setminus(\Omega_\downarrow\cup\Omega_\uparrow)$, with undefined symbols read as $\Phi_\downarrow,\Phi_\uparrow$.
-- source:
--   Alan–Kurtuluş–Nakkas, Retail Category Management with Slotting Fees, MSOM (2024), doi:10.1287/msom.2022.0143, Proposition 3, p.17; Proposition 4, p.20; Proposition 5, pp.20–21

import Mathlib
import Definitions.Def_SlottingFees_ClosedForms

namespace SlottingFees

/-- The retailer's `|A| = 1` equilibrium profit plus `K` on Ω, read from Proposition 1 (11),
pp.12–13, with its endpoints corrected: `L(ω) = max{3v₁/16, v₂/4}` if `v₁/(v₁+v₂) ≥ 1/2`, and
`max{v₁/4, 3v₂/16}` otherwise.

**Formalization Note** Auxiliary to the reconstruction of the sets `Ω^k_A` of Proposition 3,
whose definitions are in the paper's online supplement (not in the source artifact).
Products 1, 2 are indices `0`, `1`. -/
noncomputable def lowVarietyGross (ω : Params) : ℝ :=
  if 1 / 2 ≤ ω.ratio then max (3 * ω.v 0 / 16) (ω.v 1 / 4)
  else max (ω.v 0 / 4) (3 * ω.v 1 / 16)

/-- `Ω^+_{1,2}` of Proposition 3, p.17 (reconstructed): the points of Ω at which high product
variety is strictly more profitable, `K < v₁₂ + 2S^{|2|} − L(ω)`.

**Formalization Note** The paper defines the five sets `Ω^k_A` in the proof of Proposition 3, in
the online supplement, which the source artifact does not contain. This reconstruction follows
from Propositions 1–2 and agrees with every printed clause of Propositions 3 and 5 and of
Corollary 2. -/
def OmegaPlus12 : Set Params :=
  {ω | ω ∈ Omega ∧ ω.K < ω.v12 + 2 * ω.S2 - lowVarietyGross ω}

/-- `Ω^0_{{1}}` of Proposition 3, p.17 (reconstructed): low variety, product 1 carried, no
slotting fee; the points of `Ω \ Ω^+_{1,2}` with `v₁/(v₁+v₂) ∈ [1/2, 4/7]`. -/
def Omega0_1 : Set Params :=
  {ω | ω ∈ Omega ∧ ω ∉ OmegaPlus12 ∧ 1 / 2 ≤ ω.ratio ∧ ω.ratio ≤ 4 / 7}

/-- `Ω^+_{{1}}` of Proposition 3, p.17 (reconstructed): low variety, product 1 carried, positive
slotting fee; the points of `Ω \ Ω^+_{1,2}` with `v₁/(v₁+v₂) ∈ (4/7, 1]`. -/
def OmegaPlus_1 : Set Params :=
  {ω | ω ∈ Omega ∧ ω ∉ OmegaPlus12 ∧ 4 / 7 < ω.ratio}

/-- `Ω^0_{{2}}` of Proposition 3, p.17 (reconstructed): low variety, product 2 carried, no
slotting fee; the points of `Ω \ Ω^+_{1,2}` with `v₁/(v₁+v₂) ∈ [3/7, 1/2)`. -/
def Omega0_2 : Set Params :=
  {ω | ω ∈ Omega ∧ ω ∉ OmegaPlus12 ∧ 3 / 7 ≤ ω.ratio ∧ ω.ratio < 1 / 2}

/-- `Ω^+_{{2}}` of Proposition 3, p.17 (reconstructed): low variety, product 2 carried, positive
slotting fee; the points of `Ω \ Ω^+_{1,2}` with `v₁/(v₁+v₂) ∈ [0, 3/7)`. -/
def OmegaPlus_2 : Set Params :=
  {ω | ω ∈ Omega ∧ ω ∉ OmegaPlus12 ∧ ω.ratio < 3 / 7}

/-- `Ω̄_{{1}} ≡ {ω ∈ Ω : v₁ ≥ v₂, K ≥ v₁₂ − max{v₁/16, v₂/4}}`, Proposition 4, p.20. -/
def OmegaBar1 : Set Params :=
  {ω | ω ∈ Omega ∧ ω.v 1 ≤ ω.v 0 ∧ ω.v12 - max (ω.v 0 / 16) (ω.v 1 / 4) ≤ ω.K}

/-- `Ω̄_{{2}} ≡ {ω ∈ Ω : v₁ < v₂, K ≥ v₁₂ − max{v₁/4, v₂/16}}`, Proposition 4, p.20. -/
def OmegaBar2 : Set Params :=
  {ω | ω ∈ Omega ∧ ω.v 0 < ω.v 1 ∧ ω.v12 - max (ω.v 0 / 4) (ω.v 1 / 16) ≤ ω.K}

/-- `Ω̄_{{1,2}} ≡ Ω \ (Ω̄_{{1}} ∪ Ω̄_{{2}})`, Proposition 4, p.20. -/
def OmegaBar12 : Set Params := Omega \ (OmegaBar1 ∪ OmegaBar2)

/-- `Φ↑`, Proposition 5(a), p.20, **corrected**: the union of
`{ω ∈ Ω : v₁ ≥ v₂, v₁₂ − max{v₁/16, v₂/4} ≤ K < v₁₂ + 2S^{|2|} − max{3v₁/16, v₂/4}}` and
`{ω ∈ Ω : v₁ < v₂, v₁₂ − max{v₁/4, v₂/16} ≤ K < v₁₂ + 2S^{|2|} − max{v₁/4, 3v₂/16}}`.

**Formalization Note** The paper prints `max{v₁/16, v₂/4}` in the lower bound of the second set
as well. That is the `v₁ ≥ v₂` bound of Proposition 4, not its mirror `max{v₁/4, v₂/16}`
(`Ω̄_{{2}}`), and the printed statement is false: at
`(q₁, q₂, c₁, c₂, K) = (1.1, 1, 0.13, 0, 0) ∈ Ω` the printed condition holds but the benchmark
carries both products (`v₁₂ ≈ 0.2182 > max{v₁/4, v₂/16} ≈ 0.2138`). -/
def PhiUp : Set Params :=
  {ω | ω ∈ Omega ∧ ω.v 1 ≤ ω.v 0 ∧
      ω.v12 - max (ω.v 0 / 16) (ω.v 1 / 4) ≤ ω.K ∧
      ω.K < ω.v12 + 2 * ω.S2 - max (3 * ω.v 0 / 16) (ω.v 1 / 4)} ∪
  {ω | ω ∈ Omega ∧ ω.v 0 < ω.v 1 ∧
      ω.v12 - max (ω.v 0 / 4) (ω.v 1 / 16) ≤ ω.K ∧
      ω.K < ω.v12 + 2 * ω.S2 - max (ω.v 0 / 4) (3 * ω.v 1 / 16)}

/-- `Φ↓`, Proposition 5(b), p.21, as printed: the union of
`{ω ∈ Ω : v₁ ≥ v₂, v₁₂ + 2S^{|2|} − 3v₁/16 ≤ K < v₁₂ − max{v₁/16, v₂/4}}` and
`{ω ∈ Ω : v₁ < v₂, v₁₂ + 2S^{|2|} − 3v₂/16 ≤ K < v₁₂ − max{v₁/4, v₂/16}}`. -/
def PhiDown : Set Params :=
  {ω | ω ∈ Omega ∧ ω.v 1 ≤ ω.v 0 ∧
      ω.v12 + 2 * ω.S2 - 3 * ω.v 0 / 16 ≤ ω.K ∧
      ω.K < ω.v12 - max (ω.v 0 / 16) (ω.v 1 / 4)} ∪
  {ω | ω ∈ Omega ∧ ω.v 0 < ω.v 1 ∧
      ω.v12 + 2 * ω.S2 - 3 * ω.v 1 / 16 ≤ ω.K ∧
      ω.K < ω.v12 - max (ω.v 0 / 4) (ω.v 1 / 16)}

/-- `Φ0 ≡ Ω \ (Φ↓ ∪ Φ↑)`, Proposition 5(c), p.21.

**Formalization Note** The paper prints `Ω \ (Ω↓ ∪ Ω↑)`; the symbols `Ω↓`, `Ω↑` are defined
nowhere, and the sets of parts (a), (b) are `Φ↑`, `Φ↓` (the text on p.21 calls this set
`Φ0`). -/
def PhiZero : Set Params := Omega \ (PhiDown ∪ PhiUp)

end SlottingFees


