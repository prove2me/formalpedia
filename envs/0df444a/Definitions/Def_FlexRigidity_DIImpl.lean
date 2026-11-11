-- Prove2me | Definitions.Def_FlexRigidity_DIImpl
-- name    : FlexRigidity_DIImpl
-- status  : Definition
-- author  : @iris
-- created : 2026-11-10T21:18:42.301782+00:00
-- url     : https://prove2.me/theorems/d70840fb-bdd2-47a4-a831-1f5228445480
-- title:
--   Device implementation and Bob attack (Postulate Set 5.4)
-- statement:
--   Before round $i$ the complete memories of Alice's and Bob's components are $M^{\mathrm A}_i=\mathbb C^{d^{\mathrm A}_i}$ and $M^{\mathrm B}_i=\mathbb C^{d^{\mathrm B}_i}$ (no dimension bound, arbitrary history dependence). In round $i$ Alice's device is an instrument $\{\mathcal E^{\mathrm A,x,a}_i\}_a$ for each input $x$ (it never sees $u_i$ or $y_i$); Bob's operation is an instrument $\{\mathcal E^{\mathrm B,\mathrm{test},y,b}_i\}_b$ on a test round with question $y$ and a channel $\mathcal E^{\mathrm B,\mathrm{gen}}_i$ on a generation round. Bob's device and his own memory form one register, so these are all of Bob's operations; within a round the devices act as $\mathcal E^{\mathrm A}_i\otimes\mathcal E^{\mathrm B}_i$ (Postulate 5.4(i)). `IsAllowed n` says that for the first $n$ rounds every instrument element is CP, every instrument sums to a channel, and $\mathcal E^{\mathrm B,\mathrm{gen}}_i$ is a channel.
-- source:
--   Arqand, Kundu, Tan, Flexible rigidity: Compiling generic trusted-preparation protocols into sequential device-independent protocols, arXiv:2610.00444 (artifact sha256 8c67699d…), Postulate Set 5.4, p. 40; §5.3.1, pp. 43–44

import Mathlib
import Definitions.Def_QAlgorithms_Defs_Channel
import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P35
import Definitions.Def_FlexRigidity_IsCPMap
set_option autoImplicit false

open scoped Matrix ComplexOrder ENNReal
open Filter Topology
open QAlgorithms (Superop IsChannel krausApply idTensorSuperop piSuperop)
open QAlgorithms.Papers.Independent.Dependency50.P35 (tr Density Dominates divergence rawTrace spectralPower maxRelative POVM leftMarginal rightMarginal)

noncomputable section

namespace FlexRigidity

/-- **A device implementation and Bob attack in the sequential DI setting, Postulate Set 5.4**
(Arqand–Kundu–Tan, *Flexible rigidity*, arXiv:2610.00444, artifact sha256 8c67699d…, pp. 40–44):
the complete memories of Alice's and Bob's components before round `i` are `M^A_i = ℂ^{dA i}` and
`M^B_i = ℂ^{dB i}` (no dimension bound, arbitrary history dependence). In round `i` Alice's
device is an instrument `{E^{A,x,a}_i : M^A_i → M^A_{i+1}}_a` for each input `x` (it never sees
`u_i` or `y_i`); Bob's operation in a test round with question `y` is an instrument
`{E^{B,test,y,b}_i : M^B_i → M^B_{i+1}}_b`, and in a generation round a channel
`E^{B,gen}_i : M^B_i → M^B_{i+1}`. Bob's device and his own memory form the one register `M^B`, so
these maps are all of Bob's operations. Within a round the device channel factors as
`E^A_i ⊗ E^B_i` (Postulate 5.4(i)).

`IsAllowed n` says that for every round `i < n` each instrument element is completely positive,
each instrument sums to a channel, and `E^{B,gen}_i` is a channel. -/
structure DIImpl (X Y A B : Type) where
  /-- dimension of Alice's device memory `M^A_i` -/
  dA : ℕ → ℕ
  /-- dimension of Bob's memory `M^B_i` -/
  dB : ℕ → ℕ
  /-- Alice's device instrument `E^{A,x,a}_i` -/
  EA : (i : ℕ) → X → A → Superop (Fin (dA i)) (Fin (dA (i + 1)))
  /-- Bob's test-round instrument `E^{B,test,y,b}_i` -/
  EBt : (i : ℕ) → Y → B → Superop (Fin (dB i)) (Fin (dB (i + 1)))
  /-- Bob's generation-round channel `E^{B,gen}_i` -/
  EBg : (i : ℕ) → Superop (Fin (dB i)) (Fin (dB (i + 1)))

/-- The implementation is allowed for `n` rounds. -/
def DIImpl.IsAllowed {X Y A B : Type} [Fintype A] [Fintype B] (I : DIImpl X Y A B) (n : ℕ) : Prop :=
  ∀ i < n, (∀ x a, IsCPMap (I.EA i x a)) ∧ (∀ x, IsChannel (fun ρ => ∑ a, I.EA i x a ρ)) ∧
    (∀ y b, IsCPMap (I.EBt i y b)) ∧ (∀ y, IsChannel (fun ρ => ∑ b, I.EBt i y b ρ)) ∧
    IsChannel (I.EBg i)

end FlexRigidity


