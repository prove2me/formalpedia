-- Prove2me | Definitions.Def_SamplingAC0_Supplement_ACSampler
-- name    : SamplingAC0_Supplement_ACSampler
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T13:39:49.193234+00:00
-- url     : https://prove2.me/theorems/447f18d2-7e3e-4adc-bc2a-422cd5b50518
-- title:
--   AC$^0$ sampler, its wires, depth and output distribution
-- statement:
--   An **AC$^0$ sampler** with $\ell$ output bits takes $m$ uniform input bits and computes each output bit by a circuit of unbounded fan-in AND and OR gates over the inputs, with negations at the inputs and constants allowed. Its **number of wires** is the total fan-in of all gates, its **depth** the largest number of gates on a path from an input to an output, and its **output distribution** is the distribution of its output on a uniform input $U\in\{0,1\}^m$.
--
--   Theorem 7 bounds AC$^0$ samplers by $n^c$ wires and depth $c$.
--
--   **Formalization Note** Each output bit has its own circuit (the published `MantriCVQ.ACCircuit`); the wires are summed over these circuits (published wire count `HypercliqueAC0.FixedDepth.Supplement.wires`) and the depth is the maximum. A circuit with shared gates and $W$ wires gives per-output circuits with at most $\ell W$ wires in total and the same depth, so bounds of the form $n^c$ and $c$ mean the same in both models.
-- source:
--   Riazanov–Viola, Sampling Tools and the Power of AC0, STOC 2027 submission (manuscript sha256 99c33d30…), Theorem 7 p.4; §4 pp.13–14 (wire size, depth)

import Mathlib
import Definitions.Def_MantriCVQ_ACCircuit
import Definitions.Def_HypercliqueAC0_FixedDepth_Supplement_Wires
import Definitions.Def_SamplingAC0_law
set_option autoImplicit false

namespace SamplingAC0.Supplement

/-- **AC0 sampler (multi-output AC0 circuit on uniform input bits).** Riazanov–Viola, *Sampling
Tools and the Power of AC0*, STOC 2027 submission (manuscript sha256 99c33d30…), Theorem 7, p.4
("an AC0 circuit of n^c wires and depth c whose output distribution is exactly (U, f(U))"), and §4,
pp.13–14 ("AC0 sampler S1 of wire size n^c and depth c").

An AC0 sampler with `ℓ` output bits has some number `m` of input bits and, for each output
position, a circuit of unbounded fan-in AND and OR gates over the inputs, with negations at the
inputs and constants allowed (the published `MantriCVQ.ACCircuit`).

**Formalization Note.** Each output bit is given by its own circuit; the sampler's wire count is
the sum of the wire counts of these circuits (`wires`) and its depth their maximum (`depth`). A
circuit with shared gates and `W` wires yields per-output circuits with at most `ℓ · W` wires in
total and the same depth, and conversely per-output circuits are a shared circuit with the same
wires, so bounds of the form `n^c` and `c` mean the same in both models. -/
structure ACSampler (ℓ : ℕ) where
  /-- the number of uniform input bits -/
  m : ℕ
  /-- the circuit computing each output bit -/
  out : Fin ℓ → MantriCVQ.ACCircuit (Fin m)

/-- The number of wires of the sampler: the total fan-in of all its gates (published
`HypercliqueAC0.FixedDepth.Supplement.wires`), summed over the output circuits. -/
def ACSampler.wires {ℓ : ℕ} (C : ACSampler ℓ) : ℕ :=
  ∑ i, HypercliqueAC0.FixedDepth.Supplement.wires (C.out i)

/-- The depth of the sampler: the largest number of gates on a path from an input to an output
(published `MantriCVQ.ACCircuit.depth`), maximised over the outputs. -/
def ACSampler.depth {ℓ : ℕ} (C : ACSampler ℓ) : ℕ :=
  Finset.univ.sup fun i => (C.out i).depth

/-- The output of the sampler on the input bits `x`. -/
def ACSampler.eval {ℓ : ℕ} (C : ACSampler ℓ) (x : Fin C.m → Bool) : Fin ℓ → Bool :=
  fun i => (C.out i).eval x

/-- The output distribution of the sampler: its output on a uniform input in `{0,1}^m`. -/
noncomputable def ACSampler.dist {ℓ : ℕ} (C : ACSampler ℓ) : PMF (Fin ℓ → Bool) :=
  SamplingAC0.law C.eval

end SamplingAC0.Supplement


