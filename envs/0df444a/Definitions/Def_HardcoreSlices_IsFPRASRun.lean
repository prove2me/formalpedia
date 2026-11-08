-- Prove2me | Definitions.Def_HardcoreSlices_IsFPRASRun
-- name    : HardcoreSlices_IsFPRASRun
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T06:37:08.290202+00:00
-- url     : https://prove2.me/theorems/950bc848-af22-4d33-a745-41f0966aacf0
-- title:
--   FPAUS and FPRAS runs on the published real RAM
-- statement:
--   A run of an **FPAUS** for a target law $\mu$ at accuracy $\varepsilon$ is a program and an input such that on every coin tape the program has halted within $B$ steps, and its output law is within total variation $\varepsilon$ of $\mu$. A run of an **FPRAS** for $Z$ at $\varepsilon,\delta$ is a program and an input such that on every tape it has halted within $B$ steps with an output $\hat Z\ge0$, and
--   $$\Pr[(1-\varepsilon)Z\le\hat Z\le(1+\varepsilon)Z]\ge1-\delta.$$
--   The time bounds are $K(m+1+\log(1/\varepsilon))^d$ and $K(m+1+1/\varepsilon+\log(1/\delta))^d$. The inputs are the graph (`graphInts`: $m$, $\Delta$, sorted adjacency lists), further integer parameters in cells $-1,-2$, a pinned set in bitmap $0$, and real parameters.
--
--   **Formalization Note** The machine is the published unit-cost real RAM `SubsetConvFPRAS.Machine`, with fair coins and with both value oracles $0$. The paper names no model. The real parameters $\lambda,\varepsilon,\delta$ are unit-cost inputs, and the language has neither floor nor a real-to-integer cast. The probability is by counting $B$-bit tapes. The sampler's output is bitmap $0$.
-- source:
--   Kocurek, Oveis Gharan, Tjowasi, Sampling from the Hardcore Model on Random Regular Bipartite Graphs above the Uniqueness Threshold, arXiv:2604.21847 (version held, sha256 363c225d…), Definition 2.12, pp.11–12; Definition 2.13, p.12

import Mathlib
import Definitions.Def_SubsetConvFPRAS_Machine
import Definitions.Def_LowTempGlauber_SamplerInput
import Definitions.Def_HardcoreSlices_hcLaw
import Definitions.Def_mm_mixing

open Classical

namespace HardcoreSlices

open ExpanderBIS.RandomHardCore

/-- The output law of program `P` from `s₀` over `B` fair coins: the fraction of tapes on which the run of `B` steps has
halted with bitmap `0` equal to `S`. Both value oracles of the published machine are `0`. -/
noncomputable def outLawAt {n : ℕ} (P : SubsetConvFPRAS.Program) (s₀ : SubsetConvFPRAS.State n) (B : ℕ)
    (S : Finset (Fin n)) : ℝ :=
  (SubsetConvFPRAS.tapeCount P (fun _ => 0) (fun _ => 0) s₀ B
      (fun st => st.output.isSome ∧ st.bitmap 0 = S) : ℝ) / 2 ^ B

/-- **One run of an FPAUS** (Definition 2.13, p.12: "Outputs `x ∼ µ̂` satisfying `dTV(µ̂, µ) ≤ ε`"), Kocurek, Oveis Gharan, Tjowasi, *Sampling from the Hardcore Model on Random Regular Bipartite Graphs above the Uniqueness Threshold*, arXiv:2604.21847 (version held, sha256 363c225d…). On every coin tape, `P`
has halted within `B` unit-cost steps, and its output law is within total variation `ε` of `target`. -/
structure IsFPAUSRun {n : ℕ} (P : SubsetConvFPRAS.Program) (s₀ : SubsetConvFPRAS.State n) (B : ℕ)
    (target : Finset (Fin n) → ℝ) (ε : ℝ) : Prop where
  /-- Halting within `B` steps on every tape. -/
  halts : ∀ bits : Fin B → Bool,
    (SubsetConvFPRAS.run P (fun _ => 0) (fun _ => 0) s₀ (SubsetConvFPRAS.extendBits bits) B).output.isSome ∧
      (SubsetConvFPRAS.run P (fun _ => 0) (fun _ => 0) s₀ (SubsetConvFPRAS.extendBits bits) B).work ≤ B
  /-- The output law is `ε`-close to the target. -/
  tv : MarkovMixing.tvDist (outLawAt P s₀ B) target ≤ ε

/-- **One run of an FPRAS** (Definition 2.12, pp.11–12: "Outputs `Ẑ ∈ R+` satisfying
`Pr[(1 − ε)Z ≤ Ẑ ≤ (1 + ε)Z] ≥ 1 − δ`"). On every coin tape, `P` has halted within `B` unit-cost steps with a nonnegative
output, and at least a `1 − δ` fraction of the `2^B` tapes give an output in `[(1 − ε)Z, (1 + ε)Z]`. -/
structure IsFPRASRun {n : ℕ} (P : SubsetConvFPRAS.Program) (s₀ : SubsetConvFPRAS.State n) (B : ℕ)
    (Z ε δ : ℝ) : Prop where
  /-- Halting within `B` steps on every tape, with an output in `ℝ₊`. -/
  halts : ∀ bits : Fin B → Bool,
    (∃ z, (SubsetConvFPRAS.run P (fun _ => 0) (fun _ => 0) s₀ (SubsetConvFPRAS.extendBits bits) B).output = some z ∧
        0 ≤ z) ∧
      (SubsetConvFPRAS.run P (fun _ => 0) (fun _ => 0) s₀ (SubsetConvFPRAS.extendBits bits) B).work ≤ B
  /-- The output is a `(1 ± ε)`-approximation with probability at least `1 − δ`. -/
  good : (1 - δ) * 2 ^ B ≤ (SubsetConvFPRAS.tapeCount P (fun _ => 0) (fun _ => 0) s₀ B
    (fun st => ∃ z, st.output = some z ∧ (1 - ε) * Z ≤ z ∧ z ≤ (1 + ε) * Z) : ℝ)

/-- The FPAUS time bound `K (m + 1 + log 1/ε)^d`, for `poly(n, log 1/ε)` of Definition 2.13 (p.12). -/
noncomputable def timeS (K d m : ℕ) (ε : ℝ) : ℕ :=
  ⌈(K : ℝ) * ((m : ℝ) + 1 + Real.log ε⁻¹) ^ d⌉₊

/-- The FPRAS time bound `K (m + 1 + 1/ε + log 1/δ)^d`, for `poly(n, 1/ε, log 1/δ)` of Definition 2.12 (p.12). -/
noncomputable def timeC (K d m : ℕ) (ε δ : ℝ) : ℕ :=
  ⌈(K : ℝ) * ((m : ℝ) + 1 + ε⁻¹ + Real.log δ⁻¹) ^ d⌉₊

/-- The input of the programs of Theorem 1.4: integer memory `graphInts` (`m`, `Δ`, the sorted adjacency lists), empty bitmaps,
and real memory holding the list `reals`.

**Formalization Note.** The machine is the published unit-cost real RAM with fair coins (`SubsetConvFPRAS.Machine`), with both
value oracles `0`. The paper names no model. Here `λ, ε, δ` are real inputs of unit cost, and the language has no floor and no
real-to-integer cast. -/
noncomputable def initGraph (m Δ : ℕ) (G : SimpleGraph (Vertex m)) (reals : List ℝ) :
    SubsetConvFPRAS.State (m + m) :=
  SubsetConvFPRAS.mkInit (LowTempGlauber.graphInts m Δ G) (fun _ => ∅)
    (SubsetConvFPRAS.realsOf reals (fun _ : Fin 0 => 0))

/-- The input of the slice programs of Lemmas 6.1, 6.2 and Corollaries 6.6, 6.7: `graphInts`, with two further parameters `a, b`
in integer cells `-1, -2`; the pinned set `τ` in bitmap `0`; real memory holding the list `reals`. -/
noncomputable def initSlice (m Δ : ℕ) (G : SimpleGraph (Vertex m)) (a b : ℕ) (τ : Finset (Vertex m))
    (reals : List ℝ) : SubsetConvFPRAS.State (m + m) :=
  SubsetConvFPRAS.mkInit
    (fun i => if i = -1 then (a : ℤ) else if i = -2 then (b : ℤ) else LowTempGlauber.graphInts m Δ G i)
    (SubsetConvFPRAS.bitmapsOf [toBits τ])
    (SubsetConvFPRAS.realsOf reals (fun _ : Fin 0 => 0))

end HardcoreSlices


