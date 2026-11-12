-- Prove2me | Definitions.Def_NovyPQZK_Main_SP
-- name    : NovyPQZK_Main_SP
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-11T05:38:27.774551+00:00
-- url     : https://prove2.me/theorems/b2c3e5e1-9430-43dc-b0ea-b988c14f6cba
-- title:
--   The adversary S_P of the soundness proof and its abort probability (steps (1)–(8))
-- statement:
--   Fix a bit commitment $\Pi$, a (possibly malicious) quantum prover $P$ and a graph $G$. The prover is $P = (P_{com}, c\text{-}P_0, c\text{-}P_1)$: $P_{com}$ runs the committing phase, and on challenge $ch$ it applies $c\text{-}P_{ch} = \sum_t |t\rangle\langle t|_T\otimes P_{ch,t}$ (controlled by the transcript $t$) and measures its registers $PA$ (the reply). $\mathrm{Ver\text{-}CH}_{ch} = (\Pi_{ch}, 1-\Pi_{ch})$ projects onto valid replies to $ch$, and $\mathrm{Ver\text{-}COM} = (\Gamma, 1-\Gamma)$ onto valid openings of all of $A$ (2), each opened entry $A(i,j)$ being a bit (register $M_{i,j}$ holds a bit, p. 45).
--
--   $S_P(1^n)$: (1) pick $(c,d)\in_R I_\eta$; (2) run $P_{com}$ against the honest verifier, the position $(c,d)$ being played by the real $R_{com}$; (3) apply $c\text{-}P_0$ and measure $\mathrm{Ver\text{-}COM}$; (4) measure register $A$ in the computational basis; (5) measure $\mathrm{Ver\text{-}CH}_0$, abort on failure; (6) apply $c\text{-}P_1(c\text{-}P_0)^*$ and measure $\mathrm{Ver\text{-}CH}_1$, abort on failure; (7)–(8) measure $PA$ and return the two openings at $(c,d)$.
--
--   `spAbortProb` is $\Pr[\perp\leftarrow S_P(1^n)]$, i.e. one minus the trace of the state that passes steps (5) and (6).
--
--   **Formalization Note** The transcript is classical and summed over. $c\text{-}P_{ch}$ is the prover's step at round $\mathrm{rounds}(n)$ with $ch$ written into its wires; $PA$ are the wires it measures; measuring $A$ measures the opening part $(m,u)$ of a challenge-$0$ reply. Because the real $R_{com}$ in step (2) is honest with uniform coins, every register has the same joint distribution for every $(c,d)$, so the abort probability is computed with the honest verifier's coins.
-- source:
--   Dupuis, Ligez, Medhioub, Salvail, Thibodeau, Post-Quantum Perfect Zero-Knowledge Arguments for NP From Any One-Way Permutation, arXiv:2610.33185 (sha256 857d8563…3257f), §7.1 pp. 45–47, prover model, measurements, (2) and the adversary S_P

import Mathlib
import Definitions.Def_NovyPQZK_Main_HamCycle

namespace NovyPQZK.Main

/-!
Dupuis, Ligez, Medhioub, Salvail, Thibodeau, arXiv:2610.33185 (sha256 857d8563…3257f), §7.1,
pp. 45–47: the prover model `P = (P_com, c-P₀, c-P₁)`, the measurements `Ver-CH_ch` and `Ver-COM`,
and the abort probability of the adversary `S_P` (steps (1)–(8)).

A (possibly malicious) prover at one `n` and `x` is a quantum party `Ps`. Its first `rounds n`
steps are `P_com`; its step `rounds n` receives the challenge `ch` (written into its wires) and
applies its circuit: this is `c-P_ch = U · X^{ch}`, controlled by the classical transcript held by
the experiment (the prover's state is the cq-state `Σ_t |t⟩⟨t| ⊗ ρ_t`, the sum over transcripts
below). Registers `P` and `A` are the wires `outW` of that step: the response.

* `Ver-CH_ch = (Π_ch, 1 − Π_ch)`: `Π_ch` projects onto the responses the honest verifier accepts
  for challenge `ch`, given the transcript.
* `Ver-COM = (Γ, 1 − Γ)` (2): `Γ` projects onto responses whose opening part `(m, u)` (the last
  two components of a challenge-`0` response `pack [σ, m, u]`) is a valid opening of all of `A`,
  each opened entry being a bit (register `M_{i,j}` holds the bit `A(i, j)`, p. 45).
* Measuring register `A` in the computational basis: measuring the opening part `(m, u)`.

`S_P`: (1) pick `(c, d) ∈_R I_η`; (2) run `P_com` against the honest verifier, the position
`(c, d)` being played by the real `R_com`; (3) apply `c-P₀`, measure `Ver-COM`; (4) measure `A`;
(5) measure `Ver-CH₀`, abort on failure; (6) apply `c-P₁ (c-P₀)*`, measure `Ver-CH₁`, abort on
failure; (7)–(8) measure `PA` and return two openings. Since the real `R_com` is honest with
independent uniform coins, the joint distribution of all registers in steps (2)–(6) is that of `P`
against the honest verifier, for every `(c, d)`; the abort probability below is computed with the
verifier's coins.
-/

open QAlgorithms
open scoped Matrix

/-- `Pr[S_P(1^n) does not abort]` for the prover `Ps` on the graph `x`. -/
noncomputable def spNotAbortProb (Cm : CommitmentScheme) (Ps : QStrategy) (n : ℕ) (x : Bits) : ℝ :=
  match decodeGraph x with
  | none => 0
  | some (η, e) =>
      let V := (protocol18 Cm).verifier
      let inV := commonInput n x
      let K := Cm.rounds n
      let mR := ((parRecv Cm.receiver).coins (p18Pub Cm n η)).length
      avgOver (CoinSpace (V.coins inV)) fun c =>
        ∑ o : Ps.Outs K,
          let os := QStrategy.outList o
          let cR := (List.ofFn fun i => (c i).val).take mR
          let ρ := Ps.run (msgFor inV (V.msg inV c)) (zeroDM Ps.inQ) os
          let s := Ps.stepAt K
          let U0 := s.op [false]
          let U1 := s.op [true]
          let resp : Qubits Ps.N → Bits := fun z => readWires s.outW z
          let PiCh : Bool → Matrix (Qubits Ps.N) (Qubits Ps.N) ℂ := fun ch =>
            diagProj (fun z => p18Check Cm n η e cR os ch (resp z)) true
          let openPart : Qubits Ps.N → List Bits := fun z => (unpack (resp z)).drop 1
          let Γ : Matrix (Qubits Ps.N) (Qubits Ps.N) ℂ :=
            diagProj (fun z => match openPart z with
              | [mAll, uAll] =>
                  (unpack mAll).all (fun m => decide (m = [false] ∨ m = [true])) &&
                  parRopen Cm mAll uAll
                    (interleave ((List.range K).map fun i =>
                      (parRecv Cm.receiver).next
                        (pack (p18Pub Cm n η :: pack (cR.map natToBits) :: os.take i))) os)
                    (pack (cR.map natToBits)) (p18Pub Cm n η)
              | _ => false) true
          let ρ1 := U0 * ρ * U0ᴴ
          let ρ2 := Γ * ρ1 * Γ + (1 - Γ) * ρ1 * (1 - Γ)
          let ρ3 := ∑ a ∈ Finset.univ.image openPart, diagProj openPart a * ρ2 * diagProj openPart a
          let ρ4 := PiCh false * ρ3 * PiCh false
          let W := U1 * U0ᴴ
          let ρ6 := PiCh true * (W * ρ4 * Wᴴ) * PiCh true
          ρ6.trace.re

/-- `Pr[⊥ ← S_P(1^n)]`. -/
noncomputable def spAbortProb (Cm : CommitmentScheme) (Ps : QStrategy) (n : ℕ) (x : Bits) : ℝ :=
  1 - spNotAbortProb Cm Ps n x

end NovyPQZK.Main


