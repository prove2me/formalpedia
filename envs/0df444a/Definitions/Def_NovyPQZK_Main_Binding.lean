-- Prove2me | Definitions.Def_NovyPQZK_Main_Binding
-- name    : NovyPQZK_Main_Binding
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-11T05:36:27.928876+00:00
-- url     : https://prove2.me/theorems/0bcc965d-f820-410c-9d65-618ae115d11e
-- title:
--   Open-Both, Sum-Binding and Collapse-Binding experiments and the three binding notions (Experiments 5–7, Definitions 8, 9, 11)
-- statement:
--   The adversarial sender is a family $S = \{S_n\}$ of quantum parties. In each experiment it first runs the committing phase as the sender against the honest $R_{com}(\mathrm{Public}_n)$ (receiving $\mathrm{Public}_n$ with the first message) and keeps its quantum memory; let $c = (\mathrm{Comm},\mathrm{Priv}_R,\mathrm{Public}_n)$.
--
--   - **Open-Both** (Exp. 5): $S_n$ outputs $(u_0,u_1)$; success iff $R_{open}(0,u_0,c)\lor R_{open}(0,u_1,c)$ and $R_{open}(1,u_0,c)\lor R_{open}(1,u_1,c)$.
--   - **Sum-Binding** (Exp. 6): a uniform bit $b$ is announced, $S_n$ outputs $u$; success iff $R_{open}(b,u,c)$.
--   - **Collapse-Binding** (Exp. 7): with the adversary's registers $S$, $M$ (message) and $U$ (opening), the projective measurement $V^c = \{V^c_1, 1-V^c_1\}$,
--   $$V^c_1 = \sum_{(m,u):\,m\in M,\ R_{open}(m,u,c)=1}|m,u\rangle\langle m,u|_{MU}\otimes 1_S,$$
--   is applied with outcome $v$; a uniform bit $b$ is picked; if $b = 1$ and $v = 1$, $M$ is measured in the computational basis; then $S_n$ outputs $b'$; success iff $b = b'$.
--
--   $\Pi$ is post-quantum computational **open-once binding** if every QPT $S$ has $\Pr[\text{Open-Both}] \le \mathrm{negl}(n)$; **sum-binding** if $\Pr[\text{Sum-Binding}]\le \tfrac12+\mathrm{negl}(n)$; **collapse-binding** if $\Pr[\text{Collapse-Binding}]\le\tfrac12+\mathrm{negl}(n)$ for every QPT $S$ and every choice of disjoint registers $M,U$.
--
--   **Formalization Note** "$\le\mathrm{negl}(n)$" is $\exists\mu$ negligible with the bound $\le \mu(n)$ for every $n$. Outputs of arbitrary length are decoded from the measured wires with `unpack`.
-- source:
--   Dupuis, Ligez, Medhioub, Salvail, Thibodeau, Post-Quantum Perfect Zero-Knowledge Arguments for NP From Any One-Way Permutation, arXiv:2610.33185 (sha256 857d8563…3257f), §3.4 pp. 23–25, Experiments 5, 6, 7 and Definitions 8, 9, 11

import Mathlib
import Definitions.Def_CompNonlocal_Negligible
import Definitions.Def_NovyPQZK_Main_Quantum
import Definitions.Def_NovyPQZK_Main_Commitment

namespace NovyPQZK.Main

/-!
Dupuis, Ligez, Medhioub, Salvail, Thibodeau, arXiv:2610.33185 (sha256 857d8563…3257f), §3.4,
pp. 23–25: the binding experiments against a quantum sender and the three binding notions.

The adversarial sender at security parameter `n` is a quantum party `S n` (a `QStrategy`). In the
committing phase it plays the sender against the honest `R_com` (input `Public_n`, which `S` receives
together with `R_com`'s first message), for `rounds n` steps; it keeps its quantum memory. The
experiment then gives it further steps. A string of arbitrary length output through a fixed set of
wires is decoded with `unpack`/`decodeOne`, so every opening can be output.
-/

open QAlgorithms
open scoped Matrix

/-- The messages written into the adversarial sender: `R_com`'s messages (with `Public_n` at step
`0`) during the committing phase, then `extra` (from the outcomes so far). -/
def expMsg (Cm : CommitmentScheme) (n : ℕ) (c : CoinSpace (Cm.receiver.coins (Cm.setup n)))
    (extra : List Bits → Bits) (done : List Bits) : Bits :=
  if done.length < Cm.rounds n then msgFor (Cm.setup n) (Cm.receiver.msg (Cm.setup n) c) done
  else extra done

/-- `Comm`: the transcript of the committing phase with receiver coins `c`, given the sender's
messages `ss` of its `rounds n` steps. -/
def commTranscript (Cm : CommitmentScheme) (n : ℕ) (c : CoinSpace (Cm.receiver.coins (Cm.setup n)))
    (ss : List Bits) : List Bits :=
  interleave ((List.range (Cm.rounds n)).map fun j => Cm.receiver.msg (Cm.setup n) c (ss.take j)) ss

/-- Experiment 5 (p. 23), `Pr[Open-Both_{Π,S}(n) = 1]`: after the committing phase `S` outputs
`(u₀, u₁)` (its next step, decoded from `pack [u₀, u₁]`); success iff `0` and `1` are both opened
by `u₀` or `u₁`. -/
noncomputable def openBothProb (Cm : CommitmentScheme) (S : QStrategy) (n : ℕ) : ℝ :=
  avgOver (CoinSpace (Cm.receiver.coins (Cm.setup n))) fun c =>
    ∑ o : S.Outs (Cm.rounds n + 1),
      let os := QStrategy.outList o
      let comm := commTranscript Cm n c (os.take (Cm.rounds n))
      let s := os.getD (Cm.rounds n) []
      let u0 := (unpack s).getD 0 []
      let u1 := (unpack s).getD 1 []
      let ok : Bool → Bool := fun b =>
        Cm.ropen [b] u0 comm (encCoins c) (Cm.setup n) || Cm.ropen [b] u1 comm (encCoins c) (Cm.setup n)
      if (ok false && ok true) = true then
        (S.run (expMsg Cm n c (fun _ => [])) (zeroDM S.inQ) os).trace.re
      else 0

/-- Experiment 6 (p. 24), `Pr[Sum-Binding_{Π,S}(n) = 1]`: after the committing phase a uniform bit
`b` is announced to `S` (written in at its next step), `S` outputs `u`; success iff `R_open(b, u, …)`. -/
noncomputable def sumBindingProb (Cm : CommitmentScheme) (S : QStrategy) (n : ℕ) : ℝ :=
  avgOver Bool fun b =>
    avgOver (CoinSpace (Cm.receiver.coins (Cm.setup n))) fun c =>
      ∑ o : S.Outs (Cm.rounds n + 1),
        let os := QStrategy.outList o
        let comm := commTranscript Cm n c (os.take (Cm.rounds n))
        let u := decodeOne (os.getD (Cm.rounds n) [])
        if Cm.ropen [b] u comm (encCoins c) (Cm.setup n) = true then
          (S.run (expMsg Cm n c (fun _ => [b])) (zeroDM S.inQ) os).trace.re
        else 0

/-- Experiment 7 (p. 25), `Pr[Collapse-Binding_{Π,S}(n) = 1]`, with the message register `M` on
the wires `mW` and the opening register `U` on the wires `uW` of `S`. After the committing phase
the verification measurement `V^c = {V^c₁, 1 − V^c₁}`,
`V^c₁ = Σ_{(m,u) : R_open(m,u,c) = 1} |m, u⟩⟨m, u|_{MU} ⊗ 1_S` (the sum over messages `m ∈ M`,
the contents of the message register), is applied; a uniform bit `b` is
picked; if `b = 1` and `v = 1` the register `M` is measured in the computational basis; then `S`
outputs `b'` (first wire measured at its next step); success iff `b = b'`. -/
noncomputable def collapseProb (Cm : CommitmentScheme) (S : QStrategy) (mW uW : List (Fin S.N))
    (n : ℕ) : ℝ :=
  avgOver (CoinSpace (Cm.receiver.coins (Cm.setup n))) fun c =>
    ∑ o : S.Outs (Cm.rounds n),
      let os := QStrategy.outList o
      let comm := commTranscript Cm n c os
      let ρ := S.run (expMsg Cm n c (fun _ => [])) (zeroDM S.inQ) os
      let V1 : Matrix (Qubits S.N) (Qubits S.N) ℂ :=
        Matrix.diagonal fun z =>
          @ite ℂ (readWires mW z ∈ Cm.msgSpace n ∧
              Cm.ropen (readWires mW z) (decodeOne (readWires uW z)) comm (encCoins c)
                (Cm.setup n) = true) (Classical.propDecidable _) 1 0
      let V0 := 1 - V1
      let τ0 := V1 * ρ * V1 + V0 * ρ * V0
      let τ1 := (∑ m : Qubits mW.length,
          outcomeProj mW (List.ofFn m) * (V1 * ρ * V1) * outcomeProj mW (List.ofFn m)) + V0 * ρ * V0
      let U := (S.stepAt (Cm.rounds n)).op []
      let Q : Bool → Matrix (Qubits S.N) (Qubits S.N) ℂ := fun b =>
        diagProj (fun z => (readWires (S.stepAt (Cm.rounds n)).outW z).headD false) b
      (1 / 2 : ℝ) * ((Q false * U * τ0 * Uᴴ).trace.re + (Q true * U * τ1 * Uᴴ).trace.re)

/-- Definition 8 (p. 24): post-quantum computational open-once binding. -/
def CommitmentScheme.IsOpenOnceBinding (Cm : CommitmentScheme) : Prop :=
  ∀ S : ℕ → QStrategy, IsQPT S →
    ∃ μ : ℕ → ℝ, CompNonlocal.Negligible μ ∧ ∀ n, openBothProb Cm (S n) n ≤ μ n

/-- Definition 9 (p. 24): post-quantum computational sum-binding. -/
def CommitmentScheme.IsSumBinding (Cm : CommitmentScheme) : Prop :=
  ∀ S : ℕ → QStrategy, IsQPT S →
    ∃ μ : ℕ → ℝ, CompNonlocal.Negligible μ ∧ ∀ n, sumBindingProb Cm (S n) n ≤ 1 / 2 + μ n

/-- Definition 11 (p. 25): post-quantum computational collapse-binding; `M` and `U` are any two
disjoint registers of the adversary. -/
def CommitmentScheme.IsCollapseBinding (Cm : CommitmentScheme) : Prop :=
  ∀ (S : ℕ → QStrategy) (mW uW : (n : ℕ) → List (Fin (S n).N)), IsQPT S →
    (∀ n, (mW n).Nodup ∧ (uW n).Nodup ∧ ∀ a ∈ mW n, a ∉ uW n) →
    ∃ μ : ℕ → ℝ, CompNonlocal.Negligible μ ∧ ∀ n, collapseProb Cm (S n) (mW n) (uW n) n ≤ 1 / 2 + μ n

end NovyPQZK.Main


