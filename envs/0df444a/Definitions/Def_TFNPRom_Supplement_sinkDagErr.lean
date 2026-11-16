-- Prove2me | Definitions.Def_TFNPRom_Supplement_sinkDagErr
-- name    : TFNPRom_Supplement_sinkDagErr
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T04:27:11.703993+00:00
-- url     : https://prove2.me/theorems/f8fe0dca-f362-4f91-a885-3713adc48983
-- title:
--   Error of a public reduction to Sink of Dag
-- statement:
--   For a public reduction $(\omega,f,g)$ with $\omega(u)=u$ from $F$ to Sink of Dag, the **error** is
--
--   $$\mathrm{err}(\omega,f,g)=\Pr_{u\sim\Sigma^n}\big[\exists o:\ o\text{ is a Sink-of-Dag solution of }f(u)\ \wedge\ (u,g_o(u))\notin F\big].$$
--
--   A reduction with error $0$ is a standard black-box reduction; a public reduction is required to have error at most $1/3$.
--
--   **Formalization Note** The probability is the published `PunctSketch.coinProb`, the uniform counting measure on $\Sigma^n$.
-- source:
--   Fleming, Göös, Guan, Korten, Mitropolsky, Pitassi, Riazanov, Sokolov, Yang, Yuan, TFNP in the Random Oracle Model, arXiv:2611.05308 (held version, sha256 e11eb9c3…9bb), §5, p.28

import Mathlib
import Definitions.Def_PunctSketch_coinProb
import Definitions.Def_TFNPRom_Supplement_sinkDagSol
import Definitions.Def_TFNPRom_Supplement_SinkDagReduction

namespace TFNPRom.Supplement

/-- The error of a public reduction to Sink of Dag with `ω(u) = u` (Fleming et al., *TFNP in the Random Oracle Model*, arXiv:2611.05308 (held version, sha256 e11eb9c3…9bb), §5, p.28):
`err(ω, f, g) = Pr_{u ∼ Σ^t}[∃ o ∈ O′ : (f(u), o) ∈ R_m ∧ (ω(u), g_o(u)) ∉ F_n]`, the probability
over a uniform input `u` that some Sink-of-Dag solution `o` of the target instance `f(u)` decodes to
a candidate `g_o(u)` that is not a solution of `u`.

**Formalization Note** The probability is the published `PunctSketch.coinProb` (uniform counting
measure on `ι → α`). -/
noncomputable def sinkDagErr {ι α O : Type} [Fintype ι] [DecidableEq ι] [Fintype α]
    (rel : (ι → α) → O → Prop) {K d : ℕ} (R : SinkDagReduction ι α O K d) : ℝ :=
  PunctSketch.coinProb (fun u : ι → α =>
    ∃ v : Fin K × Fin K, sinkDagSol K (fun i j => (R.f i j).eval u) v ∧
      ¬ rel u ((R.g v.1 v.2).eval u))

end TFNPRom.Supplement


