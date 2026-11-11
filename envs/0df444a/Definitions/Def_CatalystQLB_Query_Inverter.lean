-- Prove2me | Definitions.Def_CatalystQLB_Query_Inverter
-- name    : CatalystQLB_Query_Inverter
-- status  : Definition
-- author  : @iris
-- created : 2026-11-10T20:20:30.441606+00:00
-- url     : https://prove2.me/theorems/ae93db33-56cb-4520-af0a-079d06d58aa5
-- title:
--   Inverters for a random function and their success $\mathrm{succ}_{\mathrm{inv}}$
-- statement:
--   An **inverter** with $T$ queries receives a classical string $z\in\{0,1\}^\lambda$ and oracle access to $O_g$. On input $z$ it prepares a unit vector on $Q\otimes R\otimes W$ for a finite workspace $W$, applies unitaries $U^z_0,\dots,U^z_T$ interleaved with $T$ queries $O_g\otimes I_W$, measures everything in the computational basis, and returns a string or aborts ($\bot$), as a function of $z$ and the outcome. Its success is
--   $$\mathrm{succ}_{\mathrm{inv}}=\Pr_{g,x}\big[\mathcal I^g(g(x))=x\big],$$
--   with $g$ a uniformly random function and $x$ uniform; an abort is a failure.
--
--   The paper's proofs turn any circuit that solves the reversed problem into such an inverter, which is then bounded by the random-function inversion bound.
--
--   **Formalization Note** Built on the published `QAlgorithms.QueryAlg` (one per input $z$) and its `outputProb`. The workspace is unbounded, and the start vector, the unitaries and the output map may depend on $z$; randomness and intermediate measurements are purified into $W$. The inverter is never given $x$ or $O_f$.
-- source:
--   Arora, Chakraborty, Cojocaru, Saminathan, Singh, Computational Work Extraction: The Complexity of Catalysts, arXiv:2609.40323 (version of 2026-11-03, sha256 44854b3a…), §5.3, Lemma 75's proof, Step (2), pp.46–47 (PDF 49–50)

import Mathlib
import Definitions.Def_QAlgorithms_Defs_Query

namespace CatalystQLB.Query

open QAlgorithms

/-- An inverter for a random function with `T` queries (Arora, Chakraborty, Cojocaru, Saminathan, Singh, *Computational Work Extraction: The Complexity of Catalysts*, arXiv:2609.40323 (version of 2026-11-03), §5.3, Lemma 75's proof, p.46
(PDF 49): "The inversion algorithm `I` receives `z = g(x)` and has oracle access to `O_g`. … It
is not given `x` or access to the original oracle `O_f`"). For every classical input `z` it
runs a `T`-query algorithm `alg z` (`QAlgorithms.QueryAlg`: a unit start vector, unitaries
`U_0, …, U_T`, interleaved with `xorOracle g ⊗ I_W` on the register `(Q × R) × W`), measures the
whole register in the computational basis and returns `out z` of the outcome: a string, or
`none` (abort, the paper's `⊥`).

**Formalization Note** The workspace `W` is any finite type and is not bounded; the start
vector, the unitaries and the output map may depend on `z`. Randomness and intermediate
measurements (the paper's inverter samples `i` and `f` and runs the tests `{Π^⊥, Π}`) are
purified into `W`. -/
structure Inverter (n : ℕ) (W : Type) [Fintype W] [DecidableEq W] (T : ℕ) where
  /-- The query algorithm run on input `z`. -/
  alg : Qubits n → QueryAlg (Qubits n) (Qubits n) W T
  /-- The output read from the measurement outcome on input `z` (`none` = abort). -/
  out : Qubits n → (Qubits n × Qubits n) × W → Option (Qubits n)

/-- The inverter's success `succ_inv := Pr_{g,x,I}[I^g(g(x)) = x]` (arXiv:2609.40323, version of
2026-11-03, §5.3, p.46 (PDF 49)): the probability that, on input `z = g(x)` with oracle `O_g`,
it outputs `x`, averaged over a uniformly random `g : {0,1}^n → {0,1}^n` and a uniform `x`.

**Formalization Note** The plain sum divided by `|{0,1}^n → {0,1}^n| · 2^n`. An abort never
counts as success. -/
noncomputable def Inverter.invSuccess {n : ℕ} {W : Type} [Fintype W] [DecidableEq W] {T : ℕ}
    (I : Inverter n W T) : ℝ :=
  ((Fintype.card (Qubits n → Qubits n) : ℝ) * 2 ^ n)⁻¹ *
    ∑ g : Qubits n → Qubits n, ∑ x : Qubits n,
      (I.alg (g x)).outputProb (xorOracle g) (I.out (g x)) (some x)

end CatalystQLB.Query


