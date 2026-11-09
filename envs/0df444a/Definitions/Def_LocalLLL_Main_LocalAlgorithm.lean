-- Prove2me | Definitions.Def_LocalLLL_Main_LocalAlgorithm
-- name    : LocalLLL_Main_LocalAlgorithm
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-08T10:51:50.241582+00:00
-- url     : https://prove2.me/theorems/a433f907-17b6-4e70-a5d4-5bdd95884c46
-- title:
--   Private-bit LOCAL programs and synchronous execution
-- statement:
--   A uniform LOCAL program has arbitrary state and message spaces, an initialization function of the node identifier, local input and private Boolean tape, a broadcast function, a transition from the current state and sender-identifier-indexed received messages, and an output function. Execution is synchronous: at each round the transition receives exactly the broadcasts of graph neighbors. The same functions run at every node.
--
--   The randomness is independent fair bits, with law
--
--   $$\mathsf{Tapes}_V=\bigotimes_{v\in V}\bigotimes_{j\in\mathbb N}\operatorname{Bernoulli}(1/2).$$
--
--   These definitions measure communication rounds without imposing computational or bandwidth limits. A broadcast can carry a dictionary of recipient-specific messages. The auxiliary function $\ell(n)=\log\log(n+16)$ makes the complexity expressions positive for every permitted $n\ge1$.
-- source:
--   Maxime Flin, Mohsen Ghaffari, Magnus M. Halldorsson, Yannic Maus, Alexandre Nolin, STOC 2027 submission #475 (October 2026), §1 LOCAL model, p. 1 (PDF 2); §2 high-probability convention, p. 2 (PDF 3); source.pdf, SHA-256 3dde5fa7cf9bc55426bf80a9dd9632c790e2ea3d0fe4a19b924d1802d48000a2.

import Mathlib

noncomputable section

namespace LocalLLL.Main

/-- Uniform private-tape LOCAL program. Only the initialization sees the local input and tape.
Messages have no size restriction; a broadcast may contain a dictionary for all recipients. -/
structure LocalAlg (I O : Type) where
  State : Type
  Message : Type
  init : ℕ → I → (ℕ → Bool) → State
  send : State → Message
  step : State → (ℕ → Option Message) → State
  output : State → O

/-- Only messages from neighbors appear, keyed by their identifiers. -/
def runState {I O V : Type} (alg : LocalAlg I O) (G : SimpleGraph V)
    (id : V → ℕ) (input : V → I) (ω : V → ℕ → Bool) : ℕ → V → alg.State
  | 0, v => alg.init (id v) (input v) (ω v)
  | t + 1, v => alg.step (runState alg G id input ω t v) (fun key => by
      classical
      exact if h : ∃ u, G.Adj v u ∧ id u = key then
        some (alg.send (runState alg G id input ω t (Classical.choose h))) else none)

def run {I O V : Type} (alg : LocalAlg I O) (T : ℕ) (G : SimpleGraph V)
    (id : V → ℕ) (input : V → I) (ω : V → ℕ → Bool) : V → O :=
  fun v => alg.output (runState alg G id input ω T v)

def fairCoin : MeasureTheory.Measure Bool :=
  ProbabilityTheory.bernoulliMeasure false true ⟨1 / 2, by norm_num⟩

def tapes (V : Type) [Fintype V] : MeasureTheory.Measure (V → ℕ → Bool) :=
  MeasureTheory.Measure.pi (fun _ : V =>
    MeasureTheory.Measure.infinitePi (fun _ : ℕ => fairCoin))

/-- Padding makes the asymptotic expression positive even at n = 1. -/
def loglog (n : ℕ) : ℝ := Real.log (Real.log ((n : ℝ) + 16))
end LocalLLL.Main


