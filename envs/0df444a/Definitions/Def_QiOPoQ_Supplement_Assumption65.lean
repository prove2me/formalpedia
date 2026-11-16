-- Prove2me | Definitions.Def_QiOPoQ_Supplement_Assumption65
-- name    : QiOPoQ_Supplement_Assumption65
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T05:10:24.993393+00:00
-- url     : https://prove2.me/theorems/b6ba0772-3d6a-4693-86d8-78f153d7a4ae
-- title:
--   Assumption 6.5 (stability of the reference distributions)
-- statement:
--   For given RIO, Encode, $s$, $N$: for every two same-shape polynomial-size families of ancilla-free circuits $C_0,C_1$ of width $n(\lambda)\ge\lambda$ (polynomially bounded) and gate count $m(\lambda)\ge1$ whose channels have negligible diamond distance, their reference distributions (Definition 6.4) are computationally indistinguishable against non-uniform QPT distinguishers.
-- source:
--   Gheorghiu, Gupte, Havlíček, Liu, Verifiable Quantum Advantage and Computation via Quantum Circuit Obfuscation, arXiv:2609.40289 (sha256 fe2f9210…), Assumption 6.5, p.32

import Mathlib
import Definitions.Def_QAdvFew_PoQOracle_Negligible
import Definitions.Def_QiOPoQ_diamond
import Definitions.Def_QiOPoQ_Supplement_NUQPT
import Definitions.Def_QiOPoQ_Supplement_Placement
import Definitions.Def_QMAvsQCMAH_PolyBounded
import Definitions.Def_QiOPoQ_Supplement_PolyBounded2
import Definitions.Def_QiOPoQ_Supplement_refExpect

set_option autoImplicit false

namespace QiOPoQ.Supplement

open QAdvFew.PoQOracle QAlgorithms.Complexity

/-- **Assumption 6.5 (Stability of the reference distributions).** Gheorghiu, Gupte, Havlíček,
Liu, *Verifiable Quantum Advantage and Computation via Quantum Circuit Obfuscation*,
arXiv:2609.40289 (sha256 fe2f9210…), Assumption 6.5, p.32: "Let C0, C1 be any same-shape
polynomial-size ancilla-free circuit families of width n = n(λ) ≥ λ and gate count m = m(λ) ≥ 1,
whose channels have negligible diamond distance. We assume that their reference distributions
defined above are computationally indistinguishable against nonuniform QPT distinguishers."

For the given `RIO, Encode, s, N` (Definition 6.4, `refExpect`): for every polynomially bounded
width `n(λ) ≥ λ` and every two polynomial-size families of ancilla-free `n(λ)`-qubit circuits with
equal gate counts `≥ 1` (so equal shapes) and negligible diamond distance, every non-uniform QPT
distinguisher has negligible advantage between their reference distributions. -/
def Assumption65 (G : GateSet) (RIO Enc : UPPT) (s : ℕ → ℕ → ℕ) (N : ℕ → ℕ → ℕ → ℕ) : Prop :=
  ∀ nw : ℕ → ℕ, QMAvsQCMAH.PolyBounded nw → (∀ l, l ≤ nw l) →
    ∀ C0 C1 : (l : ℕ) → List (Placement G (nw l)), QMAvsQCMAH.PolyBounded (fun l => (C0 l).length) →
    (∀ l, (C0 l).length = (C1 l).length) → (∀ l, 1 ≤ (C0 l).length) →
    (∃ μ : ℕ → ℝ, Negligible μ ∧ ∀ l,
      diamond (chan (afCirc (nw l) (C0 l))) (chan (afCirc (nw l) (C1 l))) ≤ μ l) →
    ∀ D : NUQPT, ∃ ν : ℕ → ℝ, Negligible ν ∧ ∀ l,
      |refExpect G RIO Enc s N l (nw l) (C0 l) (D.acc G l) -
        refExpect G RIO Enc s N l (nw l) (C1 l) (D.acc G l)| ≤ ν l

end QiOPoQ.Supplement


