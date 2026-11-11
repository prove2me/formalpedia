-- Prove2me | Definitions.Def_TDHamSim_QueryOptimal_Resources
-- name    : TDHamSim_QueryOptimal_Resources
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-10T14:20:48.584411+00:00
-- url     : https://prove2.me/theorems/d9d0415c-e7f6-4fb8-a0a3-ebcaa70b244c
-- title:
--   Circuit implementation and clean simulation predicates
-- statement:
--   The wire set is the disjoint union of system wires and auxiliary wires. A circuit implementation is equality of its matrix action with the specified operator on every input vector when the work wires start in zero; those work wires must return to zero. Additional gates are ordinary circuit gates, computed as size minus queries in the referenced oracle-circuit model.
--
--   $$\|U_{\rm sim}(|0\rangle\otimes\psi)-|0\rangle\otimes U\psi\|\le\varepsilon\qquad(\|\psi\|=1).$$
--
--   The simulation predicate measures error on the full output vector. Its auxiliary wires are not discarded or projected away. Controlled operators and the two resource scale functions are explicit, rather than resource certificates.
-- source:
--   Boyang Chen, Minbo Gao, Zhengfeng Ji, Tongyang Li, Xinzhao Wang, Shuo Zhou, STOC 2027 submission #383 (October 2026), Propositions 4, 10, 11 and Theorem 13, pp.16,28,31,33. https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/383.pdf

import Definitions.Def_TDHamSim_QueryOptimal_Dyadic

namespace TDHamSim.QueryOptimal

abbrev Wires (d k : ℕ) := Fin d ⊕ Fin k
noncomputable def wireZero (d k : ℕ) (v : Ket (Bits d)) : Ket (Wires d k → Bool) :=
  WithLp.toLp 2 (fun x => if (fun i => x (Sum.inr i)) = (fun _ => false)
    then v (fun i => x (Sum.inl i)) else 0)

/-- An actual circuit action on every input vector, with all work wires returned exactly to zero. -/
def Implements {d k t : ℕ} (c : ConstDepthUnitary.OCircuit (Wires d k) t)
    (O : Mat (Bits t)) (U : Mat (Bits d)) : Prop :=
  ∀ v : Ket (Bits d), act (ConstDepthUnitary.OCircuit.matrix O c) (wireZero d k v) =
    wireZero d k (act U v)

noncomputable def ctrl {d : ℕ} (U : Mat (Bits d)) : Mat (Bits (1+d)) :=
  fun x y => if x ⟨0, by omega⟩ = y ⟨0, by omega⟩ then
    if x ⟨0, by omega⟩ then U (slice 1 d (by omega) x) (slice 1 d (by omega) y)
    else if x = y then 1 else 0
  else 0

noncomputable def extraGates {W : Type} [DecidableEq W] {t : ℕ}
    (c : ConstDepthUnitary.OCircuit W t) : ℕ :=
  ConstDepthUnitary.OCircuit.size c - ConstDepthUnitary.OCircuit.queries c

/-- Simulation on the entire output state, including every auxiliary wire. -/
def Simulates {n k t : ℕ} (c : ConstDepthUnitary.OCircuit (Wires n k) t)
    (O : Mat (Bits t)) (U : Mat (Bits n)) (ε : ℝ) : Prop :=
  ∀ v : Ket (Bits n), ‖v‖ = 1 →
    ‖act (ConstDepthUnitary.OCircuit.matrix O c) (wireZero n k v) - wireZero n k (act U v)‖ ≤ ε

end TDHamSim.QueryOptimal


