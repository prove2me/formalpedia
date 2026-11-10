-- Prove2me | Definitions.Def_ObfEF_Incremental_IncrementalChange
-- name    : ObfEF_Incremental_IncrementalChange
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-10T04:56:00.191334+00:00
-- url     : https://prove2.me/theorems/f0c0c78d-603e-4f94-8247-132e126cce9f
-- title:
--   Incremental changes (S, R, Γ) and their support (Definition 3.1)
-- statement:
--   Let $D$ and $D'$ be circuits with the same wires and the same input wires $l_j,r_j$ of every gate $j$, in which gate $j$ computes $f_j$ and $f'_j$ respectively. An **incremental change** from $D$ to $D'$ (Definition 3.1) is a triple $(S,R,\Gamma)$ of a subcircuit $S$, a set $R\subseteq\mathrm{inp}(S)$, and circuits $\Gamma=(\Gamma_o,\Gamma'_o)_o$ over $B$, one pair for each output wire $o$ of a gate of $S$, with inputs indexed by $R_o$, such that
--
--   1. every gate $j\notin S$ satisfies $f_j=f'_j$;
--   2. every output wire $o$ of a gate of $S$ and every $\xi\in\{0,1\}^{\mathrm{inp}(S)}$ satisfy
--   $$o(\xi)=\Gamma_o(\xi|_{R_o})\ \text{in } D,\qquad o(\xi)=\Gamma'_o(\xi|_{R_o})\ \text{in } D';$$
--   3. every $o\in\mathrm{out}(S)$ satisfies $\Gamma_o=\Gamma'_o$.
--
--   The set $R$ is the **support** of the change. The number of gates $|S|$, the support size $|R|$ and the sizes $|\Gamma_o|,|\Gamma'_o|$ (Definition 2.1) are the three quantities the paper bounds.
--
--   Taking $R=\mathrm{inp}(S)$ recovers δ-equivalence (Lemma 3.2); the point of the definition is that every internal wire value of either version of $S$ is described by a small circuit reading only the few support wires that reach it, which is what the gate-by-gate obfuscation hybrids need.
--
--   **Formalization Note.** `IncrementalChange W f f'` is a structure over one `Wiring W`. The describing circuits are indexed by the gate `j` whose output wire is $o=il+j$, have one output, and have inputs indexed by `W.Ro S R j`; only those with `j ∈ S` are constrained. A boundary assignment is a total `ξ : ℕ → Bool`.
-- source:
--   Abram, Datta, Dutta, Roy, Obfuscation via Proofs of Equivalence and Polynomial-Time Reductions to Falsifiable Assumptions, STOC 2027 submission (manuscript sha256 f9518747…), p. 45, Definition 3.1

import Mathlib
import Definitions.Def_ObfEF_Incremental_Circuit
import Definitions.Def_ObfEF_Incremental_GateList

/-!
# Incremental changes and their support (Definition 3.1)

Abram, Datta, Dutta, Roy, *Obfuscation via Proofs of Equivalence and Polynomial-Time Reductions to
Falsifiable Assumptions*, STOC 2027 submission (manuscript sha256 f9518747…), p. 45,
Definition 3.1.

`D` and `D'` have the same wires and the same input wires `l_j, r_j` of every gate: they are two
gate-function maps `f`, `f'` over one `Wiring`. The describing circuits `Γ_o, Γ'_o` are circuits
over `B` (Definition 2.1) with one output whose inputs are indexed by `R_o`; they are indexed by
the gate `j` whose output wire is `o = il + j` (only those with `j ∈ S` are constrained).
-/

namespace ObfEF.Incremental

/-- An incremental change `(S, R, Γ)` from `D` (gate functions `f`) to `D'` (gate functions `f'`)
over the wiring `W`. -/
structure IncrementalChange (W : Wiring) (f f' : Fin W.n → Bool → Bool → Bool) where
  /-- The changed subcircuit `S` (a set of gates). -/
  S : Finset (Fin W.n)
  /-- The support `R ⊆ inp(S)`. -/
  R : Finset ℕ
  R_subset : R ⊆ W.inp S
  /-- `Γ_o` for the output wire `o` of gate `j`, a circuit with inputs indexed by `R_o`. -/
  Γ : (j : Fin W.n) → Circuit (W.Ro S R j) 1
  /-- `Γ'_o` for the output wire `o` of gate `j`. -/
  Γ' : (j : Fin W.n) → Circuit (W.Ro S R j) 1
  /-- (1) every gate outside `S` computes the same function in `D` and `D'`. -/
  outside : ∀ j : Fin W.n, j ∉ S → f j = f' j
  /-- (2) for every output wire `o` of a gate of `S` and every `ξ ∈ {0,1}^{inp(S)}`,
  `o(ξ) = Γ_o(ξ|R_o)` in `D` and `o(ξ) = Γ'_o(ξ|R_o)` in `D'`. -/
  describes : ∀ j ∈ S, ∀ ξ : ℕ → Bool,
    W.subVal f S ξ (W.gateWire j) = (Γ j).eval (fun w => ξ w.1) 0 ∧
    W.subVal f' S ξ (W.gateWire j) = (Γ' j).eval (fun w => ξ w.1) 0
  /-- (3) `Γ_o = Γ'_o` for every `o ∈ out(S)`. -/
  boundary : ∀ j ∈ S, W.IsOutBoundary S (W.gateWire j) → Γ j = Γ' j

end ObfEF.Incremental


