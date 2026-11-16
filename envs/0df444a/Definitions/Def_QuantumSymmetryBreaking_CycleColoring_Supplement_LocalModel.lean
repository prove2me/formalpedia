-- Prove2me | Definitions.Def_QuantumSymmetryBreaking_CycleColoring_Supplement_LocalModel
-- name    : QuantumSymmetryBreaking_CycleColoring_Supplement_LocalModel
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-15T21:05:37.82287+00:00
-- url     : https://prove2.me/theorems/ee9aed97-2110-4891-9351-c8b8bbe6dad0
-- title:
--   Operational quantum-LOCAL model on port-numbered cycles and paths
-- statement:
--   A node rule has positive finite memory and port-register dimensions, an initial density matrix, a completely positive trace-preserving local operation before each send, and a final POVM. Its only initial inputs are its own degree and identifier and the known size bound. The general channel and tensor-channel action are imported from the published Kraus-channel library.
--
--   A port-numbered network is a simple graph of maximum degree two, represented by an involution on active ports. Cycles have at least three vertices; paths include the one-vertex path. Initial states are independent products. Each round applies the tensor of the local channels and then permutes the port registers along edges. For output coloring c the law is the literal Born rule
--
--   $$p(c)=\operatorname{Re}\operatorname{Tr}\big[(\bigotimes_v P_{v,c(v)})\rho_{\mathrm{final}}\big].$$
--
--   Global success is the sum over all proper colorings. A single rule family is chosen before the network, port numbering, identifiers and actual size; the known bound may control finite resources. The identifier exponent is a known positive integer. Registers can store classical messages and measurement records. Padding unused registers to common dimensions at each bound changes no finite protocol.
--
--   This interface supports the exact one- and four-round statements without giving a node the graph or choosing an arbitrary global output law.
-- source:
--   Maxime Flin, Longcheng Li, Jukka Suomela, Quantum Advantage for Distributed Symmetry Breaking, STOC 2027 submission #863 (October 2026), §3 pp.10–11 (PDF 13–14), §6.1 pp.28–29 (PDF 31–32)

import Mathlib
import Definitions.Def_QAlgorithms_Defs_Channel
import Definitions.Def_QuantumCycleColoring_FourColor_CycleAlgorithm
import Definitions.Def_QuantumSymmetryBreaking_CycleColoring_FiniteRealization

set_option autoImplicit false

/-! Finite operational quantum-LOCAL model for maximum-degree-two networks.
Flin–Li–Suomela, STOC 2027 #863, §3 pp.10–11 and §6.1 pp.28–29.
All local dimensions may depend on the known size bound. Registers are padded to
common dimensions at that bound. A channel includes arbitrary local memory,
coherent classical control, and discarded ancillas; no initial shared entanglement.
-/
namespace QuantumSymmetryBreaking.CycleColoring.Supplement

open QuantumCycleColoring.FourColor

/-- A port-numbered simple graph, maximum degree two. Inactive slots are fixed
by the port involution; active ports are numbered 0,...,degree-1. -/
structure PortNetwork (m : ℕ) where
  degree : Fin m → Fin 3
  mate : Equiv.Perm (Fin m × Fin 2)
  involutive : Function.Involutive mate
  inactive : ∀ v p, (degree v).val ≤ p.val → mate (v,p) = (v,p)
  active : ∀ v p, p.val < (degree v).val → (mate (v,p)).1 ≠ v ∧
    (mate (v,p)).2.val < (degree (mate (v,p)).1).val
  simple : ∀ v p r, p.val < (degree v).val → r.val < (degree v).val →
    (mate (v,p)).1 = (mate (v,r)).1 → p = r

/-- Adjacency is determined by active port pairing, never by an orientation. -/
def PortNetwork.Adj {m : ℕ} (G : PortNetwork m) (u v : Fin m) : Prop :=
  ∃ p : Fin 2, p.val < (G.degree u).val ∧ (G.mate (u,p)).1 = v

/-- Every labelling of a simple undirected cycle of length at least three.
The witnessing order is unavailable to the local algorithm. -/
def PortNetwork.IsCycle {m : ℕ} (G : PortNetwork m) : Prop :=
  3 ≤ m ∧ ∃ order : Equiv.Perm (Fin m), ∀ u v : Fin m,
    G.Adj (order u) (order v) ↔
      u.val + 1 = v.val ∨ v.val + 1 = u.val ∨
      (u.val = 0 ∧ v.val + 1 = m) ∨ (v.val = 0 ∧ u.val + 1 = m)

/-- Nonempty finite paths, including the single-vertex path. -/
def PortNetwork.IsPath {m : ℕ} (G : PortNetwork m) : Prop :=
  1 ≤ m ∧ ∃ order : Equiv.Perm (Fin m), ∀ u v : Fin m,
    G.Adj (order u) (order v) ↔ u.val + 1 = v.val ∨ v.val + 1 = u.val

/-- Private memory and two separate outgoing/incoming port registers. -/
abbrev LocalBasis (D M : ℕ) := Fin D × (Fin 2 → Fin M)

/-- The only classical input available initially: own degree and identifier.
The known bound is an argument of the rule family, not a hidden graph input. -/
structure LocalView (n exponent : ℕ) where
  degree : Fin 3
  identifier : Fin (n ^ exponent)

/-- One node rule at a fixed known bound, palette and round budget. Channels
act before each send; final arbitrary local computation is absorbed into the POVM.
The general quantum channel is imported, not redefined. -/
structure LocalRule (n exponent q rounds : ℕ) where
  memoryDim : ℕ
  messageDim : ℕ
  memory_pos : 0 < memoryDim
  message_pos : 0 < messageDim
  initial : LocalView n exponent →
    Matrix (LocalBasis memoryDim messageDim) (LocalBasis memoryDim messageDim) ℂ
  initial_density : ∀ v, IsDensityMatrix (initial v)
  step : Fin rounds → LocalView n exponent →
    QAlgorithms.Superop (LocalBasis memoryDim messageDim) (LocalBasis memoryDim messageDim)
  step_channel : ∀ t v, QAlgorithms.IsChannel (step t v)
  measure : LocalView n exponent → Fin q →
    Matrix (LocalBasis memoryDim messageDim) (LocalBasis memoryDim messageDim) ℂ
  measure_povm : ∀ v, IsPOVM (measure v)

/-- A single algorithm family, chosen before the network and identifiers.
The identifier exponent is an external known constant, not chosen by the algorithm. -/
abbrev LocalAlgorithm (exponent q rounds : ℕ) := (n : ℕ) → LocalRule n exponent q rounds

/-- Each node learns its own degree and identifier, never the global port pairing. -/
def nodeView {m n exponent : ℕ} (G : PortNetwork m)
    (ids : Fin m → Fin (n ^ exponent)) (v : Fin m) : LocalView n exponent :=
  ⟨G.degree v, ids v⟩

/-- Tensor product of independently prepared local density matrices. -/
noncomputable def initialState {m n exponent q rounds : ℕ}
    (A : LocalRule n exponent q rounds) (G : PortNetwork m)
    (ids : Fin m → Fin (n ^ exponent)) :
    Matrix (Fin m → LocalBasis A.memoryDim A.messageDim)
      (Fin m → LocalBasis A.memoryDim A.messageDim) ℂ :=
  fun x y => ∏ v, A.initial (nodeView G ids v) (x v) (y v)

/-- Synchronous communication permutes only the port registers. Memory stays
at its node. Since mate is an involution, this is its own inverse on basis indices. -/
def routedIndex {m D M : ℕ} (G : PortNetwork m)
    (x : Fin m → LocalBasis D M) : Fin m → LocalBasis D M :=
  fun v => ((x v).1, fun p => (x (G.mate (v,p)).1).2 (G.mate (v,p)).2)

/-- State after t rounds (t beyond the budget is never used). Local channels
are tensored on the full state, retaining all entangled off-diagonal blocks,
then all port registers are transmitted simultaneously. -/
noncomputable def roundState {m n exponent q rounds : ℕ}
    (A : LocalRule n exponent q rounds) (G : PortNetwork m)
    (ids : Fin m → Fin (n ^ exponent)) : ℕ →
    Matrix (Fin m → LocalBasis A.memoryDim A.messageDim)
      (Fin m → LocalBasis A.memoryDim A.messageDim) ℂ
  | 0 => initialState A G ids
  | t + 1 => if h : t < rounds then
      let X := QAlgorithms.piSuperop (fun v => A.step ⟨t,h⟩ (nodeView G ids v))
        (roundState A G ids t)
      fun x y => X (routedIndex G x) (routedIndex G y)
    else roundState A G ids t

/-- Joint Born law: trace of the tensor of final local effects times the
operationally produced network state. It is not a freely chosen distribution. -/
noncomputable def localOutputProb {m n exponent q rounds : ℕ}
    (A : LocalRule n exponent q rounds) (G : PortNetwork m)
    (ids : Fin m → Fin (n ^ exponent)) (c : Fin m → Fin q) : ℝ :=
  let E : Matrix (Fin m → LocalBasis A.memoryDim A.messageDim)
      (Fin m → LocalBasis A.memoryDim A.messageDim) ℂ :=
    fun x y => ∏ v, A.measure (nodeView G ids v) (c v) (x v) (y v)
  (E * roundState A G ids rounds).trace.re

/-- Global proper-coloring probability, including every edge at once. -/
noncomputable def localSuccessProb {m n exponent q rounds : ℕ}
    (A : LocalRule n exponent q rounds) (G : PortNetwork m)
    (ids : Fin m → Fin (n ^ exponent)) : ℝ := by
  classical
  exact ∑ c ∈ Finset.univ.filter (fun c : Fin m → Fin q =>
    ∀ u v, G.Adj u v → c u ≠ c v), localOutputProb A G ids c

/-- Uniform Monte Carlo guarantee over all input graphs, identifiers and valid
known bounds. The algorithm is already fixed outside these quantifiers. -/
def ColorsNetworks {exponent q rounds : ℕ} (A : LocalAlgorithm exponent q rounds)
    (classOf : (m : ℕ) → PortNetwork m → Prop) (C : ℝ) : Prop :=
  ∀ n : ℕ, 1 ≤ n → ∀ m : ℕ, m ≤ n → ∀ G : PortNetwork m, classOf m G →
    ∀ ids : Fin m → Fin (n ^ exponent), Function.Injective ids →
      1 - 1 / (n : ℝ) ^ C ≤ localSuccessProb (A n) G ids

end QuantumSymmetryBreaking.CycleColoring.Supplement


