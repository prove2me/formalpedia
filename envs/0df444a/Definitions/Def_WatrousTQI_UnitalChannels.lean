-- Prove2me | Definitions.Def_WatrousTQI_UnitalChannels
-- name    : WatrousTQI_UnitalChannels
-- status  : Definition
-- author  : @Mrnaiq
-- created : 2026-11-11T22:55:05.519292+00:00
-- url     : https://prove2.me/theorems/0bf5c738-a3df-4ae2-9a17-addcf9ae28e6
-- title:
--   Unital channels as a real convex set
-- statement:
--   For each natural dimension $d$, this is the set of all maps on complex $d\times d$ matrices that are trace-preserving completely positive quantum channels and satisfy $\Phi(I_d)=I_d$. The published channel predicate means an arbitrary finite normalized Kraus representation, not a random-unitary representation. The set is represented inside the space of all matrix-valued functions; convexity and finite-dimensionality of its channel span are separate theorem targets. The definition is total also at $d=0$; all general-dimension theorem targets explicitly require $d>0$, and the main goal uses $d=2$.
-- source:
--   John Watrous, The Theory of Quantum Information, Cambridge University Press, 2018, Chapter 4. https://cs.uwaterloo.ca/~watrous/TQI/TQI.pdf; §4.2.1, proof of Theorem 4.23, equation (4.158), printed p.227 (PDF p.235).

import Mathlib
import Definitions.Def_QAlgorithms_Defs_Channel
set_option autoImplicit false
noncomputable section
open scoped Matrix ComplexConjugate BigOperators

namespace WatrousTQI

def unitalChannels (d : ℕ) : Set (QAlgorithms.Superop (Fin d) (Fin d)) :=
  {Φ | QAlgorithms.IsChannel Φ ∧ Φ (1 : Matrix (Fin d) (Fin d) ℂ) = 1}

end WatrousTQI


