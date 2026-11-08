-- Prove2me | Definitions.Def_FRouting_QSD
-- name    : FRouting_QSD
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T11:11:59.254101+00:00
-- url     : https://prove2.me/theorems/2ac11f59-0d6a-482a-b5e4-c0d5a1b02c95
-- title:
--   Quantum State Distinguishability, $\mathrm{QSD}_{\alpha,\beta}$ and $\mathrm{coQSD}_{\alpha,\beta}$
-- statement:
--   An instance is a pair of circuits $(C_0,C_1)$ with output registers of the same dimension. Let $\sigma_b$ be the reduced state on the output register obtained by running $C_b$ on the all-zero state and tracing out the other registers. In $\mathrm{QSD}_{\alpha,\beta}$ the Yes instances have $\Delta(\sigma_0,\sigma_1)\ge\beta$ and the No instances have $\Delta(\sigma_0,\sigma_1)\le\alpha$. In the complement $\mathrm{coQSD}_{\alpha,\beta}$ the Yes instances are the close pairs. A string that is not an instance is in neither set.
--
--   **Formalization Note** Instances are over any qudit dimension and share it, since Lemma 5.7 feeds $d$-dimensional circuits to QSD; $d=2$ is the printed problem. An instance carries free padding, since the map of Lemma 5.7 outputs $(1^n,C_0,C_1)$.
-- source:
--   Renard, Computational Bounds for f-Routing, arXiv:2609.40278 (held copy, sha256 4a327f29…), Definition 5.5, p.21

import Definitions.Def_PeresTerno_kraus_basics
import Definitions.Def_DimFreeShadow_traceDistance
import Definitions.Def_FRouting_encCircuit
import Definitions.Def_FRouting_languageOf

set_option autoImplicit false

namespace FRouting

open QAlgorithms.Complexity

/-- **An instance of QSD**: two circuits over the same qudit dimension with output registers of the
same dimension, and a free padding string. Renard, *Computational Bounds for f-Routing*,
arXiv:2609.40278 (held copy, sha256 4a327f29…), Definition 5.5, p.21.

**Formalization Note** Padding: the map of Lemma 5.7 sends `(x, y)` to `(1ⁿ, C₀, C₁)`, p.22, so an
instance needs room for `1ⁿ`, and a cheating verifier may need `(x, y)`. Instances are over any `d`,
since Lemma 5.7 feeds `d`-dimensional circuits to QSD; `d = 2` is the printed problem. -/
structure QSDInstance where
  /-- The qudit dimension. -/
  d : ℕ
  /-- The width of the output registers. -/
  k : ℕ
  /-- The number of input wires of `C₀`, all starting in `|0⟩`. -/
  in₀ : ℕ
  /-- The number of input wires of `C₁`, all starting in `|0⟩`. -/
  in₁ : ℕ
  /-- The circuit `C₀`. -/
  C₀ : Circuit d in₀ k
  /-- The circuit `C₁`. -/
  C₁ : Circuit d in₁ k
  /-- The padding. -/
  pad : Str

/-- The string of a QSD instance. -/
def encQSD (I : QSDInstance) : Str := encCircuit I.C₀ ++ encCircuit I.C₁ ++ I.pad

/-- `Δ(σ₀, σ₁)` for the output states of the two circuits on the all-zero state. -/
noncomputable def QSDInstance.dist (I : QSDInstance) : ℝ :=
  DimFreeShadow.traceDistance I.C₀.outputState I.C₁.outputState

/-- **`QSD_{α,β}`** (Definition 5.5, p.21). Yes: `Δ(σ₀, σ₁) ≥ β`. No: `Δ(σ₀, σ₁) ≤ α`. A string that
is not an instance is in neither. -/
def QSD (α β : ℝ) : PromiseProblem where
  Yes := { w | ∃ I : QSDInstance, w = encQSD I ∧ β ≤ I.dist }
  No := { w | ∃ I : QSDInstance, w = encQSD I ∧ I.dist ≤ α }

/-- **`coQSD_{α,β}`** (Definition 5.5, p.21): the complement, whose Yes instances are the close pairs. -/
def coQSD (α β : ℝ) : PromiseProblem where
  Yes := (QSD α β).No
  No := (QSD α β).Yes

end FRouting


