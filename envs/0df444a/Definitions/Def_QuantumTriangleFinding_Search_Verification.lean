-- Prove2me | Definitions.Def_QuantumTriangleFinding_Search_Verification
-- name    : QuantumTriangleFinding_Search_Verification
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-10T20:25:22.821685+00:00
-- url     : https://prove2.me/theorems/31c10a1d-649b-4a7f-ab7c-c9c583e43f05
-- title:
--   Operational exact verification of finite search relations
-- statement:
--   Let $I$ be a finite Boolean query set, $O$ a finite output set, $D$ a promised input domain and $V(x,o)$ the valid-output relation. A $v$-query exact verifier consists of a finite ancillary register and, for each candidate $o$, a published query circuit whose gates and acceptance decoder are fixed independently of $x$, such that
--   $$\Pr[\text{verifier accepts }o\text{ on }x]=1_{V(x,o)}\qquad(x\in D).$$
--   The candidate register can be retained while these circuits run coherently, so verification preserves genuine success. This is an operational query condition and does not assume the comparison theorem's conclusion.
--
--   The common domain is the union of the negative support and the unlabeled positive support. A known-zero idle query index represents the empty-coordinate case and is simulated by the phase-zero branch when coordinates exist. Search success sums the actual Born probabilities of valid outputs. Finally $\max_e\alpha_e$ is implemented as the finite nonnegative maximum with empty maximum zero.
--
--   These definitions allow inaccessible positive labels while keeping both the search relation and verification dependent only on the actual oracle input.
-- source:
--   Arjan Cornelissen, Amin Shiraz Gilani, Xingyu Zhou, STOC 2027 submission #1375 (October 2026), §§3.2, 4.1, pp. 13–16; Theorem 4.1 and its coherent verifier paragraph, p. 16

import Definitions.Def_QuantumTriangleFinding_Search_FiniteProbability
import Definitions.Def_QAlgorithms_Defs_Query

set_option autoImplicit false
open scoped BigOperators
noncomputable section

namespace QuantumTriangleFinding.Search

/-- A known zero query sector covers the empty coordinate set as well.
For nonempty I it is already simulated by the phase-zero branch. -/
def withIdle {I : Type} (x : I → Bool) : Option I → Bool := fun e => e.elim false x

def relationSuccess {I O W : Type} [Fintype I] [DecidableEq I]
    [Fintype O] [DecidableEq O] [Fintype W] [DecidableEq W] {t : ℕ}
    (valid : (I → Bool) → O → Prop) (x : I → Bool)
    (A : QAlgorithms.QueryAlg (Option I) Bool W t)
    (out : ((Option I × Bool) × W) → O) : ℝ := by
  classical
  exact ∑ o, if valid x o then
    A.outputProb (QAlgorithms.controlledPhaseOracle (withIdle x)) out o else 0

/-- Section 4.1, p.16: genuine operational exact verification in v queries on the promised domain.
The finite register Fin k is arbitrary. Candidate-dependent starts, gates and decoders are fixed
before x and can be run coherently while retaining the candidate register. Exact acceptance
therefore preserves success, including superpositions of candidates. -/
def HasExactVerifier {I O : Type} [Fintype I] [DecidableEq I]
    (D : Set (I → Bool)) (valid : (I → Bool) → O → Prop) (v : ℕ) : Prop := by
  classical
  exact ∃ k : ℕ, ∃ V : O → QAlgorithms.QueryAlg (Option I) Bool (Fin k) v,
    ∃ accept : O → ((Option I × Bool) × Fin k) → Bool,
      ∀ x ∈ D, ∀ o,
        (V o).outputProb (QAlgorithms.controlledPhaseOracle (withIdle x)) (accept o) true =
          if valid x o then 1 else 0

/-- Positive inputs may have a label, while verification and the search relation depend only on x. -/
def comparisonDomain {I L : Type} (ρn : (I → Bool) → ℝ)
    (ρp : (L × (I → Bool)) → ℝ) : Set (I → Bool) :=
  {x | 0 < ρn x ∨ ∃ a, 0 < ρp (a, x)}

/-- Max α with a 0 floor: the empty-coordinate value is exactly zero. -/
def maxCoefficient {I : Type} [Fintype I] (α : I → ℝ) : ℝ :=
  ((Finset.univ.sup fun i => Real.toNNReal (α i)) : NNReal)

end QuantumTriangleFinding.Search


