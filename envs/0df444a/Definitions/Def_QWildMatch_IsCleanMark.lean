-- Prove2me | Definitions.Def_QWildMatch_IsCleanMark
-- name    : QWildMatch_IsCleanMark
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T10:15:33.604202+00:00
-- url     : https://prove2.me/theorems/2b2a5325-323f-4809-b5d4-97c37433d56d
-- title:
--   A clean Boolean verifier (Definition 3.2), and query circuits on arbitrary input states
-- statement:
--   A clean Boolean verifier for $f$ is a possibly approximate unitary acting as
--
--   $$|x\rangle|z\rangle|0^a\rangle\mapsto|x\rangle|z\oplus f(x)\rangle|0^a\rangle$$
--
--   on the initialized-ancilla subspace, with state-norm error bounded uniformly over the index inputs and their superpositions. For a query circuit $V$ with oracle $O$ and error parameter $\varepsilon$ this says that for every state $\varphi$ on the index and target registers,
--
--   $$\bigl\|V^{O}(|q_0\rangle\otimes\varphi\otimes|a_0\rangle)-|q_0\rangle\otimes X_f\varphi\otimes|a_0\rangle\bigr\|\le\varepsilon\|\varphi\|,$$
--
--   where $X_f|x,z\rangle=|x,z\oplus f(x)\rangle$. This excludes measured, variable-length classical procedures, which are not unitaries of this form.
--
--   **Formalization Note** `applyTo` runs the circuit of a `QueryAlg` on a given state instead of its own start state, and `markEmbed` builds the state $|q_0\rangle\otimes\varphi\otimes|a_0\rangle$. The index and target registers sit in the workspace of `QueryAlg`, and $q_0$ is the initialized query register. The quantifier over all $\varphi$ is the page's uniformity over inputs and superpositions.
-- source:
--   Zhao, Chen, Li, Kong, Peng, Yu, Yue, Quantum Approximate Pattern Matching with Wildcards and Weighted Edits, STOC 2027 submission (file sha256 9e87a9dd…), Definition 3.2, p.4

import Mathlib
import Definitions.Def_QAlgorithms_Defs_Query

namespace QWildMatch

open QAlgorithms

/-- The query circuit `U_Q O U_{Q−1} ⋯ U_1 O U_0` of a `QueryAlg` applied to an arbitrary input state
`ψ`, instead of the algorithm's own start state. It is needed for Definition 3.2 and Lemma 6.3
(Zhao et al., STOC 2027 submission, pp.4, 9), which describe the unitary on given inputs. -/
noncomputable def applyTo {ι κ W : Type*} [Fintype ι] [Fintype κ] [Fintype W] [DecidableEq ι]
    [DecidableEq κ] [DecidableEq W] {Q : ℕ} (A : QueryAlg ι κ W Q) (O : Matrix (ι × κ) (ι × κ) ℂ)
    (ψ : EuclideanSpace ℂ ((ι × κ) × W)) : EuclideanSpace ℂ ((ι × κ) × W) :=
  (Fin.induction (motive := fun _ => EuclideanSpace ℂ ((ι × κ) × W))
    (act (A.U 0 : Matrix _ _ ℂ) ψ)
    (fun i φ => act (A.U i.succ : Matrix _ _ ℂ) (act (Matrix.kronecker O (1 : Matrix W W ℂ)) φ))
    (Fin.last Q))

/-- The state `|q₀⟩ ⊗ φ ⊗ |a₀⟩` with `φ` on the index and target registers `|x⟩|z⟩`, the query
register initialized to `q₀` and the ancilla to `a₀` (Zhao et al., STOC 2027 submission,
Definition 3.2, p.4). -/
noncomputable def markEmbed {ι κ W : Type*} [DecidableEq ι] [DecidableEq κ] [DecidableEq W] {N : ℕ}
    (q₀ : ι × κ) (a₀ : W) (φ : EuclideanSpace ℂ (Fin N × ZMod 2)) :
    EuclideanSpace ℂ ((ι × κ) × (Fin N × ZMod 2 × W)) :=
  WithLp.toLp 2 (fun p => if p.1 = q₀ ∧ p.2.2.2 = a₀ then φ (p.2.1, p.2.2.1) else 0)

/-- Definition 3.2 (Clean text oracle), Zhao et al., STOC 2027 submission, p.4: the circuit `V` with
oracle `O` acts as `|x⟩|z⟩|0^a⟩ ↦ |x⟩|z ⊕ f(x)⟩|0^a⟩` on the initialized subspace, with state-norm
error at most `ε`, uniformly over index inputs and their superpositions.

**Formalization Note** The quantifier over every `φ` on the index and target registers is the page's
"uniformly over the index inputs and over their superpositions". The bound scales with `‖φ‖`, so
`φ` need not be normalized. The index and target registers sit in the workspace of `QueryAlg`, and
`q₀` is the initialized query register. The ideal map is `xorOracle f`. -/
def IsCleanMark {ι κ W : Type*} [Fintype ι] [Fintype κ] [Fintype W] [DecidableEq ι] [DecidableEq κ]
    [DecidableEq W] {N Q : ℕ} (V : QueryAlg ι κ (Fin N × ZMod 2 × W) Q)
    (O : Matrix (ι × κ) (ι × κ) ℂ) (f : Fin N → ZMod 2) (q₀ : ι × κ) (a₀ : W) (ε : ℝ) : Prop :=
  ∀ φ : EuclideanSpace ℂ (Fin N × ZMod 2),
    ‖applyTo V O (markEmbed q₀ a₀ φ) - markEmbed q₀ a₀ (act (xorOracle f) φ)‖ ≤ ε * ‖φ‖

end QWildMatch


