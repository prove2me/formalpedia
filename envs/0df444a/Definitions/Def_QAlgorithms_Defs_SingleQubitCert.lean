-- Prove2me | Definitions.Def_QAlgorithms_Defs_SingleQubitCert
-- name    : QAlgorithms_Defs_SingleQubitCert
-- status  : Definition
-- author  : @Goku
-- created : 2026-10-18T19:12:43.592993+00:00
-- url     : https://prove2.me/theorems/e8f3a253-e77a-4b08-963b-ebb794855c42
-- title:
--   Certification with single-qubit measurements and product-projector queries
-- statement:
--   # Certification with single-qubit measurements and product-projector queries
--   (shared definition layer)
--
--   arXiv:2506.11355v2, cited "2506.11355 p.N" (PDF pages): Definition 3 and Remark 4 (p.4),
--   Definition 15 and §2.4 (p.8).
--
--   Model. The algorithm has Definition-15 oracle access to the hypothesis state `|hyp⟩` (a query
--   `Π₁ ⊗ ⋯ ⊗ Π_n` of single-qubit projectors returns `⟨hyp|Π₁ ⊗ ⋯ ⊗ Π_n|hyp⟩`), can flip fair
--   coins (uniform choice among `m` values), and touches its one copy of the lab state `ρ_lab` only
--   by single-qubit projective measurements in a basis `{U|0⟩, U|1⟩}`, the qubit and the basis
--   chosen adaptively (Remark 4). The lab state is carried as a subnormalized density matrix (Lüders
--   rule without renormalization), so the trace at a leaf is the probability of that branch.
--   -/
--
--   namespace QAlgorithms
--
--   /-- 2506.11355 p.8, Definition 15: a single-qubit (orthogonal) projector, of any rank (`0`, a
--   rank-one projector, or `I`).
-- source:
--   Source references and exact conventions are recorded in each declaration docstring. algorithms\QAlgorithms\Defs\SingleQubitCert.lean

import Definitions.Def_QAlgorithms_Defs_StabilizerLearning
/-!
# Certification with single-qubit measurements and product-projector queries
(shared definition layer)

arXiv:2506.11355v2, cited "2506.11355 p.N" (PDF pages): Definition 3 and Remark 4 (p.4),
Definition 15 and §2.4 (p.8).

Model. The algorithm has Definition-15 oracle access to the hypothesis state `|hyp⟩` (a query
`Π₁ ⊗ ⋯ ⊗ Π_n` of single-qubit projectors returns `⟨hyp|Π₁ ⊗ ⋯ ⊗ Π_n|hyp⟩`), can flip fair
coins (uniform choice among `m` values), and touches its one copy of the lab state `ρ_lab` only
by single-qubit projective measurements in a basis `{U|0⟩, U|1⟩}`, the qubit and the basis
chosen adaptively (Remark 4). The lab state is carried as a subnormalized density matrix (Lüders
rule without renormalization), so the trace at a leaf is the probability of that branch.
-/

namespace QAlgorithms

/-- 2506.11355 p.8, Definition 15: a single-qubit (orthogonal) projector, of any rank (`0`, a
rank-one projector, or `I`). -/
def IsQubitProjector (P : Matrix Bool Bool ℂ) : Prop :=
  P.IsHermitian ∧ P * P = P

/-- 2506.11355 p.8, Definition 15: the answer `⟨ψ|Π₁ ⊗ ⋯ ⊗ Π_n|ψ⟩` to a product-projector query
(real for Hermitian factors; factor `k` acts on wire `k`, frozen `kronAll`). -/
noncomputable def productProjOracle {n : ℕ} (ψ : EuclideanSpace ℂ (Qubits n))
    (Pj : Fin n → Matrix Bool Bool ℂ) : ℝ :=
  (inner ℂ ψ (act (kronAll Pj) ψ)).re

/-- 2506.11355 pp.2, 4 (Definition 3, Remark 4), p.8: a randomized algorithm with Definition-15
access to `|hyp⟩` and single-qubit measurement access to one copy of `ρ_lab`: a tree whose nodes
are a product-projector query (branching on the real answer), a uniform coin among `m ⩾ 1`
values, a measurement of qubit `q` in the basis `{U|0⟩, U|1⟩}` (branching on the outcome), or an
output (`true` = Accept). No gates and no ancillas act on `ρ_lab`. -/
inductive SQCertAlg (n : ℕ) where
  | query (Pj : Fin n → Matrix Bool Bool ℂ) (hPj : ∀ k, IsQubitProjector (Pj k))
      (next : ℝ → SQCertAlg n)
  | sample (m : ℕ) (hm : 0 < m) (next : Fin m → SQCertAlg n)
  | measure (q : Fin n) (U : Matrix.unitaryGroup Bool ℂ) (next : Bool → SQCertAlg n)
  | output (accept : Bool)

namespace SQCertAlg

variable {n : ℕ}

/-- 2506.11355 p.4: the probability that the algorithm outputs `a` (`true` = Accept) when the
hypothesis is `ψ` and the lab state is `ρ` (subnormalized along a branch: measuring qubit `q`
with outcome `j` maps `ρ` to `P_j ρ P_j`, `P_j = U|j⟩⟨j|U†` on qubit `q`, frozen `qubitOp1`;
zero-probability branches contribute `0`). -/
noncomputable def outProb : SQCertAlg n → EuclideanSpace ℂ (Qubits n) →
    Matrix (Qubits n) (Qubits n) ℂ → Bool → ℝ
  | output b, _, ρ, a => if b = a then ρ.trace.re else 0
  | query Pj _ next, ψ, ρ, a => (next (productProjOracle ψ Pj)).outProb ψ ρ a
  | sample m _ next, ψ, ρ, a => (m : ℝ)⁻¹ * ∑ i, (next i).outProb ψ ρ a
  | measure q U next, ψ, ρ, a => ∑ j : Bool,
      (next j).outProb ψ
        (qubitOp1 ((U : Matrix Bool Bool ℂ) * Matrix.single j j 1 * star (U : Matrix Bool Bool ℂ)) q * ρ *
          qubitOp1 ((U : Matrix Bool Bool ℂ) * Matrix.single j j 1 * star (U : Matrix Bool Bool ℂ)) q) a

/-- 2506.11355 p.8 (§2.4, Lemma 16): every execution path makes at most `b` query, sampling and
measurement steps (the time measure: `O(1)` per step). -/
def StepsAtMost : SQCertAlg n → ℕ → Prop
  | output _, _ => True
  | query _ _ next, b => 1 ≤ b ∧ ∀ y, (next y).StepsAtMost (b - 1)
  | sample _ _ next, b => 1 ≤ b ∧ ∀ i, (next i).StepsAtMost (b - 1)
  | measure _ _ next, b => 1 ≤ b ∧ ∀ j, (next j).StepsAtMost (b - 1)

end SQCertAlg

/-! ### Sanity tests -/

example : IsQubitProjector 1 ∧ IsQubitProjector 0 :=
  ⟨⟨Matrix.isHermitian_one, by simp⟩, ⟨Matrix.isHermitian_zero, by simp⟩⟩

example {n : ℕ} (ψ : EuclideanSpace ℂ (Qubits n)) (ρ : Matrix (Qubits n) (Qubits n) ℂ) :
    (SQCertAlg.output true).outProb ψ ρ true = ρ.trace.re ∧
      (SQCertAlg.output true).outProb ψ ρ false = 0 := by
  simp [SQCertAlg.outProb]

example {n : ℕ} (b : Bool) : (SQCertAlg.output (n := n) b).StepsAtMost 0 := trivial

example {n : ℕ} (next : Fin 1 → SQCertAlg n) : ¬ (SQCertAlg.sample 1 one_pos next).StepsAtMost 0 := by
  simp [SQCertAlg.StepsAtMost]

example {n : ℕ} (ψ : EuclideanSpace ℂ (Qubits n)) :
    productProjOracle ψ (fun _ => 1) = ‖ψ‖ ^ 2 := by
  have h : kronAll (fun _ : Fin n => (1 : Matrix Bool Bool ℂ)) = 1 := by
    ext y z
    simp [kronAll, Matrix.one_apply, Finset.prod_boole, funext_iff]
  rw [productProjOracle, h]
  simp [act, inner_self_eq_norm_sq_to_K]
  norm_cast

end QAlgorithms


