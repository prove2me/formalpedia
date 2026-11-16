-- Prove2me | Definitions.Def_CompressedOracleDuality_LabelSymmetric_Supplement_ClassicalModel
-- name    : CompressedOracleDuality_LabelSymmetric_Supplement_ClassicalModel
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-15T22:07:29.629173+00:00
-- url     : https://prove2.me/theorems/ccc4db25-19a6-4f2e-9280-12d1f1cdeb41
-- title:
--   Classical collision executions and their induced relabeling action
-- statement:
--   Put $N=2^n$. Reuse the published input basis $X=\{0,\ldots,N-1\}$, label basis $Y=\{0,1\}^n$, and outputs consisting of failure or a triple $(x_1,x_2,y)$. A classical collision program is the general layered program on these alphabets. Its memory map $\mu_t(H)$ is its recursively defined execution. It is label-symmetric when, for every $0\le t\le T$, every two oracles $H_1,H_2:X\to Y$, and every permutation $\sigma$ of $Y$,
--   $$\mu_t(H_1)=\mu_t(H_2)\iff\mu_t(\sigma\circ H_1)=\mu_t(\sigma\circ H_2).$$
--   Its success probability is the uniform average over all $N^N$ functions of the indicator that its actual final output satisfies $x_1<x_2$ and $H(x_1)=H(x_2)=y$; failure is unsuccessful.
--
--   Reachable layer-$t$ states are exactly the image of $\mu_t$. Choose a representative oracle for each reachable state and define $\sigma\cdot\mu_t(H)=\mu_t(\sigma\circ H)$. Under the symmetry iff this is independent of the representative and forms a group action; the module includes its structural computation rule and action laws. This construction does not permute the queried input.
--
--   The canonical bijection $e:X\simeq Y$ is the most-significant-bit-first binary representation from the published query library. Set $H^*(x)=e(x)$, $m_t^*=\mu_t(H^*)$, and $x_t^*=q_t(m_t^*)$. These objects are fixed independently of random $H$. They supply the injective comparison run in Section 5.2, including the terminal state.
-- source:
--   Ding and Zhandry, Compressed Oracle Duality: A simple framework for knowing what quantum adversaries know, October 30, 2026 preprint, arXiv:submit/8306656 [quant-ph], STOC 2027 submission #94; source.pdf SHA-256 6614c6a707d45eff1e475fa25c9c0d22747adf304a0680ebf79d2bd118122daa; https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/94.pdf, Definition 5.1, (78), p.26; Definition 5.4, (80), Remark 5.5, p.27; Section 5.2, p.29

import Definitions.Def_CompressedOracleDuality_LabelSymmetric_Model
import Definitions.Def_CompressedOracleDuality_LabelSymmetric_Supplement_LayeredProgram

open scoped BigOperators

noncomputable section

namespace CompressedOracleDuality.LabelSymmetric.Supplement

/-- Definition 5.4 specialized to N-way collision finding; the general program is separate. -/
abbrev ClassicalProgram (n T : ℕ) := LayeredProgram (Input n) (Label n) (CollisionOutput n) T

/-- Definition 5.1, (78), p.26: equality of states is preserved and reflected by relabeling,
at every layer, including the output layer. Only the oracle's labels are permuted. -/
def ClassicalLabelSymmetric {n T : ℕ} (B : ClassicalProgram n T) : Prop :=
  ∀ (t : Fin (T + 1)) (H₁ H₂ : Input n → Label n) (σ : Equiv.Perm (Label n)),
    B.run H₁ t = B.run H₂ t ↔ B.run (σ ∘ H₁) t = B.run (σ ∘ H₂) t

/-- Theorem 5.3 and Lemma 5.8: the actual uniform average over all N^N functions.
`Successful` is the published predicate requiring an ordered pair and its reported common label. -/
def classicalSuccess {n T : ℕ} (B : ClassicalProgram n T) : ℝ :=
  open Classical in
  (Fintype.card (Input n → Label n) : ℝ)⁻¹ *
    ∑ H : Input n → Label n,
      if Successful H (B.output (B.run H (Fin.last T))) then (1 : ℝ) else 0

/-- Reachability is derived from the execution, not supplied as an independent memory map. -/
def ReachableState {n T : ℕ} (B : ClassicalProgram n T) (t : Fin (T + 1)) :=
  {m : B.Vertex t // ∃ H : Input n → Label n, B.run H t = m}

/-- A representative oracle for a reachable state. No claim about its answers is assumed. -/
def representativeOracle {n T : ℕ} (B : ClassicalProgram n T) (t : Fin (T + 1))
    (m : ReachableState B t) : Input n → Label n :=
  Classical.choose m.property

/-- (80), p.27: relabel a representative execution. Under ClassicalLabelSymmetric this
is independent of the representative and satisfies the group-action laws; these are consequences,
not additional hypotheses or fields in the program. -/
def relabelState {n T : ℕ} (B : ClassicalProgram n T) (t : Fin (T + 1))
    (σ : Equiv.Perm (Label n)) (m : ReachableState B t) : ReachableState B t :=
  ⟨B.run (σ ∘ representativeOracle B t m) t, ⟨σ ∘ representativeOracle B t m, rfl⟩⟩

/-- Structural computation rule for the induced operation, using (78) only. -/
theorem relabelState_run {n T : ℕ} (B : ClassicalProgram n T)
    (hsym : ClassicalLabelSymmetric B) (t : Fin (T + 1))
    (σ : Equiv.Perm (Label n)) (H : Input n → Label n) :
    relabelState B t σ ⟨B.run H t, ⟨H, rfl⟩⟩ =
      ⟨B.run (σ ∘ H) t, ⟨σ ∘ H, rfl⟩⟩ := by
  apply Subtype.ext
  exact (hsym t _ H σ).mp (Classical.choose_spec
    (show ∃ K : Input n → Label n, B.run K t = B.run H t from ⟨H, rfl⟩))

/-- (80) and Remark 5.5: the genuine induced group action, with only structural laws.
No matched-set estimate is bundled into this object. -/
@[instance_reducible] def reachableAction {n T : ℕ} (B : ClassicalProgram n T)
    (hsym : ClassicalLabelSymmetric B) (t : Fin (T + 1)) :
    MulAction (Equiv.Perm (Label n)) (ReachableState B t) where
  smul := relabelState B t
  one_smul m := by
    obtain ⟨m, H, rfl⟩ := m
    change relabelState B t 1 _ = _
    simpa using relabelState_run B hsym t 1 H
  mul_smul σ τ m := by
    obtain ⟨m, H, rfl⟩ := m
    change relabelState B t (σ * τ) _ = relabelState B t σ (relabelState B t τ _)
    rw [relabelState_run B hsym t τ H,
      relabelState_run B hsym t σ (τ ∘ H), relabelState_run B hsym t (σ * τ) H]
    rfl

/-- The canonical most-significant-bit-first identification of the two published bases. -/
def inputLabelEquiv (n : ℕ) : Input n ≃ Label n :=
  (QAlgorithms.bitsEquivFin n).symm

/-- §5.2: H*(x)=x, transported through the fixed identification of inputs and labels. -/
def injectiveOracle (n : ℕ) : Input n → Label n := inputLabelEquiv n

/-- The fixed state reached on the injective oracle, including at the terminal layer. -/
def injectiveState {n T : ℕ} (B : ClassicalProgram n T) (t : Fin (T + 1)) :
    ReachableState B t :=
  ⟨B.run (injectiveOracle n) t, ⟨injectiveOracle n, rfl⟩⟩

/-- The fixed query x*_t, independent of the uniformly random oracle H. -/
def injectiveQuery {n T : ℕ} (B : ClassicalProgram n T) (t : Fin T) : Input n :=
  B.query t (B.run (injectiveOracle n) t.castSucc)

end CompressedOracleDuality.LabelSymmetric.Supplement


