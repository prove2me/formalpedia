-- Prove2me | Definitions.Def_CompressedOracleDuality_LabelSymmetric_Supplement_MatchedLabels
-- name    : CompressedOracleDuality_LabelSymmetric_Supplement_MatchedLabels
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-15T22:08:01.483905+00:00
-- url     : https://prove2.me/theorems/85a2cb52-beec-494e-be05-f7f097770f1a
-- title:
--   Minimum matched-label sets and the fixed injective run
-- statement:
--   Let $B$ be a deterministic collision branching program and let $m$ be a reachable state in its layer $t$. A label subset $U\subseteq Y$ is matched at $m$ if every permutation fixing $U$ pointwise fixes $m$ under the induced execution action:
--   $$\bigl(\forall y\in U,\ \sigma(y)=y\bigr)\Longrightarrow\sigma\cdot m=m.$$
--   For $2t<N$, define $L(m)$ by selecting a matched subset of minimum cardinality among all label subsets. The family is finite and contains the full label set. For label-symmetric programs in this range, the source proves the minimizer is unique. Outside $2t<N$ the formal definition explicitly returns the empty set, and the supplement's statements use $L$ only inside its valid range. Minimality, uniqueness, containment in every small matched set, $|L(m)|\le t$, equivariance, and the one-step inclusion (82) are mathematical consequences to establish from the executions, rather than hypotheses or fields of the program.
--
--   On the canonical injective execution, set $L_t^*=L(m_t^*)$. A permutation extends an oracle $H$ on a label subset $U$ precisely when
--   $$e(x)\in U\Longrightarrow\sigma(H^*(x))=H(x)\quad\text{for every input }x.$$
--   This transports the paper's common input/label carrier through its fixed binary identification. The definitions provide the same matched-set object for Lemmas 5.6 and 5.8, and introduce no quantum compressed-oracle object.
-- source:
--   Ding and Zhandry, Compressed Oracle Duality: A simple framework for knowing what quantum adversaries know, October 30, 2026 preprint, arXiv:submit/8306656 [quant-ph], STOC 2027 submission #94; source.pdf SHA-256 6614c6a707d45eff1e475fa25c9c0d22747adf304a0680ebf79d2bd118122daa; https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/94.pdf, Section 5.1, pp.27-28; (82), Section 5.2 and (83), p.29

import Definitions.Def_CompressedOracleDuality_LabelSymmetric_Supplement_ClassicalModel

noncomputable section

namespace CompressedOracleDuality.LabelSymmetric.Supplement

/-- §5.1, pp.27-28: the pointwise stabilizer of U fixes the memory state. -/
def Matched {n T : ℕ} (B : ClassicalProgram n T) (t : Fin (T + 1))
    (m : ReachableState B t) (U : Finset (Label n)) : Prop :=
  ∀ σ : Equiv.Perm (Label n), (∀ y ∈ U, σ y = y) → relabelState B t σ m = m

/-- §5.1: select a minimum-cardinality matched set from the finite set of all label subsets.
Existence follows from finiteness and the full label set being matched. Under label symmetry and
2t<N this minimizer is unique; uniqueness, |L|≤t, equivariance, and (82) must be proved from
executions, and are not assumed by this definition. Outside 2t<N the explicit unused value is ∅. -/
def matchedLabels {n T : ℕ} (B : ClassicalProgram n T) (t : Fin (T + 1))
    (m : ReachableState B t) : Finset (Label n) :=
  if 2 * t.val < 2 ^ n then
    Classical.epsilon (fun U : Finset (Label n) =>
      Matched B t m U ∧ ∀ V : Finset (Label n), Matched B t m V → U.card ≤ V.card)
  else ∅

/-- §5.2: L*_t is obtained from the fixed injective execution, never from the random run. -/
def injectiveLabels {n T : ℕ} (B : ClassicalProgram n T) (t : Fin (T + 1)) :
    Finset (Label n) :=
  matchedLabels B t (injectiveState B t)

/-- (83): transporting the label subset back to inputs using the fixed canonical bijection. -/
def ExtendsOn {n : ℕ} (σ : Equiv.Perm (Label n)) (H : Input n → Label n)
    (U : Finset (Label n)) : Prop :=
  ∀ x : Input n, inputLabelEquiv n x ∈ U → σ (injectiveOracle n x) = H x

end CompressedOracleDuality.LabelSymmetric.Supplement


