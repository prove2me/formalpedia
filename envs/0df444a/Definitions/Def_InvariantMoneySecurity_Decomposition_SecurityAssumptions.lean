-- Prove2me | Definitions.Def_InvariantMoneySecurity_Decomposition_SecurityAssumptions
-- name    : InvariantMoneySecurity_Decomposition_SecurityAssumptions
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-08T09:00:52.720224+00:00
-- url     : https://prove2.me/theorems/5e60e393-5632-46ae-b423-4eb66553b75b
-- title:
--   Security, preparation, measure-first forgery, and transfer
-- statement:
--   A forger is any uniform QPT family receiving the public serial and one coherent banknote and returning two quantum registers. Its success $\operatorname{win}_A(n)$ averages the joint two-register verifier probability under the actual mint law. Security means that this function is negligible for every such forger. A measure-first forger uses the same unrestricted quantum computation after the initial computational-basis measurement. Its probability $\operatorname{win}_A^M(n)$ averages over the measured-mint pairs $(p,x)$, supplying $|x\rangle$ in place of the coherent note.
--
--   A preparer receives only classical $(p,x)$, returns one reduced register $\sigma_B(p,x)$, and has advantage
--   $$\operatorname{adv}_B(n)=\mathbb E_{(p,x)\leftarrow M_n}\operatorname{aw}_p(\sigma_B(p,x)).$$
--   The preparation assumption requires negligible advantage for every uniform QPT preparer. Workspace can remain entangled with the output and is discarded, and accepted weight counts all same-serial orbits.
--
--   The transfer assumption is
--   $$\exists q\;\forall A\;\exists B\;\exists\nu_A:\quad \nu_A=\operatorname{negl},\quad\forall n\ge1,\quad\operatorname{win}_A(n)\le q(n)\operatorname{win}_B^M(n)+\nu_A(n).$$
--   Here $q$ is one positive real polynomial independent of $A$, $B$ can differ from $A$, and $\nu_A$ is nonnegative. Positivity and nonnegativity are harmless conventional representatives: polynomial factors and negligible errors can be enlarged to such representatives. All probabilities in these predicates are computed by the underlying channels and effects; none is an uninterpreted input or a disguised implication between assumptions.
-- source:
--   Hans Schmiedel, Jiangshan Yu, STOC 2027 submission #164 (October 2026), p. 9, Definition 2.4; p. 26, Assumption 6.1; p. 28, Definition 6.4 and Assumption 6.6

import Definitions.Def_InvariantMoneySecurity_Decomposition_MintVerifier
set_option autoImplicit false
noncomputable section

namespace InvariantMoneySecurity.Decomposition

/-- Arbitrary uniform QPT forgers with public serial and coherent challenge input. -/
abbrev Scheme.Forger (D : Scheme) :=
  QPT (fun n => (D.data n).serialBits + n) (fun n => n + n)

/-- Arbitrary uniform QPT preparers with classical public serial and measured seed input. -/
abbrev Scheme.Preparer (D : Scheme) :=
  QPT (fun n => (D.data n).serialBits + n) (fun n => n)

/-- Definition 2.4's exact joint game probability, averaged under the genuine mint law. -/
def Scheme.win (D : Scheme) (A : D.Forger) (n : ℕ) : ℝ :=
  (D.data n).mintAverage fun p _ =>
    (D.data n).jointAcceptance p (D.rounds n)
      (A.run n (classicalQuantumInput p (ketbra ((D.data n).banknote p))))

/-- Definition 6.4: dephase the challenge first; all subsequent computation remains quantum.
The uniform object average is exactly the joint measured-mint law of Definition 2.2. -/
def Scheme.winMeasured (D : Scheme) (A : D.Forger) (n : ℕ) : ℝ :=
  (D.data n).mintAverage fun p x =>
    (D.data n).jointAcceptance p (D.rounds n)
      (A.run n (classicalQuantumInput p (ketbra (basisVector x.val))))

/-- Assumption 6.1's average accepted weight. Garbage is discarded by the QPT execution. -/
def Scheme.preparationAdvantage (D : Scheme) (B : D.Preparer) (n : ℕ) : ℝ :=
  (D.data n).mintAverage fun p x =>
    (D.data n).acceptedWeight p
      (B.run n (ketbra (basisVector (appendBits p x.val))))

/-- Security quantifies over all circuits satisfying the concrete uniform QPT specification. -/
def Scheme.Secure (D : Scheme) : Prop := ∀ A : D.Forger, Negligible (D.win A)

/-- Negation means infinitely-often inverse-polynomial advantage, not an eventual lower bound. -/
def Scheme.Preparation (D : Scheme) : Prop :=
  ∀ B : D.Preparer, Negligible (D.preparationAdvantage B)

/-- Existence of an efficient winning measure-first adversary. -/
def Scheme.MeasureFirstFailure (D : Scheme) : Prop :=
  ∃ A : D.Forger, ¬ Negligible (D.winMeasured A)

/-- Assumption 6.6 with its uniform quantifier order and pointwise inequality for n≥1.
The witness B names the quantum computation after the mandatory initial measurement. -/
def Scheme.Transfer (D : Scheme) : Prop :=
  ∃ q : Polynomial ℝ, PositivePolynomial q ∧
    ∀ A : D.Forger, ∃ B : D.Forger, ∃ ν : ℕ → ℝ,
      (∀ n, 0 ≤ ν n) ∧ Negligible ν ∧
      ∀ n, 1 ≤ n → D.win A n ≤ q.eval (n : ℝ) * D.winMeasured B n + ν n

end InvariantMoneySecurity.Decomposition


