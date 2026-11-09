-- Prove2me | Definitions.Def_LeakageSpectral_Shannon_JointLaw
-- name    : LeakageSpectral_Shannon_JointLaw
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-08T10:28:22.104458+00:00
-- url     : https://prove2.me/theorems/1af8ad5f-1287-4d5b-a00f-7e669bebbaf5
-- title:
--   Definitions 1, 2 and Eq. (2) — likelihood ratio, posterior, $\chi^2$-MI, Shannon MI and Fourier energy of a joint law
-- statement:
--   Let $P$ be a joint law on $A\times B$, where $A$ is finite and $B$ is any measurable space, with marginals $p_A$ and $p_B$. The **likelihood ratio** and the **posterior** are
--
--   $$
--   r(a,b)=\frac{\mathrm dP}{\mathrm d(p_A\otimes p_B)}(a,b),\qquad p_{A\mid B}(a\mid b)=p_A(a)\,r(a,b).
--   $$
--
--   The **$\chi^2$-mutual information** and the **Shannon mutual information in bits** are
--
--   $$
--   I_{\chi^2}(A;B)=\mathbb E_B\big[\chi^2(p_{A\mid B}(\cdot\mid B)\,\|\,p_A)\big],\qquad I(A;B)=\frac{D(P\,\|\,p_A\otimes p_B)}{\ln2},
--   $$
--
--   where $D$ is the Kullback–Leibler divergence in nats. If $A$ is a finite abelian group and $\chi_w$ is a character, the **discrete Fourier transform of the posterior** and the **Fourier energy** are
--
--   $$
--   \hat p_{A\mid B}(w\mid b)=\sum_a p_{A\mid B}(a\mid b)\chi_w(a),\qquad \mathbb E_B\big[|\hat p_{A\mid B}(w\mid B)|^2\big].
--   $$
--
--   These definitions apply to one joint law and are used unchanged for the law of one share with its leakage and for the law of the secret with the whole leakage vector, so that local and global quantities are the same notions.
--
--   **Formalization Note** $P\ll p_A\otimes p_B$ holds automatically because $A$ is finite, and $r\le 1/p_A(a)$ almost everywhere where $p_A(a)>0$. The posterior is a real number, and it is determined only for $p_B$-almost every $b$, which is all the expectations use. `klDiv` is Mathlib's divergence, in nats and valued in $[0,\infty]$; it is finite here. The integrands are bounded, so the Bochner integrals are not vacuous.
-- source:
--   Rei Ueno, A Spectral Theory of Local-to-Global Leakage, STOC 2027 submission #326 (October 2026), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/326.pdf, Eq. (2), p. 9; Definition 1, p. 7; Definition 2, p. 7

import Mathlib
import Definitions.Def_LeakageSpectral_Shannon_Divergences
open MeasureTheory InformationTheory

namespace LeakageSpectral.Shannon

variable {A B : Type*} [Fintype A] [MeasurableSpace A] [MeasurableSpace B]

/-- The mass `p_A(a)` of the first marginal of a joint law `P` on `A × B`, `A` finite. -/
noncomputable def firstMarginal (P : Measure (A × B)) (a : A) : ℝ :=
  (P.fst {a}).toReal

/-- **Likelihood ratio** of a joint law (Eq. (2), p. 9):
`r(a, b) = dP / d(p_A ⊗ p_B) (a, b)`, the Radon–Nikodym derivative of `P` with respect to the product
of its marginals. -/
noncomputable def likelihoodRatio (P : Measure (A × B)) (a : A) (b : B) : ℝ :=
  (P.rnDeriv (P.fst.prod P.snd) (a, b)).toReal

/-- **Posterior** of a joint law: `p_{A∣B}(a ∣ b) = p_A(a) · r(a, b)`. It is determined for
`p_B`-almost every `b`. -/
noncomputable def posterior (P : Measure (A × B)) (a : A) (b : B) : ℝ :=
  firstMarginal P a * likelihoodRatio P a b

/-- **χ²-mutual information** of a joint law (Definition 2, p. 7):
`I_χ²(A; B) = E_B[χ²(p_{A∣B}(· ∣ B) ∥ p_A)]`. -/
noncomputable def chiSquareMI (P : Measure (A × B)) : ℝ :=
  ∫ b, chiSquareDiv (fun a => posterior P a b) (firstMarginal P) ∂P.snd

/-- **Shannon mutual information in bits** of a joint law:
`I(A; B) = D_KL(P ∥ p_A ⊗ p_B) / ln 2`, Mathlib's `klDiv` being in nats. -/
noncomputable def shannonMI (P : Measure (A × B)) : ℝ :=
  (klDiv P (P.fst.prod P.snd)).toReal / Real.log 2

/-- **Discrete Fourier transform of the posterior** (Definition 1, p. 7):
`p̂_{A∣B}(w ∣ b) = ∑ₐ p_{A∣B}(a ∣ b) χ_w(a)`, for a character `w` of the finite abelian group `A`. -/
noncomputable def posteriorDFT [AddCommGroup A] (P : Measure (A × B)) (w : AddChar A ℂ) (b : B) : ℂ :=
  ∑ a, (posterior P a b : ℂ) * w a

/-- **Fourier energy** of a joint law at the character `w` (Definition 1, p. 7, and Eq. (14), p. 27):
`E_B[|p̂_{A∣B}(w ∣ B)|²]`. -/
noncomputable def fourierEnergy [AddCommGroup A] (P : Measure (A × B)) (w : AddChar A ℂ) : ℝ :=
  ∫ b, ‖posteriorDFT P w b‖ ^ 2 ∂P.snd

end LeakageSpectral.Shannon


