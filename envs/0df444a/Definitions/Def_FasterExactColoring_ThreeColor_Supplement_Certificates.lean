-- Prove2me | Definitions.Def_FasterExactColoring_ThreeColor_Supplement_Certificates
-- name    : FasterExactColoring_ThreeColor_Supplement_Certificates
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-15T20:50:14.005739+00:00
-- url     : https://prove2.me/theorems/807225af-d0f6-49b5-a0d3-d5d3ee9e19e1
-- title:
--   Exact randomized Appendix C data and both Appendix E certificates
-- statement:
--   The randomized three-color data retain the published structural matrix $A$, normalization row $u$, and first two exponent rows. Only the third row changes to
--   $$(\ln3,\ln2,\ln2,0,0,0,\ln2/6,\ln3-2\ln2),$$
--   with offset $\epsilon\ln2$ and $\epsilon=10^{-9}$. The exact rational certificate is $z=0.274458566$, $\eta=(0.881461989,0.052151678,0.066386333)$ and $\xi=(0.000000010,0.209344508,0,0.001110933,0.000277726,0.004006697,0.000000010)$.
--
--   Appendix E's $3\times11$ matrix maps the computed terminal counts to $(|S|,n_{K_3},n_{K_4})$. Its coefficient rows are exactly the logarithms of the reduction, CSP, tree and path factors, using $\psi=(0,1/2,1,2,10/3)$ and the source's $B_{m,i}(\beta)$ and $P_{m,i}$. The deterministic matrix uses $\beta=1.3204$ and the first three rows; the randomized matrix uses $\beta=1.3159$ and all four. Both source tables are stored as exact rationals, including $z$, all five scaled weights $\widehat\omega_j$, and the algorithm mixture weights. Recover $r=e^z$ and $\omega_j=\widehat\omega_j/z$, and put $\gamma=10^{-9}\ln3$.
--
--   The named certificate predicates request every linear, branching, and terminal inequality and the objective bounds
--   $$z+\eta^\top b_2\le0.274458567\le\ln1.3159,$$
--   $$e^{z_{\rm det}+\gamma}\le1.697425486\le1.6975,\qquad
--    e^{z_{\rm rand}+\gamma}\le1.693287132\le1.6933.$$
--   These predicates are unproved arithmetic obligations. Defining the tables never assumes feasibility, solves an optimization problem, or certifies an algorithm. No theorem in this supplement assumes any of these certificate predicates.
-- source:
--   Ryosuke Yamano, Tetsuo Shibuya, STOC 2027 submission #727 (October 2026), Appendices C–E, pp. 21–26 (PDF pp. 23–28)

import Mathlib
import Definitions.Def_FasterExactColoring_ThreeColor_FinalCertificate
import Definitions.Def_FasterExactColoring_ThreeColor_Supplement_Portfolio

set_option autoImplicit false

namespace FasterExactColoring.ThreeColor.Supplement

/-- Appendix C, kappa=2. The other rows are the published data, unchanged. -/
noncomputable def randomExponentMatrix : Matrix (Fin 3) (Fin 8) ℝ :=
  fun i j => if i.val = 2 then
    ![Real.log 3,Real.log 2,Real.log 2,0,0,0,Real.log 2/6,Real.log 3-2*Real.log 2] j
    else exponentMatrix i j

noncomputable def randomExponentOffset : Fin 3 → ℝ :=
  fun i => if i.val = 2 then finalEpsilon*Real.log 2 else exponentOffset i

noncomputable def randomDualZ : ℝ := 274458566/10^9
noncomputable def randomDualEta : Fin 3 → ℝ := ![881461989/10^9,52151678/10^9,66386333/10^9]
noncomputable def randomDualXi : Fin 7 → ℝ :=
  ![10/10^9,209344508/10^9,0,1110933/10^9,277726/10^9,4006697/10^9,10/10^9]

noncomputable def randomThreeCertificate : Prop :=
  (∀ i, 0 ≤ randomDualEta i) ∧ (∀ i, 0 ≤ randomDualXi i) ∧
  (∑ i, randomDualEta i) = 1 ∧
  (∀ j, (∑ i, randomDualEta i*randomExponentMatrix i j) ≤
    randomDualZ*normalizationRow j + ∑ i, randomDualXi i*constraintMatrix i j) ∧
  randomDualZ + (∑ i, randomDualEta i*randomExponentOffset i) ≤ 274458567/10^9 ∧
  (274458567/10^9 : ℝ) ≤ Real.log (13159/10000 : ℝ)

/-- Appendix E's mapping from the eleven computed counts. -/
def terminalMatrix : Matrix (Fin 3) (Fin 11) ℝ :=
  !![1,1,0,3,6,9,0,3,6,9,12;
     0,0,1,1,1,1,0,0,0,0,0;
     0,0,0,0,0,0,1,1,1,1,1]

noncomputable def Bentry (β : ℝ) (m i : ℕ) : ℝ :=
  Real.log m + ((m : ℝ)-1+3*i)*Real.log β

noncomputable def psi (i : ℕ) : ℝ :=
  if i = 0 then 0 else if i = 1 then 1/2 else if i = 2 then 1
  else if i = 3 then 2 else 10/3

noncomputable def Pentry (m i : ℕ) : ℝ := Real.log (Qentry i)+psi (m-i)*Real.log 3

noncomputable def rowThree (β : ℝ) : Fin 11 → ℝ :=
  ![Real.log β, Real.log β,
    Bentry β 3 0,Bentry β 3 1,Bentry β 3 2,Bentry β 3 3,
    Bentry β 4 0,Bentry β 4 1,Bentry β 4 2,Bentry β 4 3,Bentry β 4 4]

noncomputable def rowCSP : Fin 11 → ℝ :=
  ![Real.log 3/4,Real.log cspBase,
    Real.log (g 3 0),Real.log (g 3 1),Real.log (g 3 2),Real.log (g 3 3),
    Real.log (g 4 0),Real.log (g 4 1),Real.log (g 4 2),Real.log (g 4 3),Real.log (g 4 4)]

noncomputable def rowTree : Fin 11 → ℝ :=
  ![Real.log 24/4,0,Real.log 18,Real.log 18,Real.log 18,Real.log 18,
    Real.log 24,Real.log 24,Real.log 24,Real.log 24,Real.log 24]

noncomputable def rowPath : Fin 11 → ℝ :=
  ![Real.log 24/4,0,Pentry 3 0,Pentry 3 1,Pentry 3 2,Pentry 3 3,
    Pentry 4 0,Pentry 4 1,Pentry 4 2,Pentry 4 3,Pentry 4 4]

noncomputable def deterministicRows : Matrix (Fin 3) (Fin 11) ℝ :=
  ![rowThree (3301/2500),rowCSP,rowTree]
noncomputable def randomizedRows : Matrix (Fin 4) (Fin 11) ℝ :=
  ![rowThree (13159/10000),rowCSP,rowTree,rowPath]

/-- Ten exact rational coordinates, in the order printed in Appendix E. -/
noncomputable def deterministicData : Fin 10 → ℝ :=
  ![5291126816180365/10^16,4944314348773351/10^16,5291126816180365/10^16,
    2957156198800068/10^16,15714124563519097/10^16,18810074111165460/10^16,
    788417191536246/10^16,8811402533346064/10^16,400180275117690/10^16,0]

noncomputable def randomizedData : Fin 10 → ℝ :=
  ![5266716867458051/10^16,4928717407360532/10^16,5266716867458051/10^16,
    2925962315974430/10^16,15621902025983386/10^16,19480191762881393/10^16,
    2043107963374502/10^16,7611219494728269/10^16,69512075211995/10^16,
    276160466685234/10^16]

noncomputable def recoveredWeights (data : Fin 10 → ℝ) : Weights :=
  ⟨data 1/data 0,data 2/data 0,data 3/data 0,data 4/data 0,data 5/data 0⟩

noncomputable def finalGamma : ℝ := finalEpsilon*Real.log 3

/-- Data alone do not assert feasibility. These are proof obligations, not hypotheses
of any headline theorem and not fields of a presumed solver. -/
noncomputable def deterministicFourCertificate : Prop :=
  0 < deterministicData 0 ∧
  appendixD (Real.exp (deterministicData 0)) (recoveredWeights deterministicData) ∧
  dualComparison (Real.exp (deterministicData 0)) (recoveredWeights deterministicData)
    terminalMatrix deterministicRows (fun i => deterministicData ⟨i.val+6,by omega⟩) ∧
  Real.exp (deterministicData 0+finalGamma) ≤ 1697425486/10^9 ∧
  (1697425486/10^9 : ℝ) ≤ 679/400

noncomputable def randomizedFourCertificate : Prop :=
  0 < randomizedData 0 ∧
  appendixD (Real.exp (randomizedData 0)) (recoveredWeights randomizedData) ∧
  dualComparison (Real.exp (randomizedData 0)) (recoveredWeights randomizedData)
    terminalMatrix randomizedRows (fun i => randomizedData ⟨i.val+6,by omega⟩) ∧
  Real.exp (randomizedData 0+finalGamma) ≤ 1693287132/10^9 ∧
  (1693287132/10^9 : ℝ) ≤ 16933/10000

end FasterExactColoring.ThreeColor.Supplement


