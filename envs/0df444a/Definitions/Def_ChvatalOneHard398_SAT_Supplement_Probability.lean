-- Prove2me | Definitions.Def_ChvatalOneHard398_SAT_Supplement_Probability
-- name    : ChvatalOneHard398_SAT_Supplement_Probability
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-15T18:20:09.670934+00:00
-- url     : https://prove2.me/theorems/68801b89-ab4b-4d36-a38a-77ad864da794
-- title:
--   LWE laws, finite-precision sampling and eventual advantage
-- statement:
--   Entries of $A$ and the secret $s$ are independent uniform residues, and error coordinates have an arbitrary common law $\chi$ on $\mathbb Z$. The LWE target is $(A^Ts+e)\bmod q$; the uniform target is independent of $A$. Their unconditioned equal mixture defines the input laws. The error law $\bar\Psi_\alpha$ is nearest-integer rounding of a real normal with mean zero and standard deviation $\alpha q/\sqrt{2\pi}$, before reduction modulo $q$.
--
--   The ideal parallelepiped and formula laws are the pushforwards of these mixtures through the specified constructions. Their rates are
--   $$\alpha_{12}=\frac1{200n^2k^2\log n},\qquad
--   \alpha_{29}=\frac1{200n^{3/2}k^{5/2}\log n}.$$
--   An effective sampler takes unary dimension $n$, binary modulus $q$ and unary precision $\ell$. One fixed polynomial-time randomized machine approximates the ideal law within $2^{-\ell}$ on every event. Its guarantee also bounds by $2^{-\ell}$ the change in success probability of every test with a fresh tape. Thus the ideal Gaussian is retained and finite numerical error is accounted for quantitatively.
--
--   An average-case solver has eventual mixture success at least $1/2+n^{-c}$ for some fixed $c>0$. A decision-LWE solver has an eventual difference of output-one probabilities at least $n^{-c}$. Both algorithms and polynomial bounds are uniform over dimensions. The modulus is an explicit input parameter, allowing every prime family in $[n^3,2n^3]$, without a computability restriction on the externally chosen family. Coefficient bounds apply to actual integral matrix and right-hand-side data.
-- source:
--   Alberto Del Pia, 0/1 integer programming over polytopes of Chvátal rank one is as hard as lattice problems, STOC 2027 submission #398 (October 2026), p.9, 14–16, 29–31, §2, Proposition 11, Theorems 12 and 29. https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/398.pdf

import Mathlib
import Definitions.Def_ChvatalOneHard398_SAT_Supplement_Algorithms
import Definitions.Def_ChvatalOneHard398_SAT_Supplement_Random

namespace ChvatalOneHard398.SAT.Supplement
open scoped BigOperators
open MeasureTheory ProbabilityTheory

/-- A total finite uniform law, with raw q=0 assigned the deterministic default zero. -/
noncomputable def uniformResidue (q : ℕ) : PMF ℤ :=
  if h : 0 < q then
    letI : NeZero q := ⟨Nat.ne_of_gt h⟩
    (PMF.uniformOfFintype (Fin q)).map (fun i => (i.val : ℤ))
  else PMF.pure 0

noncomputable def iid {A : Type} (μ : PMF A) : (d : ℕ) → PMF (Fin d → A)
  | 0 => PMF.pure (fun i => Fin.elim0 i)
  | d+1 => μ.bind fun x => (iid μ d).map (Fin.cons x)

noncomputable def matrixLaw (n m q : ℕ) : PMF AryMatrix :=
  (iid (iid (uniformResidue q) m) n).map fun A => ⟨n,m,q,A⟩

noncomputable def uniformLaw (n m q : ℕ) : PMF AryInput :=
  (iid (iid (uniformResidue q) m) n).bind fun A =>
    (iid (uniformResidue q) m).map fun t => ⟨⟨n,m,q,A⟩,t⟩

noncomputable def lweLaw (n m q : ℕ) (χ : PMF ℤ) : PMF AryInput :=
  (iid (iid (uniformResidue q) m) n).bind fun A =>
    (iid (uniformResidue q) n).bind fun s =>
      (iid χ m).map fun e =>
        ⟨⟨n,m,q,A⟩,fun j => ((∑ i, A i j*s i)+e j) % (q : ℤ)⟩

noncomputable def mixtureLaw (n m q : ℕ) (χ : PMF ℤ) : PMF AryInput :=
  (PMF.uniformOfFintype Bool).bind fun b =>
    if b then lweLaw n m q χ else uniformLaw n m q

/-- Rounding is performed on a real normal before modular reduction; half-integer ties
are rounded upwards, an event of probability zero for positive alpha and q. -/
noncomputable def roundedGaussian (α : ℝ) (q : ℕ) : PMF ℤ := by
  let σ := α * q / Real.sqrt (2 * Real.pi)
  let μ := gaussianReal 0 (⟨σ^2, sq_nonneg σ⟩ : NNReal)
  haveI : IsProbabilityMeasure μ := by
    exact ProbabilityTheory.instIsProbabilityMeasureGaussianReal 0 _
  have hm : Measurable (fun x : ℝ => (⌊x+(1/2 : ℝ)⌋ : ℤ)) := by fun_prop
  let ν := μ.map (fun x : ℝ => (⌊x+(1/2 : ℝ)⌋ : ℤ))
  haveI : IsProbabilityMeasure ν := μ.isProbabilityMeasure_map hm.aemeasurable
  exact ν.toPMF

noncomputable def alpha12 (n q : ℕ) : ℝ :=
  1 / (200 * (n : ℝ)^2 * (bits q : ℝ)^2 * Real.log n)

noncomputable def alpha29 (n q : ℕ) : ℝ :=
  1 / (200 * (n : ℝ)^(3/2 : ℝ) * (bits q : ℝ)^(5/2 : ℝ) * Real.log n)

noncomputable def paraLaw (n q : ℕ) : PMF ParaInput :=
  (mixtureLaw n (samples n q) q (roundedGaussian (alpha12 n q) q)).map toPara

noncomputable def formulaLaw (n q : ℕ) : PMF Formula :=
  (mixtureLaw n (samples n q) q (roundedGaussian (alpha29 n q) q)).map toFormula

/-- Accuracy and dimension are unary, the modulus binary; all data have honest bit encodings. -/
def encSampler (z : ℕ × ℕ × ℕ) : List OnlineCRS.Combine.Sym :=
  frame (List.replicate z.1 1) ++ frame (OnlineCRS.Combine.encNat z.2.1) ++
  List.replicate z.2.2 1

def primeRange (n q : ℕ) : Prop := q.Prime ∧ n^3 ≤ q ∧ q ≤ 2*n^3

/-- Effective sampling to any requested total-variation accuracy. The ideal law stays
unchanged. The last conjunct records quantitative transfer for every randomized test,
including its fresh independent tape; it is a conclusion, not a hypothesis on a sampler. -/
noncomputable def SamplableFrom {O : Type} (eo : O → List OnlineCRS.Combine.Sym)
    (N : ℕ) (D : ℕ → ℕ → PMF O) : Prop :=
  ∃ S : RandomAlg (ℕ × ℕ × ℕ) O, IsPolyRandom encSampler eo S ∧
    ∀ n q l, N ≤ n → primeRange n q →
      (∀ P : O → Prop,
        |prob (randomLaw encSampler S (n,q,l)) P - prob (D n q) P| ≤ (2 : ℝ)^(-(l : ℤ))) ∧
      (∀ A : RandomAlg O Bool, ∀ P : O → Prop,
        |success eo A (randomLaw encSampler S (n,q,l)) P - success eo A (D n q) P| ≤
          (2 : ℝ)^(-(l : ℤ)))

noncomputable def SolvesLWE (α : ℕ → ℕ → ℝ) (q : ℕ → ℕ) : Prop :=
  ∃ A : RandomAlg AryInput Bool, IsPolyRandom encAry encBool A ∧
    ∃ c : ℝ, 0 < c ∧ ∃ N : ℕ, ∀ n, N ≤ n →
      (n : ℝ)^(-c) ≤
        |outputOne encAry A (lweLaw n (samples n (q n)) (q n)
            (roundedGaussian (α n (q n)) (q n))) -
          outputOne encAry A (uniformLaw n (samples n (q n)) (q n))|

noncomputable def averageAdvantage {I : Type} (ei : I → List OnlineCRS.Combine.Sym)
    (A : RandomAlg I Bool) (D : ℕ → ℕ → PMF I) (q : ℕ → ℕ) (P : I → Prop) : Prop :=
  ∃ c : ℝ, 0 < c ∧ ∃ N : ℕ, ∀ n, N ≤ n →
    1/2 + (n : ℝ)^(-c) ≤ success ei A (D n (q n)) P

noncomputable def smallCoefficients (q : ℕ) (Q : ParaInput) : Prop :=
  Q.Valid ∧
  (∀ i j, ∃ b : ℤ, Q.B i j = b ∧ |b| < 2*(q : ℤ)) ∧
  (∀ i, ∃ u v : ℤ, Q.t i + Q.r = u ∧ -Q.t i + Q.r = v ∧
    |u| < 2*(q : ℤ) ∧ |v| < 2*(q : ℤ))

end ChvatalOneHard398.SAT.Supplement


