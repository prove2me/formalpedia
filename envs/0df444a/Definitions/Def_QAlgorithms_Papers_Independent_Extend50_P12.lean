-- Prove2me | Definitions.Def_QAlgorithms_Papers_Independent_Extend50_P12
-- name    : QAlgorithms_Papers_Independent_Extend50_P12
-- status  : Definition
-- author  : @Gohan
-- created : 2026-10-29T19:47:46.901336+00:00
-- url     : https://prove2.me/theorems/097e5fe0-ec13-4dad-91c8-b7d8049763de
-- title:
--   Definitions for Positive maps from the walled Brauer algebra
-- statement:
--   The objects the formalized statements of *Positive maps from the walled Brauer algebra* (arXiv:2112.12738) are stated in. Each was checked against the paper by a blind read-back and a moderator.
--
--   - `LocalMatrix`: One-register matrix algebra, PDF p.2.
--   - `ComplexNonnegative`: Complex nonnegativity includes vanishing imaginary part, PDF pp.2-3.
--   - `tensorMatrices`: Ordered tensor product, in the fixed product basis, PDF p.2.
--   - `joinWords`: Join input and output basis words without changing their order, PDF p.2.
--   - `inputOutputTensor`: A tensor product across the cut r|m; the m-register factor is unrestricted, so it includes operators entangled across the output sites, PDF p.6, Eq.(36).
--   - `productInputContraction`: Unnormalized partial-trace contraction tr_inputs[P(X_1 ⊗ ... ⊗ X_r ⊗ I)], written entrywise; the input order is X_i(b_i,a_i), PDF pp.2,6, Eqs.(1),(34).
--   - `PositiveMap`: Positivity on all PSD inputs, without trace normalization, PDF p.2.
--   - `ComplexMultilinear`: Separate complex linearity, including arbitrary matrices as inputs, PDF p.2.
--   - `InputOutputBlockPositive`: Block positivity for 1|...|r|[r+1,...,r+m], in its equivalent PSD trace-pairing form. The whole output is one block; the complex pairing must be real, PDF pp.3,6, Eqs.(13),(36). No PSD or normalization premise is imposed on P.
--   - `transposeRegisterSet`: Ordinary, basis-dependent partial transpose, with zero-based site labels, PDF p.2, Eq.(4). There is no complex conjugation.
--   - `embedLeading`: Embed an operator on the leading s sites and identity on the remaining sites; the suffix Kronecker delta is explicit, PDF pp.8-9, Eq.(51).
--   - `permutation`: Physical permutation matrices, with sigma^{-1} on the word coordinates, exactly Eq.(2) and Eq.(A2), PDF pp.2,11.
--   - `contractionPairs`: Product of the k disjoint, partially transposed swaps in Eq.(A12), PDF p.12. Here N=a+2k and site a+j is paired with site N-1-j.
--   - `walledNormalization`: The normalization in Eq.(52), PDF p.9. Both dimensions are constructed: Specht dimensions are finranks of the regular Young ideals, and Schur multiplicities are finranks of the tensor Young images.
--   - `walledKernel`: The constructed maximal-productInputContraction-sector kernel, Eqs.(51),(52),(A11),(A12), PDF pp.8-9,11-12. The coset sum is written as the full S_(a+k) conjugation sum divided by |S_a|=a!: the core commutes with permutations of its first a sites. The P's are full character isotypic projectors from Eq.(A6), not Young images. Nothing here assumes positivity of this computed physical matrix.
--   - `walledMap`: Reindex the total system count as inputs plus outputs; Eq.(53)'s overloaded n is thus split into r inputs and r+m total sites, PDF p.9.
--   - `WernerDensity`: Density matrix premise of the tripartite section, PDF pp.2,5.
--   - `bcsWitness`: The qutrit witness P(1/4,-1/10), with unnormalized Bell operators obtained by partial transposition of physical swaps, PDF p.4, Eq.(25).
--   - `wernerPermutations`: The six permutation operators in Eq.(26), in the order id,(12),(23),(31), (123),(321); cycles follow the global Eq.(2) convention, PDF p.5.
--   - `wernerBasis`: R_+,R_-,R_0,R_1,R_2,R_3 as defined in Eq.(27), PDF p.5.
--   - `wernerFromCoefficients`: The matrix computed by Eq.(B3), PDF p.13; c has real entries ordered +, -, 0, 1, 2, 3. It is not an unrelated free density matrix.
--   - `correctedPermutationCoefficients`: Coefficients forced by Eq.(27). The printed alpha_2 in Eq.(B5) is corrected from c_+/6-c_minus/6-c_2/sqrt(3) to c_+/6-c_minus/6-c_1/3+c_2/sqrt(3), PDF pp.5,13.
--   - `example14Kernel`: The Example-14 projector constructed from the FIRST line of Eq.(56), PDF p.9, N=4,k=1,d=2. The symmetric two-site and (2,1) three-site isotypic projectors are exactly those in Eq.(55); gamma=1.
--   - `example14Map`: Identify the single output register with M_2, PDF p.9, Eq.(58).
--   - `example14Formula`: The explicitly ordered six products and three trace terms in Eq.(58), PDF p.9; transpose is ordinary matrix transpose.
--   - `reshuffleSites`: Reshuffling R_(ketSite,braSite) of Eq.(44), PDF p.7, with zero-based sites. Its coefficient action swaps the indicated ket and bra coordinates.
--   - `reshuffleTwo`: Two-site reshuffling of Eq.(6), PDF p.2: the first bra and second ket are interchanged. This is R_(2,1) in the later notation.
--   - `homogeneousTensorPair`: Two-factor ordered tensor product, PDF p.2.
--   - `leadingInput`: A single input followed by identities on n-1 sites, PDF pp.7-8.
--   - `orderedReshuffles`: Apply R_(n,n-1), then R_(n,n-2), down to R_(n,1), in that order, using zero-based internal labels. This is the precise ordered sequence of Eq.(46)/(C5), PDF pp.7,14. Its domain n>=2 excludes the printed site-0 endpoint.
--   - `rankOneThreeOutput`: The summed kernel sum_(k,l)|alpha,k,beta><k,l,l| in Eq.(45), PDF p.7.
--   - `tableSubsets`: The six nonempty proper subsets in Table I order 1,2,3,12,13,23, PDF p.13. Site numbers are converted to zero-based labels.
--   - `permutationExpansion`: Construct the matrix in Eqs.(26),(B4) from its six permutation coefficients, PDF pp.5,13. Physical matrices avoid small-d injectivity assumptions.
--   - `tripartiteF`: f_S from Eq.(29), with the unnormalized partial trace, PDF p.5.
--   - `tripartiteG`: g_S from Eq.(30), identifying the single output with M_d, PDF p.5.
--   - `tableF`: All six f rows of Table I, with labelled alpha coefficients and the exact product/reshuffling order retained, PDF p.13 (Example 3 is included).
--   - `tableG`: All six g rows of Table I, PDF p.13. Ordinary transpose and the labelled cycle contributions have exactly their printed order.
-- source:
--   Positive maps from the walled Brauer algebra, arXiv:2112.12738v3, https://arxiv.org/abs/2112.12738v3

import Mathlib
import Definitions.Def_QAlgorithms_Defs_SchurWeylDecomposition

noncomputable section

open scoped BigOperators Matrix ComplexOrder

namespace QAlgorithms.Papers.Independent.Extend50.P12

attribute [local instance] Classical.propDecidable

/-!
Reuse audit (PDF pp.2,3,6): basis labels and operator types below use Mathlib's
function spaces and `Matrix` directly; matrix units use `Matrix.single`.
The indexed frozen homonyms are different objects: Claimed50.P02.contraction
is a two-wire Bell operator; Claimed50.P37.contraction is a full Fock-space
Choi contraction with a transposed input; Claimed50.P49.BlockPositive tests
CP block matrices on arbitrary coupled vectors. Dependency50.P22.tensorTwo
is qubit-only, and Dependency50.P32.partialTranspose / Frontier18.P17.partialTranspose
transpose one factor of a bipartite product index. They cannot replace the
arbitrary-d product-input contraction, multipartite separable-block test,
homogeneous pair, or arbitrary register-set transpose defined here.
-/

/-- One-register matrix algebra, PDF p.2. -/
abbrev LocalMatrix (d : ℕ) := Matrix (Fin d) (Fin d) ℂ

/-- Complex nonnegativity includes vanishing imaginary part, PDF pp.2-3. -/
def ComplexNonnegative (z : ℂ) : Prop := z.im = 0 ∧ 0 ≤ z.re

/-- Ordered tensor product, in the fixed product basis, PDF p.2. -/
def tensorMatrices {d r : ℕ} (X : Fin r → LocalMatrix d) : Matrix (Fin r → Fin d) (Fin r → Fin d) ℂ :=
  fun x y => ∏ i, X i (x i) (y i)

/-- Join input and output basis words without changing their order, PDF p.2. -/
def joinWords {d r m : ℕ} (x : (Fin r → Fin d)) (y : (Fin m → Fin d)) : (Fin (r + m) → Fin d) :=
  Fin.addCases x y

/-- A tensor product across the cut r|m; the m-register factor is unrestricted,
so it includes operators entangled across the output sites, PDF p.6, Eq.(36). -/
def inputOutputTensor {d r m : ℕ} (X : Fin r → LocalMatrix d)
    (C : Matrix (Fin m → Fin d) (Fin m → Fin d) ℂ) : Matrix (Fin (r + m) → Fin d) (Fin (r + m) → Fin d) ℂ :=
  fun x y =>
    (∏ i : Fin r, X i (x (Fin.castAdd m i)) (y (Fin.castAdd m i))) *
      C (fun j => x (Fin.natAdd r j)) (fun j => y (Fin.natAdd r j))

/-- Unnormalized partial-trace contraction tr_inputs[P(X_1 ⊗ ... ⊗ X_r ⊗ I)],
written entrywise; the input order is X_i(b_i,a_i), PDF pp.2,6, Eqs.(1),(34). -/
def productInputContraction {d r m : ℕ} (P : Matrix (Fin (r + m) → Fin d) (Fin (r + m) → Fin d) ℂ)
    (X : Fin r → LocalMatrix d) : Matrix (Fin m → Fin d) (Fin m → Fin d) ℂ :=
  fun y z => ∑ a : (Fin r → Fin d), ∑ b : (Fin r → Fin d),
    P (joinWords a y) (joinWords b z) * ∏ i, X i (b i) (a i)

/-- Positivity on all PSD inputs, without trace normalization, PDF p.2. -/
def PositiveMap {d r m : ℕ} (f : (Fin r → LocalMatrix d) → Matrix (Fin m → Fin d) (Fin m → Fin d) ℂ) : Prop :=
  ∀ X, (∀ i, (X i).PosSemidef) → (f X).PosSemidef

/-- Separate complex linearity, including arbitrary matrices as inputs, PDF p.2. -/
def ComplexMultilinear {d r m : ℕ}
    (f : (Fin r → LocalMatrix d) → Matrix (Fin m → Fin d) (Fin m → Fin d) ℂ) : Prop :=
  (∀ (i : Fin r) (X : Fin r → LocalMatrix d) (A B : LocalMatrix d),
    f (Function.update X i (A + B)) =
    f (Function.update X i A) + f (Function.update X i B)) ∧
  (∀ (i : Fin r) (X : Fin r → LocalMatrix d) (c : ℂ) (A : LocalMatrix d),
    f (Function.update X i (c • A)) = c • f (Function.update X i A))

/-- Block positivity for 1|...|r|[r+1,...,r+m], in its equivalent PSD trace-pairing
form. The whole output is one block; the complex pairing must be real, PDF
pp.3,6, Eqs.(13),(36). No PSD or normalization premise is imposed on P. -/
def InputOutputBlockPositive {d r m : ℕ} (P : Matrix (Fin (r + m) → Fin d) (Fin (r + m) → Fin d) ℂ) : Prop :=
  ∀ X, (∀ i, (X i).PosSemidef) → ∀ C : Matrix (Fin m → Fin d) (Fin m → Fin d) ℂ, C.PosSemidef →
    ComplexNonnegative (Matrix.trace (P * inputOutputTensor X C))

/-- Ordinary, basis-dependent partial transpose, with zero-based site labels,
PDF p.2, Eq.(4). There is no complex conjugation. -/
def transposeRegisterSet {d n : ℕ} (S : Finset (Fin n)) (P : Matrix (Fin n → Fin d) (Fin n → Fin d) ℂ) :
    Matrix (Fin n → Fin d) (Fin n → Fin d) ℂ :=
  fun x y => P (fun i => if i ∈ S then y i else x i)
    (fun i => if i ∈ S then x i else y i)

/-- Embed an operator on the leading s sites and identity on the remaining
sites; the suffix Kronecker delta is explicit, PDF pp.8-9, Eq.(51). -/
def embedLeading {d s n : ℕ} (h : s ≤ n) (P : Matrix (Fin s → Fin d) (Fin s → Fin d) ℂ) : Matrix (Fin n → Fin d) (Fin n → Fin d) ℂ :=
  fun x y => P (fun i => x ⟨i.val, lt_of_lt_of_le i.isLt h⟩)
    (fun i => y ⟨i.val, lt_of_lt_of_le i.isLt h⟩) *
      if ∀ i : Fin n, s ≤ i.val → x i = y i then 1 else 0

/-- Physical permutation matrices, with sigma^{-1} on the word coordinates,
exactly Eq.(2) and Eq.(A2), PDF pp.2,11. -/
abbrev permutation (d n : ℕ) (pi : Equiv.Perm (Fin n)) : Matrix (Fin n → Fin d) (Fin n → Fin d) ℂ :=
  QAlgorithms.Schur.tensorPermutation d n pi

/-- Product of the k disjoint, partially transposed swaps in Eq.(A12), PDF p.12.
Here N=a+2k and site a+j is paired with site N-1-j. -/
def contractionPairs (d a k : ℕ) : Matrix (Fin (a + 2 * k) → Fin d) (Fin (a + 2 * k) → Fin d) ℂ :=
  (List.ofFn fun j : Fin k =>
    let left : Fin (a + 2 * k) := ⟨a + j.val, by omega⟩
    let right : Fin (a + 2 * k) := ⟨a + 2 * k - 1 - j.val, by omega⟩
    transposeRegisterSet {right} (permutation d (a + 2 * k) (Equiv.swap left right))).prod

/-- The normalization in Eq.(52), PDF p.9. Both dimensions are constructed:
Specht dimensions are finranks of the regular Young ideals, and Schur
multiplicities are finranks of the tensor Young images. -/
def walledNormalization {d a k : ℕ} (alpha : QAlgorithms.Schur.Partition d a)
    (mu : QAlgorithms.Schur.Partition d (a + k)) : ℂ :=
  (k.factorial : ℂ) * ((a + k).choose k : ℂ) *
    (Module.finrank ℂ (QAlgorithms.Schur.schurModule mu) : ℂ) *
    (Module.finrank ℂ (QAlgorithms.Schur.spechtSpace alpha) : ℂ) /
    ((Module.finrank ℂ (QAlgorithms.Schur.schurModule alpha) : ℂ) *
      (Module.finrank ℂ (QAlgorithms.Schur.spechtSpace mu) : ℂ))

/-- The constructed maximal-productInputContraction-sector kernel, Eqs.(51),(52),(A11),(A12),
PDF pp.8-9,11-12. The coset sum is written as the full S_(a+k) conjugation sum
divided by |S_a|=a!: the core commutes with permutations of its first a sites.
The P's are full character isotypic projectors from Eq.(A6), not Young images.
Nothing here assumes positivity of this computed physical matrix. -/
def walledKernel {d : ℕ} (a k : ℕ) (alpha : QAlgorithms.Schur.Partition d a)
    (mu : QAlgorithms.Schur.Partition d (a + k)) : Matrix (Fin (a + 2 * k) → Fin d) (Fin (a + 2 * k) → Fin d) ℂ :=
  (walledNormalization alpha mu)⁻¹ •
    (embedLeading (by omega : a + k ≤ a + 2 * k)
      (QAlgorithms.Schur.isotypicProjector mu) *
      ((a.factorial : ℂ)⁻¹ •
        ∑ eta : Equiv.Perm (Fin (a + k)),
          embedLeading (by omega : a + k ≤ a + 2 * k)
            (permutation d (a + k) eta⁻¹) *
          (embedLeading (by omega : a ≤ a + 2 * k)
            (QAlgorithms.Schur.isotypicProjector alpha) * contractionPairs d a k) *
          embedLeading (by omega : a + k ≤ a + 2 * k)
            (permutation d (a + k) eta)))

/-- Reindex the total system count as inputs plus outputs; Eq.(53)'s overloaded
n is thus split into r inputs and r+m total sites, PDF p.9. -/
def walledMap {d a k r m : ℕ} (h : r + m = a + 2 * k)
    (alpha : QAlgorithms.Schur.Partition d a)
    (mu : QAlgorithms.Schur.Partition d (a + k))
    (X : Fin r → LocalMatrix d) : Matrix (Fin m → Fin d) (Fin m → Fin d) ℂ :=
  productInputContraction (h.symm ▸ walledKernel a k alpha mu) X

/-- Density matrix premise of the tripartite section, PDF pp.2,5. -/
def WernerDensity {d : ℕ} (rho : Matrix (Fin 3 → Fin d) (Fin 3 → Fin d) ℂ) : Prop :=
  rho.PosSemidef ∧ Matrix.trace rho = 1 ∧
    ∀ U : Matrix.unitaryGroup (Fin d) ℂ,
      let T := tensorMatrices (fun _ : Fin 3 => (U : LocalMatrix d))
      T * rho * T.conjTranspose = rho

/-- The qutrit witness P(1/4,-1/10), with unnormalized Bell operators obtained
by partial transposition of physical swaps, PDF p.4, Eq.(25). -/
def bcsWitness : Matrix (Fin 3 → Fin 3) (Fin 3 → Fin 3) ℂ :=
  transposeRegisterSet {1} (permutation 3 3 (Equiv.swap 0 1)) +
    permutation 3 3 (Equiv.swap 0 2) + (1 / 4 : ℂ) • 1 -
    (1 / 10 : ℂ) • transposeRegisterSet {1} (permutation 3 3 (Equiv.swap 1 2))

/-- The six permutation operators in Eq.(26), in the order id,(12),(23),(31),
(123),(321); cycles follow the global Eq.(2) convention, PDF p.5. -/
def wernerPermutations (d : ℕ) : Fin 6 → Matrix (Fin 3 → Fin d) (Fin 3 → Fin d) ℂ :=
  ![1, permutation d 3 (Equiv.swap 0 1), permutation d 3 (Equiv.swap 1 2),
    permutation d 3 (Equiv.swap 0 2),
    permutation d 3 (Equiv.swap 0 1 * Equiv.swap 1 2),
    permutation d 3 (Equiv.swap 1 2 * Equiv.swap 0 1)]

/-- R_+,R_-,R_0,R_1,R_2,R_3 as defined in Eq.(27), PDF p.5. -/
def wernerBasis (d : ℕ) : Fin 6 → Matrix (Fin 3 → Fin d) (Fin 3 → Fin d) ℂ :=
  let V := wernerPermutations d
  ![(1 / 6 : ℂ) • (V 0 + V 1 + V 2 + V 3 + V 4 + V 5),
    (1 / 6 : ℂ) • (V 0 - V 1 - V 2 - V 3 + V 4 + V 5),
    (1 / 3 : ℂ) • ((2 : ℂ) • V 0 - V 4 - V 5),
    (1 / 3 : ℂ) • ((2 : ℂ) • V 2 - V 3 - V 1),
    ((Real.sqrt 3 : ℂ)⁻¹) • (V 1 - V 3),
    (Complex.I / (Real.sqrt 3 : ℂ)) • (V 4 - V 5)]

/-- The matrix computed by Eq.(B3), PDF p.13; c has real entries ordered
+, -, 0, 1, 2, 3. It is not an unrelated free density matrix. -/
def wernerFromCoefficients (d : ℕ) (c : Fin 6 → ℝ) : Matrix (Fin 3 → Fin d) (Fin 3 → Fin d) ℂ :=
  ∑ j, (c j : ℂ) • wernerBasis d j

/-- Coefficients forced by Eq.(27). The printed alpha_2 in Eq.(B5) is corrected
from c_+/6-c_minus/6-c_2/sqrt(3) to
c_+/6-c_minus/6-c_1/3+c_2/sqrt(3), PDF pp.5,13. -/
def correctedPermutationCoefficients (c : Fin 6 → ℝ) : Fin 6 → ℂ :=
  let p : ℂ := c 0
  let q : ℂ := c 1
  let z : ℂ := c 2
  let x : ℂ := c 3
  let y : ℂ := c 4
  let t : ℂ := c 5
  ![p / 6 + q / 6 + 2 * z / 3,
    p / 6 - q / 6 - x / 3 + y / (Real.sqrt 3 : ℂ),
    p / 6 - q / 6 + 2 * x / 3,
    p / 6 - q / 6 - x / 3 - y / (Real.sqrt 3 : ℂ),
    p / 6 + q / 6 - z / 3 + Complex.I * t / (Real.sqrt 3 : ℂ),
    p / 6 + q / 6 - z / 3 - Complex.I * t / (Real.sqrt 3 : ℂ)]

/-- The Example-14 projector constructed from the FIRST line of Eq.(56),
PDF p.9, N=4,k=1,d=2. The symmetric two-site and (2,1) three-site isotypic
projectors are exactly those in Eq.(55); gamma=1. -/
def example14Kernel : Matrix (Fin 4 → Fin 2) (Fin 4 → Fin 2) ℂ :=
  let pa := (1 / 2 : ℂ) • (1 + permutation 2 4 (Equiv.swap 0 1))
  let cycle := permutation 2 4 (Equiv.swap 0 1 * Equiv.swap 1 2)
  let inverseCycle := permutation 2 4 (Equiv.swap 1 2 * Equiv.swap 0 1)
  let pm := (1 / 3 : ℂ) • ((2 : ℂ) • 1 - cycle - inverseCycle)
  let sigma := transposeRegisterSet {3} (permutation 2 4 (Equiv.swap 2 3))
  let v23 := permutation 2 4 (Equiv.swap 1 2)
  let v13 := permutation 2 4 (Equiv.swap 0 2)
  pm * (pa * sigma + v23 * pa * sigma * v23 + v13 * pa * sigma * v13)

/-- Identify the single output register with M_2, PDF p.9, Eq.(58). -/
def example14Map (A B C : LocalMatrix 2) : LocalMatrix 2 :=
  let M := productInputContraction (r := 3) (m := 1) example14Kernel ![A, B, C]
  fun i j => M (fun _ => i) (fun _ => j)

/-- The explicitly ordered six products and three trace terms in Eq.(58),
PDF p.9; transpose is ordinary matrix transpose. -/
def example14Formula (A B C : LocalMatrix 2) : LocalMatrix 2 :=
  (-1 / 6 : ℂ) • ((A * C * B).transpose + (B * A * C).transpose +
    (C * B * A).transpose + (A * B * C).transpose +
    (B * C * A).transpose + (C * A * B).transpose) +
  (1 / 3 : ℂ) • ((Matrix.trace B * Matrix.trace C) • A.transpose +
    (Matrix.trace A * Matrix.trace C) • B.transpose +
    (Matrix.trace A * Matrix.trace B) • C.transpose)

/-- Sanity: transposing every site is ordinary transpose, without conjugation. -/
example {d n : ℕ} (P : Matrix (Fin n → Fin d) (Fin n → Fin d) ℂ) :
    transposeRegisterSet Finset.univ P = P.transpose := by
  funext x y
  simp [transposeRegisterSet, Matrix.transpose_apply]

/-- Sanity: no contractions means the identity on the remaining sites. -/
example (d a : ℕ) : contractionPairs d a 0 = 1 := by
  simp [contractionPairs]

/-- Sanity: the first permutation is the physical identity. -/
example (d : ℕ) : wernerPermutations d 0 = 1 := by
  rfl

/-- Sanity: the corrected (12) coefficient includes the R_1 contribution. -/
example (c : Fin 6 → ℝ) : correctedPermutationCoefficients c 1 =
    (c 0 : ℂ) / 6 - (c 1 : ℂ) / 6 - (c 3 : ℂ) / 3 +
      (c 4 : ℂ) / (Real.sqrt 3 : ℂ) := by
  rfl

/-- Reshuffling R_(ketSite,braSite) of Eq.(44), PDF p.7, with zero-based sites.
Its coefficient action swaps the indicated ket and bra coordinates. -/
def reshuffleSites {d n : ℕ} (ketSite braSite : Fin n) (P : Matrix (Fin n → Fin d) (Fin n → Fin d) ℂ) :
    Matrix (Fin n → Fin d) (Fin n → Fin d) ℂ :=
  fun x y => P (Function.update x ketSite (y braSite))
    (Function.update y braSite (x ketSite))

/-- Two-site reshuffling of Eq.(6), PDF p.2: the first bra and second ket
are interchanged. This is R_(2,1) in the later notation. -/
def reshuffleTwo {d : ℕ} (P : Matrix (Fin 2 → Fin d) (Fin 2 → Fin d) ℂ) : Matrix (Fin 2 → Fin d) (Fin 2 → Fin d) ℂ :=
  reshuffleSites 1 0 P

/-- Two-factor ordered tensor product, PDF p.2. -/
def homogeneousTensorPair {d : ℕ} (A B : LocalMatrix d) : Matrix (Fin 2 → Fin d) (Fin 2 → Fin d) ℂ :=
  tensorMatrices ![A, B]

/-- A single input followed by identities on n-1 sites, PDF pp.7-8. -/
def leadingInput {d : ℕ} (n : ℕ) (hn : 0 < n) (A : LocalMatrix d) : Matrix (Fin n → Fin d) (Fin n → Fin d) ℂ :=
  embedLeading (by omega : 1 ≤ n) (tensorMatrices ![A])

/-- Apply R_(n,n-1), then R_(n,n-2), down to R_(n,1), in that order,
using zero-based internal labels. This is the precise ordered sequence of
Eq.(46)/(C5), PDF pp.7,14. Its domain n>=2 excludes the printed site-0 endpoint. -/
def orderedReshuffles {d : ℕ} (n : ℕ) (hn : 2 ≤ n) (P : Matrix (Fin n → Fin d) (Fin n → Fin d) ℂ) :
    Matrix (Fin n → Fin d) (Fin n → Fin d) ℂ :=
  ((List.finRange (n - 1)).reverse).foldl
    (fun M j => reshuffleSites ⟨n - 1, by omega⟩ ⟨j.val, by omega⟩ M) P

/-- The summed kernel sum_(k,l)|alpha,k,beta><k,l,l| in Eq.(45), PDF p.7. -/
def rankOneThreeOutput {d : ℕ} (alpha beta : Fin d) : Matrix (Fin 3 → Fin d) (Fin 3 → Fin d) ℂ :=
  fun x y => if x 0 = alpha ∧ x 2 = beta ∧ x 1 = y 0 ∧ y 1 = y 2 then 1 else 0

/-- The six nonempty proper subsets in Table I order 1,2,3,12,13,23,
PDF p.13. Site numbers are converted to zero-based labels. -/
def tableSubsets : Fin 6 → Finset (Fin 3) :=
  ![{0}, {1}, {2}, {0, 1}, {0, 2}, {1, 2}]

/-- Construct the matrix in Eqs.(26),(B4) from its six permutation coefficients,
PDF pp.5,13. Physical matrices avoid small-d injectivity assumptions. -/
def permutationExpansion (d : ℕ) (alpha : Fin 6 → ℂ) : Matrix (Fin 3 → Fin d) (Fin 3 → Fin d) ℂ :=
  ∑ j, alpha j • wernerPermutations d j

/-- f_S from Eq.(29), with the unnormalized partial trace, PDF p.5. -/
def tripartiteF {d : ℕ} (rho : Matrix (Fin 3 → Fin d) (Fin 3 → Fin d) ℂ) (S : Finset (Fin 3))
    (A : LocalMatrix d) : Matrix (Fin 2 → Fin d) (Fin 2 → Fin d) ℂ :=
  productInputContraction (r := 1) (m := 2) (transposeRegisterSet S rho) ![A]

/-- g_S from Eq.(30), identifying the single output with M_d, PDF p.5. -/
def tripartiteG {d : ℕ} (rho : Matrix (Fin 3 → Fin d) (Fin 3 → Fin d) ℂ) (S : Finset (Fin 3))
    (A B : LocalMatrix d) : LocalMatrix d :=
  let M := productInputContraction (r := 2) (m := 1) (transposeRegisterSet S rho) ![A, B]
  fun i j => M (fun _ => i) (fun _ => j)

/-- All six f rows of Table I, with labelled alpha coefficients and the exact
product/reshuffling order retained, PDF p.13 (Example 3 is included). -/
def tableF {d : ℕ} (a : Fin 6 → ℂ) (A : LocalMatrix d) : Fin 6 → Matrix (Fin 2 → Fin d) (Fin 2 → Fin d) ℂ :=
  let I : LocalMatrix d := 1
  let II := homogeneousTensorPair I I
  let R := reshuffleTwo
  let T := transposeRegisterSet ({1} : Finset (Fin 2))
  let Q := A.transpose
  ![ (a 0 * Matrix.trace A) • II + a 1 • homogeneousTensorPair Q I +
       (a 2 * Matrix.trace A) • T (R II) + a 3 • homogeneousTensorPair I Q +
       a 4 • T (R (homogeneousTensorPair Q I)) + a 5 • T (R (homogeneousTensorPair I A)),
     (a 0 * Matrix.trace A) • II + a 1 • homogeneousTensorPair Q I +
       (a 2 * Matrix.trace A) • R II + a 3 • homogeneousTensorPair I A +
       a 4 • R (homogeneousTensorPair I A) + a 5 • R (homogeneousTensorPair Q I),
     (a 0 * Matrix.trace A) • II + a 1 • homogeneousTensorPair A I +
       (a 2 * Matrix.trace A) • R II + a 3 • homogeneousTensorPair I Q +
       a 4 • R (homogeneousTensorPair A I) + a 5 • R (homogeneousTensorPair I Q),
     (a 0 * Matrix.trace A) • II + a 1 • homogeneousTensorPair A I +
       (a 2 * Matrix.trace A) • R II + a 3 • homogeneousTensorPair I Q +
       a 4 • R (homogeneousTensorPair I Q) + a 5 • R (homogeneousTensorPair A I),
     (a 0 * Matrix.trace A) • II + a 1 • homogeneousTensorPair Q I +
       (a 2 * Matrix.trace A) • R II + a 3 • homogeneousTensorPair I A +
       a 4 • R (homogeneousTensorPair Q I) + a 5 • R (homogeneousTensorPair I A),
     (a 0 * Matrix.trace A) • II + a 1 • homogeneousTensorPair Q I +
       (a 2 * Matrix.trace A) • T (R II) + a 3 • homogeneousTensorPair I Q +
       a 4 • T (R (homogeneousTensorPair I A)) + a 5 • T (R (homogeneousTensorPair Q I)) ]

/-- All six g rows of Table I, PDF p.13. Ordinary transpose and the labelled
cycle contributions have exactly their printed order. -/
def tableG {d : ℕ} (a : Fin 6 → ℂ) (A B : LocalMatrix d) : Fin 6 → LocalMatrix d :=
  let I : LocalMatrix d := 1
  let Q := A.transpose
  let Z := B.transpose
  let c := (a 0 * Matrix.trace A * Matrix.trace B) • I
  ![c + (a 1 * Matrix.trace (Q * B)) • I +
       (a 2 * Matrix.trace A) • B + (a 3 * Matrix.trace B) • Q +
       a 4 • (B * Q) + a 5 • (Q * B),
    c + (a 1 * Matrix.trace (A * Z)) • I +
       (a 2 * Matrix.trace A) • Z + (a 3 * Matrix.trace B) • A +
       a 4 • (Z * A) + a 5 • (A * Z),
    c + (a 1 * Matrix.trace (A * B)) • I +
       (a 2 * Matrix.trace A) • Z + (a 3 * Matrix.trace B) • Q +
       a 4 • (Q * Z) + a 5 • (Z * Q),
    c + (a 1 * Matrix.trace (Q * Z)) • I +
       (a 2 * Matrix.trace A) • Z + (a 3 * Matrix.trace B) • Q +
       a 4 • (Z * Q) + a 5 • (Q * Z),
    c + (a 1 * Matrix.trace (Q * B)) • I +
       (a 2 * Matrix.trace A) • Z + (a 3 * Matrix.trace B) • A +
       a 4 • (A * Z) + a 5 • (Z * A),
    c + (a 1 * Matrix.trace (Q * B)) • I +
       (a 2 * Matrix.trace A) • B + (a 3 * Matrix.trace B) • Q +
       a 4 • (Q * B) + a 5 • (B * Q)]

end QAlgorithms.Papers.Independent.Extend50.P12


