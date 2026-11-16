-- Prove2me | Definitions.Def_AggregatedCodeTesting_Testing_Supplement_Algebra
-- name    : AggregatedCodeTesting_Testing_Supplement_Algebra
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-15T11:28:18.130084+00:00
-- url     : https://prove2.me/theorems/fbd155ea-b6e4-4e47-9211-d11c6fcc7d84
-- title:
--   Supplement — rank-three family, deterministic witness selection, moment decoder and profile-recovery risk
-- statement:
--   Fix a binary linear code $C\le\mathbb F_2^m$. The observation law $P_\ell$, block-coset profile $T_C(\ell)$, Krawtchouk products $\psi_\nu$, formal logarithm and detection orders are the published base definitions, reused unchanged.
--
--   For $k\ge1$, define $\alpha=1100\,0^k$, $\beta=0011\,0^k$, $\gamma=1010\,1^k$, $D_k=\operatorname{span}\{\alpha,\beta,\gamma\}$ and $C_k=D_k^\perp$. Orthogonality is the ordinary binary dot product. The character $A=\alpha+\beta$ and exponent vector $(1,1,1,1,2,\ldots,2)$ are actual functions of $k$.
--
--   For a block $D$, let $Q_D=\mathbb F_2^D/C_D$, $q_D=|Q_D|$ and $d_D=\max\{|A|:A\in C_D^\perp\}$. Representatives are the least binary-number words of each coset, with zeros outside $D$. The polynomial used in Appendix B is
--
--   $$F_A=\prod_{\chi_A(\sigma)=1}g_\sigma-\prod_{\chi_A(\sigma)=-1}g_\sigma.$$
--
--   Set $D_0=d_Dq_D/2$. Among nonzero coefficients choose first the least total degree, then the least base-$(D_0+1)$ numerical monomial code. Store its exponent $\nu_A$ and $b_A=[z^{\nu_A}]F_A/q_D$. This is a finite deterministic selection from the actual polynomial, with no correctness property assumed.
--
--   Put $S=s^*(C)$ and retain every nonconstant blockwise multi-index of total degree at most $S$. For rounded integer moments $a_\nu$, construct the rational series $f(z)=1+\sum_\nu a_\nu z^\nu$. The decoder reads
--
--   $$\widehat n_A=b_A^{-1}[z^{\nu_A}]\log f,\qquad
--   n_{D,\sigma}=q_D^{-1}\left(w+\sum_{0\ne A\in C_D^\perp}\widehat n_A\chi_A(\sigma)\right).$$
--
--   It checks nonnegative integer counts, coset invariance and sum $w$ on each block. If a check fails, it returns the fixed valid profile of $w$ zero offsets. These checks use only the decoded entries; there is no list of candidate profiles in the procedure.
--
--   The batch size is $n=128\operatorname{Bell}(2S)w^S$. For $R$ disjoint batches, compute exact rational means of every retained $\psi_\nu$, take the coordinatewise median (middle entry of the sorted list), round to the nearest integer, and apply the decoder. Theorems use positive odd $R$; all operations are defined on other inputs too. A coordinate exceeding $w$ has Krawtchouk factor zero by the published convention.
--
--   An arbitrary randomized $N$-sample estimator $E$ is a probability kernel from the $N$ observations to profile-shaped outputs, including invalid outputs. Its error at $\ell$ and its uniform-error criterion are
--
--   $$\operatorname{err}_\ell(E)=\sum_{x_1,\ldots,x_N}\prod_{i=1}^N P_\ell(x_i)\left(1-E(x_1,\ldots,x_N)\{T_C(\ell)\}\right),\qquad
--   \forall\ell,\ \operatorname{err}_\ell(E)\le\eta.$$
--
--   Invalid outputs count as errors. These definitions specify the exact profile-recovery task and the decoder of equation (15), without assuming its accuracy, the nonvanishing of its witnesses or its computational efficiency.
--
--   **Formalization Note.** Printed coordinate $i$ is `Fin m` coordinate $i-1$. Rational arithmetic is exact; signed character counts are not natural subtraction. Order infinity is not silently excluded: later theorems conclude finiteness before using its natural value. A zero polynomial has the zero witness index and coefficient; division by zero defaults to zero in this total definition, and theorems establish the needed nonzero coefficients on source instances through the actual decoder guarantee.
-- source:
--   Jianxin Wang, Zixuan Wang, Chenxu Pang, Chaoen Xiao, Lei Zhang, Zaitian Fu, Conghui Zheng, Yiyang Zou, STOC 2027 submission #1555 (October 2026), §3.2 Theorem 5, printed pp.5–6 (PDF pp.6–7); §5 equation (15), printed pp.10–11 (PDF pp.11–12); Appendix B, printed pp.14–15 (PDF pp.15–16); https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1555.pdf; pinned PDF SHA256 1f5fce093155b2721073a124d87a3c6947269ff7851c61301dfa6e81232f0b2c

import Definitions.Def_AggregatedCodeTesting_Testing_Orders

set_option autoImplicit false
open Finset Classical
noncomputable section

namespace AggregatedCodeTesting.Testing.Supplement

/-- The ordinary binary orthogonal subspace, with no asserted structural properties. -/
def orthogonal {m : ℕ} (C : Submodule (ZMod 2) (Word m)) : Submodule (ZMod 2) (Word m) where
  carrier := {x | ∀ c ∈ C, dotProduct c x = 0}
  zero_mem' := by simp
  add_mem' := by
    intro x y hx hy c hc
    rw [dotProduct_add, hx c hc, hy c hc, add_zero]
  smul_mem' := by
    intro a x hx c hc
    rw [dotProduct_smul, hx c hc, smul_zero]

/-- The three printed generators, with printed coordinate i represented by i-1. -/
def alpha (k : ℕ) : Word (k + 4) := fun e => if e.val < 2 then 1 else 0
def beta (k : ℕ) : Word (k + 4) := fun e => if 2 ≤ e.val ∧ e.val < 4 then 1 else 0
def gamma (k : ℕ) : Word (k + 4) := fun e => if e.val = 0 ∨ e.val = 2 ∨ 4 ≤ e.val then 1 else 0
def familyDual (k : ℕ) : Submodule (ZMod 2) (Word (k + 4)) :=
  Submodule.span (ZMod 2) {alpha k, beta k, gamma k}
def familyCode (k : ℕ) : Submodule (ZMod 2) (Word (k + 4)) := orthogonal (familyDual k)
def familyCharacter (k : ℕ) : Word (k + 4) := alpha k + beta k
/-- Exponents (1,1,1,1,2,...,2) of the entire lowest homogeneous part. -/
def familyExponent (k : ℕ) : Fin (k + 4) →₀ ℕ :=
  Finsupp.equivFunOnFinite.symm (fun e => if e.val < 4 then 1 else 2)

variable {m : ℕ}
/-- Binary numerical order fixes representatives without any statistical assumption. -/
def wordNumber (x : Word m) : ℕ := ∑ e, (x e).val * 2 ^ e.val
/-- One representative per block coset, zero outside the block. -/
def representatives (C : Submodule (ZMod 2) (Word m)) (D : Finset (Fin m)) : Finset (Word m) :=
  univ.filter fun x => supp x ⊆ D ∧
    ∀ y : Word m, supp y ⊆ D → proj D (y - x) ∈ C → wordNumber x ≤ wordNumber y

def maxDualWeight (C : Submodule (ZMod 2) (Word m)) (D : Finset (Fin m)) : ℕ :=
  (blockDual C D).sup weight

def degreeBound (C : Submodule (ZMod 2) (Word m)) (D : Finset (Fin m)) : ℕ :=
  maxDualWeight C D * (blockDual C D).card / 2

/-- Appendix B's actual multivariate integer polynomial, one factor per coset. -/
def differencePoly (C : Submodule (ZMod 2) (Word m)) (D : Finset (Fin m)) (A : Word m) :
    MvPolynomial (Fin m) ℤ :=
  (∏ x ∈ (representatives C D).filter (fun x => chi A x = 1), codePoly ℤ C D x) -
  (∏ x ∈ (representatives C D).filter (fun x => chi A x = -1), codePoly ℤ C D x)

/-- Degree first, then base-(D+1) monomial order. -/
def monomialKey (B : ℕ) (v : Fin m →₀ ℕ) : ℕ :=
  v.degree * (B + 1) ^ m + ∑ e, v e * (B + 1) ^ e.val

def firstKey (B : ℕ) (F : MvPolynomial (Fin m) ℤ) : ℕ :=
  let keys := F.support.image (monomialKey B)
  if h : keys.Nonempty then keys.min' h else 0

/-- The least key is decoded into its exponent vector. F=0 defaults to the zero vector. -/
def witnessIndex (C : Submodule (ZMod 2) (Word m)) (D : Finset (Fin m)) (A : Word m) :
    Fin m →₀ ℕ :=
  let B := degreeBound C D
  let j := firstKey B (differencePoly C D A) % (B + 1) ^ m
  Finsupp.equivFunOnFinite.symm (fun e => j / (B + 1) ^ e.val % (B + 1))

def witnessCoefficient (C : Submodule (ZMod 2) (Word m)) (D : Finset (Fin m)) (A : Word m) : ℚ :=
  ((MvPolynomial.coeff (witnessIndex C D A) (differencePoly C D A) : ℤ) : ℚ) /
    (blockDual C D).card

/-- All retained nonconstant blockwise moment indices; finite also on malformed codes. -/
def momentIndices (C : Submodule (ZMod 2) (Word m)) : Finset (Fin m → ℕ) :=
  (lowIndices m (sStar C).toNat).filter (IsBlockwiseIndex C)

/-- Profile-shaped rational Walsh inversion of the rounded moment polynomial, equation (15). -/
def invertedCounts (C : Submodule (ZMod 2) (Word m)) (w : ℕ)
    (mom : (Fin m → ℕ) → ℤ) (D : Finset (Fin m)) (x : Word m) : ℚ :=
  let f : MvPowerSeries (Fin m) ℚ := fun v =>
    if v = 0 then 1 else if (fun e => v e) ∈ momentIndices C then mom (fun e => v e) else 0
  ((w : ℚ) + ∑ A ∈ (blockDual C D).filter (· ≠ 0),
    (MvPowerSeries.coeff (witnessIndex C D A) (formalLog f) / witnessCoefficient C D A) *
      (chi A x : ℚ)) / (blockDual C D).card

abbrev Profile (C : Submodule (ZMod 2) (Word m)) := ↥(blocks C) → Word m → ℕ

/-- Local arithmetic validity; this predicate does not enumerate candidate profiles. -/
def ValidCounts (C : Submodule (ZMod 2) (Word m)) (w : ℕ)
    (f : Finset (Fin m) → Word m → ℚ) : Prop :=
  ∀ D ∈ blocks C,
    (∀ x, 0 ≤ f D x ∧ (f D x).den = 1) ∧
    (∀ x y, proj D (x - y) ∈ C → f D x = f D y) ∧
    (∑ x ∈ representatives C D, f D x) = (w : ℚ)

/-- Exact inversion with the specified fixed valid fallback (all offsets zero). -/
def decodeMoments (C : Submodule (ZMod 2) (Word m)) (w : ℕ)
    (mom : (Fin m → ℕ) → ℤ) : Profile C :=
  let f := invertedCounts C w mom
  if ValidCounts C w f then fun D x => (f D.val x).num.toNat
  else profile C (fun _ : Fin w => (0 : Word m))

/-- Batch size in Theorem 11, with Bell the number of set partitions. -/
def batchSize (C : Submodule (ZMod 2) (Word m)) (w : ℕ) : ℕ :=
  128 * Nat.bell (2 * (sStar C).toNat) * w ^ (sStar C).toNat

/-- Exact rational batch means, with disjoint consecutive batches. -/
def batchMean (w n R : ℕ) (xs : Fin (n * R) → (Fin m → Fin (w + 1)))
    (nu : Fin m → ℕ) (j : Fin R) : ℚ :=
  (∑ i : Fin n, (psi w nu (xs ⟨j.val * n + i.val, by
    calc j.val * n + i.val < j.val * n + n := Nat.add_lt_add_left i.isLt _
         _ = (j.val + 1) * n := by ring
         _ ≤ R * n := Nat.mul_le_mul_right n j.isLt
         _ = n * R := Nat.mul_comm R n⟩) : ℚ)) / n

/-- Coordinatewise median, sorted exactly; the theorem uses a positive odd R. -/
def medianMoment (w n R : ℕ) (xs : Fin (n * R) → (Fin m → Fin (w + 1)))
    (nu : Fin m → ℕ) : ℤ :=
  round (((List.ofFn (batchMean w n R xs nu)).mergeSort (· ≤ ·)).getD (R / 2) 0)

def recovery (C : Submodule (ZMod 2) (Word m)) (w R : ℕ)
    (xs : Fin (batchSize C w * R) → (Fin m → Fin (w + 1))) : Profile C :=
  decodeMoments C w (medianMoment w (batchSize C w) R xs)

/-- Every randomized estimator is a probability kernel; invalid count outputs are permitted
and counted as errors. This includes every deterministic rule and every independent randomization. -/
abbrev Estimator (C : Submodule (ZMod 2) (Word m)) (w N : ℕ) :=
  (Fin N → (Fin m → Fin (w + 1))) → PMF (Profile C)

/-- Validity of an output means realizability by offsets. This is only a specification of the
output, never used by the decoder to search for candidate profiles. -/
def ValidOutput (C : Submodule (ZMod 2) (Word m)) (w : ℕ) (t : Profile C) : Prop :=
  ∃ l : Fin w → Word m, t = profile C l

/-- Product-law error at a fixed unknown profile. PMFs allow arbitrary real randomization. -/
def recoveryError {w N : ℕ} (C : Submodule (ZMod 2) (Word m)) (E : Estimator C w N)
    (l : Fin w → Word m) : ℝ :=
  ∑ xs, (∏ i, law C l (xs i)) * (1 - (E xs (profile C l)).toReal)

def deterministicEstimator {w N : ℕ} (C : Submodule (ZMod 2) (Word m))
    (f : (Fin N → (Fin m → Fin (w + 1))) → Profile C) : Estimator C w N :=
  fun xs => PMF.pure (f xs)

/-- Uniform error requirement, quantifying over every profile, including sparse ones. -/
def ErrorAtMost (C : Submodule (ZMod 2) (Word m)) (w N : ℕ) (E : Estimator C w N) (eta : ℝ) : Prop :=
  ∀ l : Fin w → Word m, recoveryError C E l ≤ eta

end AggregatedCodeTesting.Testing.Supplement


