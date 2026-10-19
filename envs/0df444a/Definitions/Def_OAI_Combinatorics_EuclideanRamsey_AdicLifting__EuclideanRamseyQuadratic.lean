-- Prove2me | Definitions.Def_OAI_Combinatorics_EuclideanRamsey_AdicLifting__EuclideanRamseyQuadratic
-- name    : OAI_Combinatorics_EuclideanRamsey_AdicLifting__EuclideanRamseyQuadratic
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-19T07:33:31.557303+00:00
-- url     : https://prove2.me/theorems/093c0fec-2a7e-45c9-9f6c-ecec855c651d
-- title:
--   Exponential and logarithm on nilpotent ideals, logarithms of unipotent characters, and coset ideals of $\mathbb{Q}[\mathbb{Z}^k]$
-- statement:
--   This file develops the exponential of nilpotent elements of commutative $\mathbb{Q}$-algebras, uses it to take logarithms of characters with values in $1+I$ for a nilpotent ideal $I$, and defines the coset ideals of the group algebra of the integer lattice.
--
--   Let $R$ be a commutative ring that is an algebra over $\mathbb{Q}$. For a nilpotent element $a\in R$ put
--   $$\exp(a)=\sum_{i\ge0}\frac{a^i}{i!},$$
--   a finite sum. The file proves the following facts about this exponential: (a) for nilpotent $a$ there is a nilpotent $b$ with $\exp(a)=1+a(1+b)$, and consequently $\exp(a)=1$ if and only if $a=0$; (b) if $a$ is nilpotent and lies in an ideal $J$, then $\exp(a)-1-a\in J^2$ and $\exp(a)-1\in J$; (c) in any commutative ring, if an ideal $I$ satisfies $I^n=0$ for some $n$, then every element of $I$ is nilpotent; (d) if $I^n=0$, then $\exp$ maps $I$ bijectively onto $1+I$: for every $z\in I$ there is $x\in I$ with $\exp(x)=1+z$, and $\exp(x)=\exp(y)$ with $x,y\in I$ implies $x=y$.
--
--   1. **Logarithm of a character.** Let $I$ be an ideal of $R$ with $I^n=0$ for some $n$, let $G$ be an additive abelian group, and let $\chi$ be a monoid homomorphism from $G$ (written multiplicatively) to the multiplicative monoid of $R$ such that $\chi(\gamma)-1\in I$ for every $\gamma\in G$. Then $\log_\chi(\gamma)$ is the element of $I$ with $\exp(\log_\chi(\gamma))=\chi(\gamma)$ (it exists and is unique by (d)), and $\gamma\mapsto\log_\chi(\gamma)$ is an additive group homomorphism $G\to R$:
--   $$\exp\bigl(\log_\chi(\gamma)\bigr)=\chi(\gamma),\qquad \log_\chi(\gamma)\in I,\qquad \log_\chi(\gamma+\gamma')=\log_\chi(\gamma)+\log_\chi(\gamma').$$
--   2. **Rational extension.** For $k\in\mathbb{N}$ and an additive homomorphism $f:\mathbb{Z}^k\to R$, $\bar f:\mathbb{Q}^k\to R$ is the $\mathbb{Q}$-linear map $\bar f(v)=\sum_{j=1}^{k}v_j\,f(e_j)$, where $e_1,\dots,e_k$ are the standard basis vectors; it satisfies $\bar f(e_j)=f(e_j)$.
--   3. **Coset map and coset ideal.** For a subgroup $\Lambda\le\mathbb{Z}^k$, the coset map is the $\mathbb{Q}$-algebra homomorphism $\mathbb{Q}[\mathbb{Z}^k]\to\mathbb{Q}[\mathbb{Z}^k/\Lambda]$ between group algebras induced by the quotient map $\mathbb{Z}^k\to\mathbb{Z}^k/\Lambda$, and the coset ideal of $\Lambda$ is its kernel, i.e. the set of rational signed measures $\nu$ on $\mathbb{Z}^k$ whose weights sum to $0$ on every coset of $\Lambda$.
--
--   These tools drive the proof of the finite lattice identity. In the group algebra $\mathbb{Q}[\mathbb{Z}^k]$, modulo a power $A^N$ of the augmentation ideal $A$ (the kernel of the homomorphism sending every basis element $[\gamma]$ to $1$), the character $\gamma\mapsto[\gamma]$ takes values in $1+A$, and $A$ becomes nilpotent, so the character has a logarithm, an additive homomorphism on $\mathbb{Z}^k$. Lifts $l_1,\dots,l_k$ of the logarithms of the basis vectors are combined into the quadratic stencil $\tfrac12\sum_{a,b}C_{ab}\,l_al_b$; via the rational extension of the logarithm, the vanishing of $\sum_{a,b}C_{ab}\,e_a\otimes e_b$ modulo the rational span of $\Lambda$ places this stencil in the sum of the coset ideal of $\Lambda$ and $A^N$, and a Noetherian (Artin–Rees type) lifting argument then corrects it into an element of all the required coset ideals with the same moments up to order two.
--
--   **Formalization Note** The exponential is Mathlib's `IsNilpotent.exp`; facts (a) to (d) are `nil_exp_quadratic`, `nil_exp_eq_one_iff`, `nil_exp_sub_one_sub_mem`, `nil_exp_sub_one_mem`, `nilpotent_of_mem_nil_ideal` (which needs no $\mathbb{Q}$-algebra structure), `nil_ideal_exp_surjective` and `nil_exp_injective`. The character is a monoid homomorphism `Multiplicative G →* R`; `characterLog hI χ hχ` is chosen with `Classical.choose` from the surjectivity statement, with properties `characterLog_mem` and `characterLog_exp`, and `characterLogHom` packages it as `G →+ R`. `rationalExtension` has the simp lemma `rationalExtension_single`; `cosetMap` is `AddMonoidAlgebra.mapDomainAlgHom` along `QuotientAddGroup.mk'`, and `cosetIdeal` is its `RingHom.ker`. The lifting lemmas mentioned in the role paragraph are proved separately; the corresponding sections of this file contain no declarations.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/EuclideanRamsey/AdicLifting.lean

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/EuclideanRamsey/AdicLifting.lean by skeleton subtraction
-- (upload_full_project.md Phase 3): Definitions bundle for the EuclideanRamseyQuadratic mission closure.
-- Kept: reachable definitions/instances and the theorems their bodies or the node statements cite.
-- Project imports rewritten to platform modules; otherwise byte-identical to the source.
import Mathlib
import Definitions.Def_EuclideanRamseyQuadratic
import Definitions.Def_OAI_Combinatorics_EuclideanRamsey_Model__EuclideanRamseyQuadratic
import Definitions.Def_OAI_Combinatorics_EuclideanRamsey_TensorNecessity__EuclideanRamseyQuadratic
import Definitions.Def_OAI_Combinatorics_EuclideanRamsey_TensorDescent__EuclideanRamseyQuadratic
import Definitions.Def_OAI_Combinatorics_EuclideanRamsey_SmoothingKernel__EuclideanRamseyQuadratic
import Definitions.Def_OAI_Combinatorics_EuclideanRamsey_Hessian__EuclideanRamseyQuadratic
import Definitions.Def_OAI_Combinatorics_EuclideanRamsey_DifferentialSplitting__EuclideanRamseyQuadratic
import Definitions.Def_OAI_Combinatorics_EuclideanRamsey_SmoothingMatrix__EuclideanRamseyQuadratic
import Definitions.Def_OAI_Combinatorics_EuclideanRamsey_LatticeMoments__EuclideanRamseyQuadratic
import Definitions.Def_OAI_Combinatorics_EuclideanRamsey_Discretization__EuclideanRamseyQuadratic

namespace OAI

universe uRing uGroup uSemigroup uModule uModuleTarget uIndex

noncomputable section

open scoped TensorProduct RealInnerProductSpace
open scoped BigOperators
open Real Filter Topology MeasureTheory Polynomial
open Matrix MeasureTheory
open MeasureTheory
open Matrix
open scoped MatrixOrder Matrix.Norms.L2Operator
open MeasureTheory Matrix
open scoped TensorProduct
open scoped BigOperators Pointwise Topology
open MeasureTheory Filter
open scoped BigOperators Pointwise
open scoped BigOperators Topology

open scoped TensorProduct
namespace EuclideanRamsey

section NilpotentLog
variable {R : Type uRing} [CommRing R] [Algebra ℚ R]
open Finset

lemma nil_exp_quadratic {a : R} (ha : IsNilpotent a) :
    ∃ b : R, IsNilpotent b ∧ IsNilpotent.exp a = 1 + a * (1 + b) := by
  obtain ⟨n, hn⟩ := ha
  let c : R := ∑ i ∈ range n, ((i + 2).factorial : ℚ)⁻¹ • a ^ i
  refine ⟨a * c, ?_, ?_⟩
  · exact ⟨n, by rw [mul_pow, hn, zero_mul]⟩
  · rw [IsNilpotent.exp_eq_sum (pow_eq_zero_of_le (Nat.le_add_right n 2) hn)]
    rw [show n + 2 = 2 + n by omega, sum_range_add]
    have h2 : (∑ i ∈ range 2, (i.factorial : ℚ)⁻¹ • a ^ i) = 1 + a := by
      simp [sum_range_succ]
    rw [h2]
    have ht : (∑ i ∈ range n, ((2 + i).factorial : ℚ)⁻¹ • a ^ (2 + i)) = a ^ 2 * c := by
      simp only [c, mul_sum, pow_add, mul_smul_comm, add_comm 2, mul_comm]
    rw [ht]
    ring

lemma nil_exp_eq_one_iff {a : R} (ha : IsNilpotent a) :
    IsNilpotent.exp a = 1 ↔ a = 0 := by
  obtain ⟨b, hb, he⟩ := nil_exp_quadratic ha
  rw [he]
  constructor
  · intro h
    have hmul : a * (1 + b) = 0 := by linear_combination h
    exact hb.isUnit_one_add.mul_right_cancel (by simpa using hmul)
  · intro h
    simp [h]

lemma nil_exp_sub_one_sub_mem {J : Ideal R} {a : R} (ha : IsNilpotent a) (hJ : a ∈ J) :
    IsNilpotent.exp a - 1 - a ∈ J ^ 2 := by
  obtain ⟨n, hn⟩ := ha
  rw [IsNilpotent.exp_eq_sum (pow_eq_zero_of_le (Nat.le_add_right n 2) hn)]
  rw [show n + 2 = 2 + n by omega, sum_range_add]
  have h2 : (∑ i ∈ range 2, (i.factorial : ℚ)⁻¹ • a ^ i) = 1 + a := by
    simp [sum_range_succ]
  rw [h2]
  have he : 1 + a + (∑ i ∈ range n, ((2 + i).factorial : ℚ)⁻¹ • a ^ (2 + i)) - 1 - a =
      ∑ i ∈ range n, ((2 + i).factorial : ℚ)⁻¹ • a ^ (2 + i) := by ring
  rw [he]
  apply Submodule.sum_mem
  intro i hi
  rw [Algebra.smul_def]
  apply Ideal.mul_mem_left
  rw [pow_add]
  exact Ideal.mul_mem_right _ _ (Ideal.pow_mem_pow hJ 2)

lemma nil_exp_sub_one_mem {J : Ideal R} {a : R} (ha : IsNilpotent a) (hJ : a ∈ J) :
    IsNilpotent.exp a - 1 ∈ J := by
  have h2 := nil_exp_sub_one_sub_mem ha hJ
  have hle : J ^ 2 ≤ J := Ideal.pow_le_self (by omega)
  have := J.add_mem (hle h2) hJ
  simpa only [sub_add_cancel] using this

omit [Algebra ℚ R] in
lemma nilpotent_of_mem_nil_ideal {I : Ideal R} {n : ℕ} (hI : I ^ n = ⊥)
    {x : R} (hx : x ∈ I) : IsNilpotent x := by
  refine ⟨n, ?_⟩
  have := Ideal.pow_mem_pow hx n
  simpa only [hI, Ideal.mem_bot] using this

lemma nil_ideal_exp_surjective {I : Ideal R} {n : ℕ} (hI : I ^ n = ⊥)
    {z : R} (hz : z ∈ I) : ∃ x ∈ I, IsNilpotent.exp x = 1 + z := by
  have happrox : ∀ k : ℕ, ∃ x ∈ I, IsNilpotent.exp x - (1 + z) ∈ I ^ (k + 1) := by
    intro k
    induction k with
    | zero =>
      refine ⟨0, I.zero_mem, ?_⟩
      simpa using I.neg_mem hz
    | succ k ih =>
      obtain ⟨x, hx, he⟩ := ih
      let e := (1 + z) - IsNilpotent.exp x
      have he' : e ∈ I ^ (k + 1) := by simpa only [e, neg_sub] using (I ^ (k + 1)).neg_mem he
      have hp : I ^ (k + 1) ≤ I := Ideal.pow_le_self (by omega)
      have hei : e ∈ I := hp he'
      have hnx := nilpotent_of_mem_nil_ideal hI hx
      have hne := nilpotent_of_mem_nil_ideal hI hei
      refine ⟨x + e, I.add_mem hx hei, ?_⟩
      rw [IsNilpotent.exp_add_of_commute (Commute.all _ _) hnx hne]
      let r := IsNilpotent.exp e - 1 - e
      have hr : r ∈ (I ^ (k + 1)) ^ 2 := nil_exp_sub_one_sub_mem hne he'
      have hle : (I ^ (k + 1)) ^ 2 ≤ I ^ (k + 2) := by
        rw [← pow_mul]
        exact Ideal.pow_le_pow_right (by omega)
      have hterm1 : (IsNilpotent.exp x - 1) * e ∈ I ^ (k + 2) := by
        have hh := Ideal.mul_mem_mul (nil_exp_sub_one_mem hnx hx) he'
        simpa only [← pow_succ', Nat.add_assoc] using hh
      have hterm2 : IsNilpotent.exp x * r ∈ I ^ (k + 2) :=
        Ideal.mul_mem_left _ _ (hle hr)
      have hh := (I ^ (k + 2)).add_mem hterm1 hterm2
      convert hh using 1 ; dsimp [r, e] ; ring
  obtain ⟨x, hx, he⟩ := happrox n
  have hp : I ^ (n + 1) = ⊥ := by simp [pow_succ, hI]
  rw [hp, Ideal.mem_bot, sub_eq_zero] at he
  exact ⟨x, hx, he⟩

end NilpotentLog

section LogCharacter
variable {R : Type uRing} [CommRing R] [Algebra ℚ R]
  {I : Ideal R} {n : ℕ} (hI : I ^ n = ⊥)

include hI in
lemma nil_exp_injective {a b : R} (ha : a ∈ I) (hb : b ∈ I)
    (he : IsNilpotent.exp a = IsNilpotent.exp b) : a = b := by
  have hna := nilpotent_of_mem_nil_ideal hI ha
  have hnb := nilpotent_of_mem_nil_ideal hI hb
  have hnd := nilpotent_of_mem_nil_ideal hI (I.sub_mem ha hb)
  apply sub_eq_zero.mp
  apply (nil_exp_eq_one_iff hnd).mp
  rw [sub_eq_add_neg, IsNilpotent.exp_add_of_commute (Commute.all _ _) hna hnb.neg,
    he, hnb.exp_mul_exp_neg_self]

variable {G : Type uGroup} [AddCommGroup G] (χ : Multiplicative G →* R)
  (hχ : ∀ γ : G, χ (Multiplicative.ofAdd γ) - 1 ∈ I)

noncomputable def characterLog (γ : G) : R :=
  Classical.choose (nil_ideal_exp_surjective hI (hχ γ))

lemma characterLog_mem (γ : G) : characterLog hI χ hχ γ ∈ I :=
  (Classical.choose_spec (nil_ideal_exp_surjective hI (hχ γ))).1

lemma characterLog_exp (γ : G) :
    IsNilpotent.exp (characterLog hI χ hχ γ) = χ (Multiplicative.ofAdd γ) := by
  have := (Classical.choose_spec (nil_ideal_exp_surjective hI (hχ γ))).2
  simpa only [characterLog, add_sub_cancel] using this

noncomputable def characterLogHom : G →+ R where
  toFun := characterLog hI χ hχ
  map_zero' := by
    apply nil_exp_injective hI (characterLog_mem ..) I.zero_mem
    rw [characterLog_exp, IsNilpotent.exp_zero]
    exact χ.map_one
  map_add' a b := by
    apply nil_exp_injective hI (characterLog_mem ..)
      (I.add_mem (characterLog_mem ..) (characterLog_mem ..))
    rw [characterLog_exp, IsNilpotent.exp_add_of_commute (Commute.all _ _)
      (nilpotent_of_mem_nil_ideal hI (characterLog_mem ..))
      (nilpotent_of_mem_nil_ideal hI (characterLog_mem ..)), characterLog_exp, characterLog_exp]
    exact χ.map_mul _ _

end LogCharacter

section LatticeLog
variable {k : ℕ} {R : Type uRing} [CommRing R] [Algebra ℚ R]

def rationalExtension (f : (Fin k → ℤ) →+ R) : (Fin k → ℚ) →ₗ[ℚ] R where
  toFun v := ∑ j, v j • f (Pi.single j 1)
  map_add' a b := by simp [add_smul, Finset.sum_add_distrib]
  map_smul' a b := by simp [mul_smul, Finset.smul_sum]

end LatticeLog

section AdicLifting
variable {R : Type uRing} {M : Type uModule} {N : Type uModuleTarget} [CommRing R] [IsNoetherianRing R]
  [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
  [Module.Finite R N]

end AdicLifting

section IntersectionLifting
variable {R : Type uRing} [CommRing R] [IsNoetherianRing R]
  {ι : Type uIndex} [Fintype ι] (I : Ideal R) (J : ι → Ideal R)

end IntersectionLifting

section Construction
variable {k : ℕ}

@[simp] lemma rationalExtension_single {R : Type uRing} [CommRing R] [Algebra ℚ R]
    (f : Lattice k →+ R) (a : Fin k) :
    rationalExtension f (Pi.single a 1) = f (Pi.single a 1) := by
  classical
  simp [rationalExtension, Pi.single_apply]

def cosetMap (Λ : AddSubgroup (Lattice k)) :
    LatticeRing k →ₐ[ℚ] AddMonoidAlgebra ℚ (Lattice k ⧸ Λ) :=
  AddMonoidAlgebra.mapDomainAlgHom ℚ ℚ (QuotientAddGroup.mk' Λ)

def cosetIdeal (Λ : AddSubgroup (Lattice k)) : Ideal (LatticeRing k) :=
  RingHom.ker (cosetMap Λ)

end Construction

end EuclideanRamsey

end

end OAI


