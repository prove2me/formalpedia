-- Prove2me | Definitions.Def_OAI_MathematicalPhysics_Fock_Beam
-- name    : OAI_MathematicalPhysics_Fock_Beam
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-15T22:59:21.599062+00:00
-- url     : https://prove2.me/theorems/75418070-927c-4cb7-b4c6-8539b71161a0
-- title:
--   Fischer pairing, rotated two-mode creation polynomials and the multimode beam-splitter unitary on two-port Fock space
-- statement:
--   This file constructs the passive beam-splitter unitary acting on two copies of an $n$-mode bosonic Fock space, and identifies its matrix in the number basis with an explicit real orthogonal block matrix. The construction runs through polynomials: a number vector $|a\rangle$ corresponds to the monomial $x^a/\sqrt{a!}$, creation operators correspond to multiplication by variables, and a beam splitter corresponds to a rotation of the variables.
--
--   Throughout, $\mathbb{N}^n$ indexes the number basis of $n$ modes, and the *one-mode beam-splitter coefficient* for a transmissivity $\eta$ and $k,e,a,b \in \mathbb{N}$ is
--   $$
--   \beta_\eta(k,e;a,b) = [k+e=a+b]\,\sqrt{\frac{k!\,e!}{a!\,b!}}\sum_{\substack{0\le p\le a,\ 0\le q\le b\\ p+q=k}} \binom{a}{p}\binom{b}{q}\,\sqrt{\eta}^{\,p}\,\bigl(-\sqrt{1-\eta}\bigr)^{a-p}\sqrt{1-\eta}^{\,q}\,\sqrt{\eta}^{\,b-q},
--   $$
--   with the $n$-mode coefficient $\beta_\eta(k,e;a,b) = \prod_{j=1}^n \beta_\eta(k_j,e_j;a_j,b_j)$ for $k,e,a,b \in \mathbb{N}^n$.
--
--   1. **Fischer pairing.** For a finite index set $J$ and an exponent vector $m \in \mathbb{N}^J$ put $w(m) = \prod_{j} m_j!$. The Fischer pairing is the real bilinear form on $\mathbb{R}[x_j : j \in J]$ determined by $\langle x^m, q\rangle = w(m)\cdot[x^m]q$, where $[x^m]q$ is the coefficient of $x^m$ in $q$. It satisfies $\langle 1, q\rangle = q(0)$, $w(m + e_i) = (m_i+1)\,w(m)$, and multiplication by a variable is adjoint to differentiation: $\langle x_i p, q\rangle = \langle p, \partial_i q\rangle$.
--
--   2. **Rotated creators.** In two variables $x_0,x_1$ and for real $c,s$ put $A = c x_0 - s x_1$, $B = s x_0 + c x_1$, with the derivations $D_A = c\partial_0 - s\partial_1$ and $D_B = s\partial_0 + c\partial_1$. Then $\langle A p, q\rangle = \langle p, D_A q\rangle$ and $\langle B p, q\rangle = \langle p, D_B q\rangle$, $D_A B = D_B A = 0$, and if $c^2+s^2=1$ also $D_A A = D_B B = 1$. For the rotated monomials $R_{a,b} = A^a B^b$ and $c^2+s^2=1$ one gets the orthogonality relation
--   $$
--   \langle A^a B^b,\ A^u B^v\rangle = \begin{cases} a!\,b! & (a,b)=(u,v),\\ 0 & \text{otherwise.}\end{cases}
--   $$
--   Moreover the constant term of $A^aB^b$ is $1$ if $a=b=0$ and $0$ otherwise, and for all real $c,s$ the coefficient of $x_0^k x_1^e$ in $A^aB^b$ vanishes unless $k+e=a+b$, in which case it equals $\sum_{p\le a,\,q\le b,\,p+q=k}\binom{a}{p}\binom{b}{q}c^p(-s)^{a-p}s^q c^{b-q}$.
--
--   3. **Sector matrices.** For a total number $T \in \mathbb{N}$ and $k,a \in \{0,\dots,T\}$ the sector matrix is
--   $$
--   M^{c,s}_T(k,a) = \frac{\sqrt{k!\,(T-k)!}}{\sqrt{a!\,(T-a)!}}\,[x_0^k x_1^{T-k}]\bigl(A^a B^{T-a}\bigr),
--   $$
--   and for $T \in \mathbb{N}^n$ the multi-sector matrix is the tensor product $M^{c,s}_T(k,a) = \prod_j M^{c,s}_{T_j}(k_j,a_j)$ indexed by $k,a$ with $0\le k_j,a_j\le T_j$. If $c^2+s^2=1$, both are real orthogonal matrices (orthonormal columns and orthonormal rows). A polynomial whose coefficients vanish outside total degree $T$ is the sum of its monomials of degree $T$. The general *oscillator coefficient* $\sqrt{w(k,e)}/\sqrt{w(a,b)}\cdot[x_0^kx_1^e](A^aB^b)$ is also defined, and $\beta_\eta(k,e;a,b)$ equals it for $c=\sqrt\eta$, $s=\sqrt{1-\eta}$.
--
--   4. **Block unitaries.** Let $E$ be a complex Hilbert space with a Hilbert basis $(b_{s,k})$ indexed by pairs with $k$ in a finite block $I_s$, and let $U_s$ be real $I_s\times I_s$ matrices. The rotated vectors are $b'_{s,a} = \sum_{k \in I_s} U_s(k,a)\, b_{s,k}$. If every $U_s$ has orthonormal columns the $b'$ are orthonormal; if every $U_s$ also has orthonormal rows, then $b_{s,k} = \sum_a U_s(k,a)\, b'_{s,a}$, the $b'$ span a dense subspace and form a Hilbert basis, and the unitary $\mathcal U$ of $E$ with $\mathcal U b_{s,a} = b'_{s,a}$ satisfies $\mathcal U^{-1} b_{s,k} = \sum_a U_s(k,a)\, b_{s,a}$. A Hilbert basis may also be reindexed along any bijection of index sets.
--
--   5. **The beam-splitter unitary.** The joint Fock space is $\ell^2(\mathbb{N}^n\times\mathbb{N}^n;\mathbb{C})$ with number basis $|k,e\rangle$. Number sectors are pairs $(T,a)$ with $T \in \mathbb{N}^n$ and $0\le a_j\le T_j$; the bijection $(T,a)\mapsto (a, T-a)$ (inverse $(k,e)\mapsto(k+e,k)$) reindexes the number basis by sectors. On a sector, $\beta_\eta(k,T-k;a,T-a)$ equals the multi-sector matrix with $c=\sqrt\eta$, $s=\sqrt{1-\eta}$, and for $\eta \in [0,1]$ one has $\sqrt\eta^{\,2}+\sqrt{1-\eta}^{\,2}=1$. For $\eta\in[0,1]$ the beam-splitter unitary $\mathcal U_\eta$ is the block unitary of item 4 built from these matrices, and its inverse acts on number vectors by
--   $$
--   \mathcal U_\eta^{-1}\,|k,e\rangle = \sum_{\substack{a \in \mathbb{N}^n\\ a_j \le k_j+e_j}} \beta_\eta\bigl(k,e;\,a,\,k+e-a\bigr)\,|a,\,k+e-a\rangle .
--   $$
--
--   These objects realise, as an honest unitary operator on the untruncated two-port Fock space, the passive mixing whose matrix elements enter the definition of a beam-splitter output state; the sector decomposition shows that the mixing preserves the total photon number in each paired mode.
--
--   **Formalization Note** The pairing is built with `Basis.constr` on the monomial basis of `MvPolynomial J ℝ`; `degree a b` is the exponent vector $(a,b)$ in two variables. Sector bases are indexed by the sigma type `NumberSector n`, and `beamUnitary η hη` requires the proof `hη : η ∈ Set.Icc 0 1`. The natural-number subtractions $T-k$, $k+e-a$ are truncated, but in every use the subtrahend is at most the minuend. Two private `if`-rewriting lemmas are plumbing.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/MathematicalPhysics/Fock/Beam.lean

-- Generated from openai/math@1581d4c lean/OAI/MathematicalPhysics/Fock/Beam.lean by skeleton subtraction
-- (upload_full_project.md Phase 3): Definitions bundle for the EntropyPhotonNumber mission closure.
-- Kept: reachable definitions/instances and the theorems their bodies or the node statements cite.
-- Project imports rewritten to platform modules; otherwise byte-identical to the source.
import Mathlib
import Definitions.Def_EntropyPhotonNumber

-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
private theorem ite_eq_left.{u} {c : Prop} {h : Decidable c} (hc : c) {α : Sort u} {t e : α} : (ite c t e) = t := @if_pos c h hc α t e
private theorem ite_eq_right.{u} {c : Prop} {h : Decidable c} (hc : ¬c) {α : Sort u} {t e : α} : (ite c t e) = e := @if_neg c h hc α t e

namespace OAI

noncomputable section

section
open scoped BigOperators ComplexConjugate ENNReal Topology
open MeasureTheory
open scoped ComplexConjugate
open scoped BigOperators ComplexConjugate
open scoped BigOperators
open MvPolynomial

namespace FischerBeam
variable {J : Type*} [Fintype J] [DecidableEq J]

def weight (m : J →₀ ℕ) : ℝ := ∏ j, (m j).factorial

def pairing : MvPolynomial J ℝ →ₗ[ℝ] MvPolynomial J ℝ →ₗ[ℝ] ℝ :=
  (basisMonomials J ℝ).constr ℝ (fun m => weight m • lcoeff ℝ m)

omit [DecidableEq J] in
@[simp] theorem pairing_monomial (m : J →₀ ℕ) (a : ℝ) (q : MvPolynomial J ℝ) :
    pairing (monomial m a) q = a * weight m * q.coeff m := by
  have hm : monomial m a = a • (basisMonomials J ℝ) m := by
    simp [coe_basisMonomials, smul_monomial]
  have hb : pairing ((basisMonomials J ℝ) m) = weight m • lcoeff ℝ m :=
    (basisMonomials J ℝ).constr_basis ℝ _ m
  rw [hm, map_smul, LinearMap.smul_apply, hb]
  simp only [LinearMap.smul_apply, lcoeff_apply, smul_eq_mul]
  ring

omit [DecidableEq J] in
@[simp] theorem weight_zero : weight (0 : J →₀ ℕ) = 1 := by simp [weight]

omit [DecidableEq J] in
@[simp] theorem pairing_one (p : MvPolynomial J ℝ) :
    pairing 1 p = constantCoeff p := by
  change pairing (monomial 0 1) p = p.coeff 0
  rw [pairing_monomial, weight_zero, one_mul, one_mul]

theorem weight_add_single (m : J →₀ ℕ) (i : J) :
    weight (m + Finsupp.single i 1) = ((m i : ℝ)+1) * weight m := by
  unfold weight
  rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ i),
    ← Finset.mul_prod_erase _ (fun j => ((m j).factorial : ℝ)) (Finset.mem_univ i)]
  have he : (∏ j ∈ Finset.univ.erase i, ((m+(Finsupp.single i 1 : J →₀ ℕ)) j).factorial : ℝ) =
      ∏ j ∈ Finset.univ.erase i, ((m j).factorial : ℝ) := by
    apply Finset.prod_congr rfl
    intro j hj
    simp [Finsupp.single_eq_of_ne (Finset.ne_of_mem_erase hj)]
  rw [he]
  simp [Nat.factorial_succ, mul_assoc]

theorem pairing_X_left (i : J) (p q : MvPolynomial J ℝ) :
    pairing (X i*p) q = pairing p (pderiv i q) := by
  induction p using MvPolynomial.induction_on' with
  | add p r hp hr => simp [mul_add, hp, hr]
  | monomial m a =>
    rw [X, monomial_mul, one_mul, add_comm, pairing_monomial, pairing_monomial,
      coeff_pderiv, weight_add_single]
    ring

abbrev Poly := MvPolynomial (Fin 2) ℝ

def creatorA (c s : ℝ) : Poly := c • X 0 - s • X 1

def creatorB (c s : ℝ) : Poly := s • X 0 + c • X 1

def derivA (c s : ℝ) : Derivation ℝ Poly Poly := c • pderiv 0 - s • pderiv 1

def derivB (c s : ℝ) : Derivation ℝ Poly Poly := s • pderiv 0 + c • pderiv 1

@[simp] theorem derivA_creatorA {c s : ℝ} (h : c^2+s^2=1) :
    derivA c s (creatorA c s) = 1 := by
  simp only [derivA, creatorA, Derivation.sub_apply, Derivation.smul_apply, map_sub,
    Derivation.map_smul, pderiv_X_self, pderiv_X_of_ne (by decide : (1:Fin 2)≠0),
    pderiv_X_of_ne (by decide : (0:Fin 2)≠1), smul_zero, sub_zero, zero_sub,
    smul_neg, smul_smul, sub_neg_eq_add, ← add_smul]
  rw [← pow_two, ← pow_two, h, one_smul]

@[simp] theorem derivA_creatorB (c s : ℝ) : derivA c s (creatorB c s) = 0 := by
  simp [derivA, creatorB, Derivation.map_smul, smul_smul, mul_comm]

@[simp] theorem derivB_creatorA (c s : ℝ) : derivB c s (creatorA c s) = 0 := by
  simp [derivB, creatorA, Derivation.map_smul, smul_smul, mul_comm]

@[simp] theorem derivB_creatorB {c s : ℝ} (h : c^2+s^2=1) :
    derivB c s (creatorB c s) = 1 := by
  simp only [derivB, creatorB, Derivation.add_apply, Derivation.smul_apply, map_add,
    Derivation.map_smul, pderiv_X_self, pderiv_X_of_ne (by decide : (1:Fin 2)≠0),
    pderiv_X_of_ne (by decide : (0:Fin 2)≠1), smul_zero, add_zero, zero_add,
    smul_smul, ← add_smul]
  rw [← pow_two, ← pow_two, add_comm, h, one_smul]

theorem pairing_creatorA (c s : ℝ) (p q : Poly) :
    pairing (creatorA c s*p) q = pairing p (derivA c s q) := by
  simp [creatorA, derivA, sub_mul, pairing_X_left]

theorem pairing_creatorB (c s : ℝ) (p q : Poly) :
    pairing (creatorB c s*p) q = pairing p (derivB c s q) := by
  simp [creatorB, derivB, add_mul, pairing_X_left]

def rotated (c s : ℝ) (a b : ℕ) : Poly := creatorA c s^a * creatorB c s^b

@[simp] theorem derivA_rotated {c s : ℝ} (h : c^2+s^2=1) (a b : ℕ) :
    derivA c s (rotated c s a b) = a • rotated c s (a-1) b := by
  simp [rotated, Derivation.leibniz, Derivation.leibniz_pow, derivA_creatorA h,
    smul_eq_mul]
  ring

@[simp] theorem derivB_rotated {c s : ℝ} (h : c^2+s^2=1) (a b : ℕ) :
    derivB c s (rotated c s a b) = b • rotated c s a (b-1) := by
  simp [rotated, Derivation.leibniz, Derivation.leibniz_pow, derivB_creatorB h,
    smul_eq_mul]
  ring

@[simp] theorem constantCoeff_rotated (c s : ℝ) (a b : ℕ) :
    constantCoeff (rotated c s a b) = if a = 0 ∧ b = 0 then 1 else 0 := by
  simp [rotated, creatorA, creatorB, zero_pow_eq]
  split_ifs <;> simp_all

theorem pairing_rotated {c s : ℝ} (h : c^2+s^2=1) (a b u v : ℕ) :
    pairing (rotated c s a b) (rotated c s u v) =
      if a = u ∧ b = v then (a.factorial : ℝ)*b.factorial else 0 := by
  induction a generalizing b u v with
  | zero =>
    induction b generalizing u v with
    | zero =>
      rw [show rotated c s 0 0 = 1 by simp [rotated], pairing_one, constantCoeff_rotated]
      simp [eq_comm]
    | succ b ih =>
      have hr : rotated c s 0 (b+1) = creatorB c s * rotated c s 0 b := by
        simp [rotated, pow_succ']
      rw [hr, pairing_creatorB, derivB_rotated h, map_nsmul]
      cases v with
      | zero => simp
      | succ v =>
        simp only [Nat.add_one_sub_one, nsmul_eq_mul, ih]
        by_cases he : u = 0 ∧ b = v
        · obtain ⟨rfl, rfl⟩ := he
          simp [Nat.factorial_succ]
        · simp [he, eq_comm]
  | succ a ih =>
    have hr : rotated c s (a+1) b = creatorA c s * rotated c s a b := by
      simp [rotated, pow_succ', mul_assoc]
    rw [hr, pairing_creatorA, derivA_rotated h, map_nsmul]
    cases u with
    | zero => simp
    | succ u =>
      simp only [Nat.add_one_sub_one, nsmul_eq_mul, ih]
      by_cases he : a = u ∧ b = v
      · obtain ⟨rfl, rfl⟩ := he
        simp [Nat.factorial_succ]
        ring
      · simp [he]

end FischerBeam

namespace FischerBeam

def degree (a b : ℕ) : Fin 2 →₀ ℕ := Finsupp.single 0 a + Finsupp.single 1 b

@[simp] theorem degree_zero (a b : ℕ) : degree a b 0 = a := by simp [degree]
@[simp] theorem degree_one (a b : ℕ) : degree a b 1 = b := by simp [degree]

@[simp] theorem degree_eq_iff (a b u v : ℕ) : degree a b = degree u v ↔ a=u ∧ b=v := by
  constructor
  · intro h
    exact ⟨by simpa using congrArg (fun f => f 0) h,
      by simpa using congrArg (fun f => f 1) h⟩
  · rintro ⟨rfl, rfl⟩; rfl

@[simp] theorem degree_add (a b u v : ℕ) : degree a b + degree u v = degree (a+u) (b+v) := by
  ext j
  fin_cases j <;> simp [degree]

@[simp] theorem weight_degree (a b : ℕ) : weight (degree a b) = (a.factorial : ℝ)*b.factorial := by
  simp [weight, Fin.prod_univ_two]

theorem linear_power (c s : ℝ) (a : ℕ) :
    (c • (X 0 : Poly)+s • X 1)^a =
      ∑ p ∈ Finset.range (a+1), monomial (degree p (a-p))
        ((a.choose p : ℝ)*c^p*s^(a-p)) := by
  rw [add_pow]
  apply Finset.sum_congr rfl
  intro p _
  rw [smul_pow, smul_pow, X_pow_eq_monomial, X_pow_eq_monomial,
    smul_monomial, smul_monomial]
  simp only [smul_eq_mul, mul_one]
  rw [monomial_mul]
  rw [show (a.choose p : Poly) = C (a.choose p : ℝ) by simp]
  rw [mul_comm _ (C _), C_mul_monomial]
  simp only [degree, mul_assoc]

theorem rotated_expansion (c s : ℝ) (a b : ℕ) :
    rotated c s a b =
      ∑ p ∈ Finset.range (a+1), ∑ q ∈ Finset.range (b+1),
        monomial (degree (p+q) ((a-p)+(b-q)))
          ((a.choose p : ℝ)*b.choose q*c^p*(-s)^(a-p)*s^q*c^(b-q)) := by
  have ha : creatorA c s = c • (X 0 : Poly) + (-s) • X 1 := by simp [creatorA, sub_eq_add_neg]
  rw [rotated, ha, creatorB, linear_power, linear_power, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro p _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro q _
  rw [monomial_mul, degree_add]
  congr 1
  ring

theorem coeff_rotated (c s : ℝ) (k e a b : ℕ) :
    (rotated c s a b).coeff (degree k e) =
      if k+e=a+b then
        ∑ p ∈ Finset.range (a+1), ∑ q ∈ Finset.range (b+1),
          if p+q=k then (a.choose p : ℝ)*b.choose q*c^p*(-s)^(a-p)*s^q*c^(b-q) else 0
      else 0 := by
  rw [rotated_expansion]
  simp only [coeff_sum, coeff_monomial, degree_eq_iff]
  by_cases ht : k+e=a+b
  · rw [ite_eq_left ht]
    apply Finset.sum_congr rfl
    intro p hp
    apply Finset.sum_congr rfl
    intro q hq
    have hp' := Finset.mem_range.mp hp
    have hq' := Finset.mem_range.mp hq
    have he : p+q=k ∧ a-p+(b-q)=e ↔ p+q=k := by omega
    simp only [he]
  · rw [ite_eq_right ht]
    apply Finset.sum_eq_zero
    intro p hp
    apply Finset.sum_eq_zero
    intro q hq
    have hp' := Finset.mem_range.mp hp
    have hq' := Finset.mem_range.mp hq
    rw [ite_eq_right (by omega)]

end FischerBeam

namespace FischerBeam

@[simp] theorem degree_coordinates (m : Fin 2 →₀ ℕ) : degree (m 0) (m 1) = m := by
  ext j
  fin_cases j <;> simp

theorem sector_reconstruction (P : Poly) (T : ℕ)
    (hP : ∀ k e, k+e ≠ T → P.coeff (degree k e) = 0) :
    P = ∑ k : Fin (T+1), monomial (degree k (T-k)) (P.coeff (degree k (T-k))) := by
  ext m
  obtain ⟨k, e, rfl⟩ : ∃ k e, m = degree k e := ⟨m 0, m 1, (degree_coordinates m).symm⟩
  simp only [coeff_sum, coeff_monomial, degree_eq_iff]
  by_cases ht : k+e=T
  · have hk : k < T+1 := by omega
    rw [Finset.sum_eq_single ⟨k,hk⟩]
    · simp [show T-k=e by omega]
    · intro j _ hj
      have hj' : j.val ≠ k := by exact fun he => hj (Fin.ext he)
      simp [hj']
    · simp
  · rw [hP k e ht]
    symm
    apply Finset.sum_eq_zero
    intro j _
    by_cases he : j.val=k ∧ T-j.val=e
    · have hj := j.isLt
      omega
    · simp [he]

def sectorMatrix (c s : ℝ) (T : ℕ) : Matrix (Fin (T+1)) (Fin (T+1)) ℝ :=
  fun k a => Real.sqrt (weight (degree k (T-k))) /
      Real.sqrt (weight (degree a (T-a))) *
    (rotated c s a (T-a)).coeff (degree k (T-k))

@[simp] theorem sqrt_weight_degree_pos (a b : ℕ) : 0 < Real.sqrt (weight (degree a b)) := by
  rw [weight_degree]
  positivity

theorem sectorMatrix_columns {c s : ℝ} (h : c^2+s^2=1) (T : ℕ)
    (a b : Fin (T+1)) :
    ∑ k, sectorMatrix c s T k a * sectorMatrix c s T k b = if a=b then 1 else 0 := by
  have ha : a.val + (T-a.val) = T := Nat.add_sub_of_le (by omega : a.val ≤ T)
  have hp : pairing (rotated c s a (T-a)) (rotated c s b (T-b)) =
      ∑ k : Fin (T+1), weight (degree k (T-k)) *
        (rotated c s a (T-a)).coeff (degree k (T-k)) *
        (rotated c s b (T-b)).coeff (degree k (T-k)) := by
    have hrec := sector_reconstruction (rotated c s a (T-a)) T (by
      intro k e hne
      rw [coeff_rotated, ite_eq_right (by omega)])
    conv_lhs => arg 1; rw [hrec]
    simp only [map_sum, LinearMap.sum_apply, pairing_monomial]
    apply Finset.sum_congr rfl
    intro k _
    ring
  have ho := pairing_rotated h a (T-a) b (T-b)
  have he : (a.val=b.val ∧ T-a.val=T-b.val) ↔ a=b := by
    constructor
    · exact fun he => Fin.ext he.1
    · rintro rfl; exact ⟨rfl,rfl⟩
  simp only [he] at ho
  have hsa := (sqrt_weight_degree_pos a (T-a)).ne'
  have hsb := (sqrt_weight_degree_pos b (T-b)).ne'
  calc
    (∑ k, sectorMatrix c s T k a * sectorMatrix c s T k b) =
        (∑ k : Fin (T+1), weight (degree k (T-k)) *
          (rotated c s a (T-a)).coeff (degree k (T-k)) *
          (rotated c s b (T-b)).coeff (degree k (T-k))) /
            (Real.sqrt (weight (degree a (T-a)))*Real.sqrt (weight (degree b (T-b)))) := by
      rw [Finset.sum_div]
      apply Finset.sum_congr rfl
      intro k _
      have hw : 0 ≤ weight (degree k (T-k)) := by rw [weight_degree]; positivity
      dsimp only [sectorMatrix]
      field_simp
      rw [Real.sq_sqrt hw]
      ring
    _ = if a=b then 1 else 0 := by
      rw [← hp, ho]
      by_cases heq : a=b
      · subst b
        rw [ite_eq_left rfl, ite_eq_left rfl, ← pow_two, Real.sq_sqrt (by rw [weight_degree]; positivity), weight_degree]
        exact div_self (by positivity)
      · rw [ite_eq_right heq, ite_eq_right heq, zero_div]

end FischerBeam

namespace FischerBeam

def multiSectorMatrix {n : ℕ} (c s : ℝ) (T : Fin n → ℕ) :
    Matrix (∀ j, Fin (T j+1)) (∀ j, Fin (T j+1)) ℝ :=
  fun k a => ∏ j, sectorMatrix c s (T j) (k j) (a j)

theorem multiSectorMatrix_columns {n : ℕ} {c s : ℝ} (h : c^2+s^2=1)
    (T : Fin n → ℕ) (a b : ∀ j, Fin (T j+1)) :
    ∑ k, multiSectorMatrix c s T k a * multiSectorMatrix c s T k b =
      if a=b then 1 else 0 := by
  classical
  simp only [multiSectorMatrix, ← Finset.prod_mul_distrib]
  rw [← Fintype.prod_sum (fun (j : Fin n) (u : Fin (T j+1)) =>
    sectorMatrix c s (T j) u (a j) * sectorMatrix c s (T j) u (b j))]
  simp only [sectorMatrix_columns h]
  by_cases hab : a=b
  · subst b
    simp
  · rw [ite_eq_right hab]
    obtain ⟨j,hj⟩ := Function.ne_iff.mp hab
    exact Finset.prod_eq_zero (Finset.mem_univ j) (ite_eq_right hj)

theorem multiSectorMatrix_rows {n : ℕ} {c s : ℝ} (h : c^2+s^2=1)
    (T : Fin n → ℕ) (k l : ∀ j, Fin (T j+1)) :
    ∑ a, multiSectorMatrix c s T k a * multiSectorMatrix c s T l a =
      if k=l then 1 else 0 := by
  have hc : (multiSectorMatrix c s T).transpose * multiSectorMatrix c s T = 1 := by
    ext a b
    simpa only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.one_apply] using
      multiSectorMatrix_columns h T a b
  have hr := mul_eq_one_comm.mp hc
  simpa only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.one_apply] using
    congrArg (fun M => M k l) hr

end FischerBeam

end

section
open scoped BigOperators ComplexConjugate ENNReal Topology
open MeasureTheory
open scoped ComplexConjugate
open scoped BigOperators ComplexConjugate
open scoped BigOperators
open MvPolynomial
open scoped BigOperators ComplexConjugate Classical
open Submodule

namespace BlockUnitary

variable {S : Type*} {I : S → Type*} [∀ s, Fintype (I s)]
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

def rotated (b : HilbertBasis (Sigma I) ℂ E)
    (U : ∀ s, I s → I s → ℝ) (i : Sigma I) : E :=
  ∑ k, (U i.1 k i.2 : ℂ) • b ⟨i.1,k⟩

theorem inner_rotated_same (b : HilbertBasis (Sigma I) ℂ E)
    (U : ∀ s, I s → I s → ℝ) (s : S) (a d : I s) :
    inner ℂ (rotated b U ⟨s,a⟩) (rotated b U ⟨s,d⟩) =
      ((∑ k, U s k a * U s k d : ℝ) : ℂ) := by
  classical
  simp only [rotated, inner_sum, sum_inner, inner_smul_right, inner_smul_left,
    orthonormal_iff_ite.mp b.orthonormal, Complex.conj_ofReal]
  simp [mul_comm]

theorem inner_rotated_ne (b : HilbertBasis (Sigma I) ℂ E)
    (U : ∀ s, I s → I s → ℝ) {s t : S} (hst : s ≠ t)
    (a : I s) (d : I t) :
    inner ℂ (rotated b U ⟨s,a⟩) (rotated b U ⟨t,d⟩) = 0 := by
  classical
  simp only [rotated, inner_sum, sum_inner, inner_smul_right, inner_smul_left,
    orthonormal_iff_ite.mp b.orthonormal]
  have he (k : I s) (l : I t) : (Sigma.mk s k : Sigma I) ≠ ⟨t,l⟩ := by
    intro h
    exact hst (congrArg Sigma.fst h)
  simp [he]

theorem rotated_orthonormal (b : HilbertBasis (Sigma I) ℂ E)
    (U : ∀ s, I s → I s → ℝ)
    (hU : ∀ s a d, ∑ k, U s k a * U s k d = if a=d then 1 else 0) :
    Orthonormal ℂ (rotated b U) := by
  classical
  rw [orthonormal_iff_ite]
  rintro ⟨s,a⟩ ⟨t,d⟩
  by_cases hst : s=t
  · subst t
    rw [inner_rotated_same, hU]
    by_cases had : a=d <;> simp [had]
  · rw [inner_rotated_ne b U hst]
    simp [show (Sigma.mk s a : Sigma I) ≠ ⟨t,d⟩ from
      fun he => hst (congrArg Sigma.fst he)]

theorem inner_basis_rotated_same (b : HilbertBasis (Sigma I) ℂ E)
    (U : ∀ s, I s → I s → ℝ) (s : S) (k a : I s) :
    inner ℂ (b ⟨s,k⟩) (rotated b U ⟨s,a⟩) = (U s k a : ℂ) := by
  classical
  simp [rotated, orthonormal_iff_ite.mp b.orthonormal]

theorem inner_basis_rotated_ne (b : HilbertBasis (Sigma I) ℂ E)
    (U : ∀ s, I s → I s → ℝ) {s t : S} (hst : s ≠ t)
    (k : I s) (a : I t) :
    inner ℂ (b ⟨s,k⟩) (rotated b U ⟨t,a⟩) = 0 := by
  classical
  have he (l : I t) : (Sigma.mk s k : Sigma I) ≠ ⟨t,l⟩ := by
    exact fun h => hst (congrArg Sigma.fst h)
  simp [rotated, orthonormal_iff_ite.mp b.orthonormal, he]

theorem inverse_expansion (b : HilbertBasis (Sigma I) ℂ E)
    (U : ∀ s, I s → I s → ℝ)
    (hU : ∀ s k l, ∑ a, U s k a * U s l a = if k=l then 1 else 0)
    (s : S) (k : I s) :
    b ⟨s,k⟩ = ∑ a, (U s k a : ℂ) • rotated b U ⟨s,a⟩ := by
  classical
  apply b.repr.injective
  apply lp.ext
  funext i
  rcases i with ⟨t,l⟩
  simp only [b.repr_apply_apply, inner_sum, inner_smul_right]
  by_cases hts : t=s
  · subst t
    simp only [inner_basis_rotated_same, orthonormal_iff_ite.mp b.orthonormal]
    simp only [← Complex.ofReal_mul, ← Complex.ofReal_sum, hU]
    by_cases hlk : l=k
    · subst k; simp
    · simp [hlk, Ne.symm hlk]
  · have he : (Sigma.mk t l : Sigma I) ≠ ⟨s,k⟩ :=
      fun he => hts (congrArg Sigma.fst he)
    simp [inner_basis_rotated_ne b U hts, orthonormal_iff_ite.mp b.orthonormal, he]

theorem rotated_dense (b : HilbertBasis (Sigma I) ℂ E)
    (U : ∀ s, I s → I s → ℝ)
    (hU : ∀ s k l, ∑ a, U s k a * U s l a = if k=l then 1 else 0) :
    ⊤ ≤ (span ℂ (Set.range (rotated b U))).topologicalClosure := by
  rw [← b.dense_span]
  apply Submodule.topologicalClosure_mono
  apply Submodule.span_le.mpr
  rintro _ ⟨⟨s,k⟩,rfl⟩
  rw [inverse_expansion b U hU s k]
  exact Submodule.sum_mem _ (fun a _ => Submodule.smul_mem _ _
    (Submodule.subset_span ⟨⟨s,a⟩,rfl⟩))

variable [CompleteSpace E]

def basis (b : HilbertBasis (Sigma I) ℂ E)
    (U : ∀ s, I s → I s → ℝ)
    (hcol : ∀ s a d, ∑ k, U s k a * U s k d = if a=d then 1 else 0)
    (hrow : ∀ s k l, ∑ a, U s k a * U s l a = if k=l then 1 else 0) :
    HilbertBasis (Sigma I) ℂ E :=
  HilbertBasis.mk (rotated_orthonormal b U hcol) (rotated_dense b U hrow)

@[simp] theorem basis_apply (b : HilbertBasis (Sigma I) ℂ E)
    (U : ∀ s, I s → I s → ℝ)
    (hcol : ∀ s a d, ∑ k, U s k a * U s k d = if a=d then 1 else 0)
    (hrow : ∀ s k l, ∑ a, U s k a * U s l a = if k=l then 1 else 0)
    (i : Sigma I) : basis b U hcol hrow i = rotated b U i := by
  simp [basis]

def unitary (b : HilbertBasis (Sigma I) ℂ E)
    (U : ∀ s, I s → I s → ℝ)
    (hcol : ∀ s a d, ∑ k, U s k a * U s k d = if a=d then 1 else 0)
    (hrow : ∀ s k l, ∑ a, U s k a * U s l a = if k=l then 1 else 0) :
    E ≃ₗᵢ[ℂ] E := b.repr.trans (basis b U hcol hrow).repr.symm

@[simp] theorem unitary_apply_basis (b : HilbertBasis (Sigma I) ℂ E)
    (U : ∀ s, I s → I s → ℝ)
    (hcol : ∀ s a d, ∑ k, U s k a * U s k d = if a=d then 1 else 0)
    (hrow : ∀ s k l, ∑ a, U s k a * U s l a = if k=l then 1 else 0)
    (i : Sigma I) : unitary b U hcol hrow (b i) = rotated b U i := by
  change (basis b U hcol hrow).repr.symm (b.repr (b i)) = _
  rw [b.repr_self, HilbertBasis.repr_symm_single, basis_apply]

end BlockUnitary

namespace BlockUnitary
variable {S : Type*} {I : S → Type*} [∀ s, Fintype (I s)]
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

def reindex {ι κ : Type*} (b : HilbertBasis ι ℂ E) (e : κ ≃ ι) : HilbertBasis κ ℂ E :=
  HilbertBasis.mk (b.orthonormal.comp e e.injective) (by
    have hr : Set.range (b ∘ e) = Set.range b := by
      ext x
      constructor
      · rintro ⟨i,rfl⟩; exact ⟨e i,rfl⟩
      · rintro ⟨i,rfl⟩; exact ⟨e.symm i,by simp⟩
    rw [hr, b.dense_span])

@[simp] theorem reindex_apply {ι κ : Type*} (b : HilbertBasis ι ℂ E) (e : κ ≃ ι)
    (k : κ) : reindex b e k = b (e k) := by simp [reindex]

theorem unitary_symm_apply_basis (b : HilbertBasis (Sigma I) ℂ E)
    (U : ∀ s, I s → I s → ℝ)
    (hcol : ∀ s a d, ∑ k, U s k a * U s k d = if a=d then 1 else 0)
    (hrow : ∀ s k l, ∑ a, U s k a * U s l a = if k=l then 1 else 0)
    (s : S) (k : I s) :
    (unitary b U hcol hrow).symm (b ⟨s,k⟩) =
      ∑ a, (U s k a : ℂ) • b ⟨s,a⟩ := by
  apply (unitary b U hcol hrow).injective
  simp only [LinearIsometryEquiv.apply_symm_apply, map_sum, map_smul, unitary_apply_basis]
  exact inverse_expansion b U hrow s k

end BlockUnitary

namespace EntropyPhotonNumber
open FischerBeam

theorem oneModeBeamCoefficient_eq (η : ℝ) (k e a b : ℕ) :
    oneModeBeamCoefficient η k e a b =
      Real.sqrt (weight (degree k e)) / Real.sqrt (weight (degree a b)) *
        (rotated (Real.sqrt η) (Real.sqrt (1-η)) a b).coeff (degree k e) := by
  rw [coeff_rotated]
  by_cases ht : k+e=a+b
  · simp only [oneModeBeamCoefficient, ite_eq_left ht, weight_degree]
    rw [Real.sqrt_div (by positivity)]
  · simp [oneModeBeamCoefficient, ht]

abbrev PairedIndex (n : ℕ) := NumberIndex n × NumberIndex n
abbrev JointFock (n : ℕ) := lp (fun _ : PairedIndex n => ℂ) 2
abbrev NumberSector (n : ℕ) := Σ T : NumberIndex n, ∀ j, Fin (T j+1)

def sectorEquiv (n : ℕ) : NumberSector n ≃ PairedIndex n where
  toFun a := (fun j => a.2 j, fun j => a.1 j-a.2 j)
  invFun x := ⟨fun j => x.1 j+x.2 j, fun j => ⟨x.1 j, by dsimp; omega⟩⟩
  left_inv := by
    rintro ⟨T,a⟩
    have hT : (fun j => (a j).val + (T j-(a j).val)) = T := by
      funext j
      have ha := (a j).isLt
      omega
    apply Sigma.ext hT
    apply Function.hfunext rfl
    intro j j' hj
    have he : j=j' := eq_of_heq hj
    subst j'
    apply (Fin.heq_ext_iff (congrArg (fun t : NumberIndex n => t j+1) hT)).mpr
    rfl
  right_inv := by
    rintro ⟨a,b⟩
    ext j <;> simp

def jointNumberBasis (n : ℕ) : HilbertBasis (PairedIndex n) ℂ (JointFock n) :=
  HilbertBasis.ofRepr (LinearIsometryEquiv.refl ℂ _)

def jointSectorBasis (n : ℕ) : HilbertBasis (NumberSector n) ℂ (JointFock n) :=
  BlockUnitary.reindex (jointNumberBasis n) (sectorEquiv n)

@[simp] theorem jointNumberBasis_apply {n : ℕ} (i : PairedIndex n) :
    jointNumberBasis n i = lp.single 2 i 1 := by
  exact ((jointNumberBasis n).repr_symm_single i).symm

@[simp] theorem jointSectorBasis_apply {n : ℕ} (a : NumberSector n) :
    jointSectorBasis n a = lp.single 2 (sectorEquiv n a) 1 := by
  simp [jointSectorBasis]

theorem beam_sectorCoefficient {n : ℕ} (η : ℝ) (T : NumberIndex n)
    (k a : ∀ j, Fin (T j+1)) :
    beamCoefficient η (fun j => k j) (fun j => T j-k j)
      (fun j => a j) (fun j => T j-a j) =
        multiSectorMatrix (Real.sqrt η) (Real.sqrt (1-η)) T k a := by
  simp only [beamCoefficient, multiSectorMatrix, oneModeBeamCoefficient_eq, sectorMatrix]

theorem sqrt_beam_rotation {η : ℝ} (hη : η ∈ Set.Icc 0 1) :
    Real.sqrt η^2 + Real.sqrt (1-η)^2 = 1 := by
  rw [Real.sq_sqrt hη.1, Real.sq_sqrt (sub_nonneg.mpr hη.2)]
  ring

def beamUnitary {n : ℕ} (η : ℝ) (hη : η ∈ Set.Icc 0 1) :
    JointFock n ≃ₗᵢ[ℂ] JointFock n :=
  BlockUnitary.unitary (jointSectorBasis n)
    (multiSectorMatrix (Real.sqrt η) (Real.sqrt (1-η)))
    (fun T a b => by
      have h := multiSectorMatrix_columns (sqrt_beam_rotation hη) T a b
      by_cases he : a=b <;> simpa [he] using h)
    (fun T k l => by
      have h := multiSectorMatrix_rows (sqrt_beam_rotation hη) T k l
      by_cases he : k=l <;> simpa [he] using h)

end EntropyPhotonNumber

namespace EntropyPhotonNumber
open FischerBeam

theorem beam_symm_sector {n : ℕ} (η : ℝ) (hη : η ∈ Set.Icc 0 1)
    (T : NumberIndex n) (k : ∀ j, Fin (T j+1)) :
    (beamUnitary (n := n) η hη).symm (jointSectorBasis n ⟨T,k⟩) =
      ∑ a : (∀ j, Fin (T j+1)),
        (beamCoefficient η (fun j => k j) (fun j => T j-k j)
          (fun j => a j) (fun j => T j-a j) : ℂ) • jointSectorBasis n ⟨T,a⟩ := by
  simp only [beam_sectorCoefficient]
  unfold beamUnitary
  apply BlockUnitary.unitary_symm_apply_basis

theorem beam_symm_number {n : ℕ} (η : ℝ) (hη : η ∈ Set.Icc 0 1)
    (k e : NumberIndex n) :
    (beamUnitary (n := n) η hη).symm (lp.single 2 (k,e) 1) =
      ∑ a : SectorSplit k e,
        (beamCoefficient η k e (splitLeft a) (splitRight a) : ℂ) •
          lp.single 2 (splitLeft a,splitRight a) 1 := by
  have h := beam_symm_sector η hη (fun j => k j+e j)
    (fun j => (⟨k j, by omega⟩ : Fin (k j+e j+1)))
  simp only [jointSectorBasis_apply, sectorEquiv, Nat.add_sub_cancel_left,
    Equiv.coe_fn_mk] at h
  convert! h using 1

end EntropyPhotonNumber

namespace FischerBeam
open MvPolynomial

@[simp] theorem degree_add_zero (k e : ℕ) : degree k e + Finsupp.single 0 1 = degree (k+1) e := by
  ext j
  fin_cases j <;> simp [degree]
@[simp] theorem degree_add_one (k e : ℕ) : degree k e + Finsupp.single 1 1 = degree k (e+1) := by
  ext j
  fin_cases j <;> simp [degree]

def oscillatorCoefficient (c s : ℝ) (k e a b : ℕ) : ℝ :=
  Real.sqrt (weight (degree k e))/Real.sqrt (weight (degree a b))*
    (rotated c s a b).coeff (degree k e)

end FischerBeam

namespace EntropyPhotonNumber
open FischerBeam

end EntropyPhotonNumber

namespace EntropyPhotonNumber
open FischerBeam
variable {n : ℕ}

end EntropyPhotonNumber

end

end

end OAI


